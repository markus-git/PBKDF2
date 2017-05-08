module PBKDF2 where

import Data.Bits
import Data.Word
import Data.Char (ord)
import Data.List (unfoldr, intersperse)

-- underlying psuedo-random function.
import qualified Data.Digest.SHA1 as SHA1

-- for converting between words of different size and other numbers.
--import qualified Data.ByteString.Lazy     as L
--import qualified Data.ByteString.Char8    as C
--import qualified Data.ByteString.Internal as I
import qualified Codec.Binary.UTF8.String as S
--import qualified Data.Serialize as S
import Numeric

-- for testing.
import Debug.Trace
import Test.QuickCheck
import qualified Data.HMAC as HMAC (hmac_sha1)

--------------------------------------------------------------------------------
-- * PBKDF2.
--
--     1. If dkLen > (2^32 - 1) * hLen, output "derived key too long" and
--        stop.
--
--     2. Let l be the number of hLen-octet blocks in the derived key,
--        rounding up, and let r be the number of octets in the last
--        block:
--
--                 l = ceiling (dkLen / hLen) ,
--                 r = dkLen - (l - 1) * hLen .
--
--     3. For each block of the derived key apply the function F defined
--        below to the password P, the salt S, the iteration count c, and
--        the block index to compute the block:
--
--                 T_1 = F (P, S, c, 1) ,
--                 T_2 = F (P, S, c, 2) ,
--                 ...
--                 T_l = F (P, S, c, l) ,
--
--        where the function F is defined as the exclusive-or sum of the
--        first c iterates of the underlying pseudorandom function PRF
--        applied to the password P and the concatenation of the salt S
--        and the block index i:
--
--                 F (P, S, c, i) = U_1 ⊕ U_2 ⊕ ... ⊕ U_c
--
--         where
--
--                 U_1 = PRF (P, S ∥ int (i)) ,
--                 U_2 = PRF (P, U_1) ,
--                 ...
--                 U_c = PRF (P, U_{c-1}) .
--
--     4. Concatenate the blocks and extract the first dkLen octets to
--        produce a derived key DK:
--
--                 DK = T_1 ∥ T_2 ∥ ... ∥ T_l<0..r-1>
--
--     5. Output the derived key DK.
--
--------------------------------------------------------------------------------

type Password = [Word8] -- password, an octet string.
type Salt     = [Word8] -- salt, an octet string.
type Hash     = [Word8] -- derived key, a dkLen-octet string.

pbkdf2 :: Password -> Salt -> Integer -> Integer -> Hash
pbkdf2 pswd salt c dkLen
  | dkLen > (2^32 - 1) * hLen = error "derived key too long"
  | otherwise =
  let l  = dkLen `mdiv` hLen
      r  = dkLen - (l - 1) * hLen

      us :: Integer -> [[Word8]]
      us i = iterate (hmac pswd) (hmac pswd (salt ++ int i))

      f :: Integer -> [Word8]
      f i = take (fromInteger c) $ foldr1 mxor (us i)

      ts :: [[Word8]]
      ts = map f [1..l]
  in
  take (fromInteger r - 1) (concat ts)

-- INT (i) is a four-octet encoding of the integer i,
-- most significant octet first.
int :: Integer -> [Word8]
int i | length o > 4 = error "size of INT(i) > four-octet"
      | length o < 4 = replicate (4 - length o) 0x00 ++ o
      | otherwise    = o
  where o = unroll i

--------------------------------------------------------------------------------
-- * HMAC-SHA1.
--
-- The definition of HMAC requires a cryptographic hash function, for which we
-- will use SHA1 and we denote by H, and a secret key K. We denote by B the
-- byte-length of blocks (B=64 for SHA1), and by L the byte-length of hash
-- outputs (L=20 for SHA-1). The authentication key K can be of any length up
-- to B. Applications that use keys longer than B bytes will first hash the key
-- using H and then use the resultant L byte string as the actual key to HMAC.
-- In any case the minimal recommended length for K is L bytes.
--
-- We define two fixed and different strings ipad and opad as follows
-- (the 'i' and 'o' are mnemonics for inner and outer):
--
--     ipad = the byte 0x36 repeated B times
--     opad = the byte 0x5C repeated B times.
--
-- To compute HMAC over the data `text' we perform
--
--     H(K XOR opad, H(K XOR ipad, text))
--
-- Namely,
--
--  (1) append zeros to the end of K to create a B byte string
--      (e.g., if K is of length 20 bytes and B=64, then K will be
--       appended with 44 zero bytes 0x00)
--  (2) XOR (bitwise exclusive-OR) the B byte string computed in step
--      (1) with ipad
--  (3) append the stream of data 'text' to the B byte string resulting
--      from step (2)
--  (4) apply H to the stream generated in step (3)
--  (5) XOR (bitwise exclusive-OR) the B byte string computed in
--      step (1) with opad
--  (6) append the H result from step (4) to the B byte string
--      resulting from step (5)
--  (7) apply H to the stream generated in step (6) and output
--      the result
--
-- Pseudocode specification for HMAC-SHA1:
--
--  function hmac (key, message) {
--    if (length(key) > blocksize) {
--        key = hash(key)
--    }
--    if (length(key) < blocksize) {
--        key = key ∥ [0x00 * (blocksize - length(key))]
--    }
--    o_key_pad = [0x5c * blocksize] ⊕ key
--    i_key_pad = [0x36 * blocksize] ⊕ key
--
--    return hash(o_key_pad ∥ hash(i_key_pad ∥ message))
--  }
--
-- Where '*' denotes repetition.
--------------------------------------------------------------------------------

hmac :: [Word8] -- message, an octet string.
     -> [Word8] -- encryption key, an octet string.
     -> [Word8] -- encoded message, an octet string.
hmac msg key =
  let sized_key = hmac_fitted_key key
      o_key_pad = (0x5c `mrepeat` hmac_blocksize) `mxor` sized_key
      i_key_pad = (0x36 `mrepeat` hmac_blocksize) `mxor` sized_key
  in
  hash(o_key_pad ++ hash(i_key_pad ++ msg))

hmac_fitted_key :: [Word8] -> [Word8]
hmac_fitted_key key
  | length key > hmac_blocksize = hmac_fitted_key (hash key)
  | otherwise  = key ++ (0x00 `mrepeat` (hmac_blocksize - length key))

hmac_blocksize :: Int
hmac_blocksize = 64

hmac_hashsize :: Int
hmac_hashsize = 20
  
-- length in octets of pseudorandom function output, 
-- a positive integer. (SHA1 outputs 160 bits).
hLen :: Integer
hLen = 160 `div` 8

-- underlying pseudorandom function (hLen denotes the 
-- length in octets of the pseudorandom function output).
hash :: [Word8] -> [Word8]
hash = unroll . SHA1.toInteger . SHA1.hash

----------------------------------------

prop_hmac_key_len :: [Word8] -> Property
prop_hmac_key_len key = len >= hmac_hashsize .&&. len <= hmac_blocksize
  where len = length $ hmac_fitted_key key

--------------------------------------------------------------------------------
-- ** Operations from above specifications.

mdiv :: Integer -> Integer -> Integer
mdiv a b = ceiling ((fromIntegral a) / (fromIntegral b))

mxor :: [Word8] -> [Word8] -> [Word8]
mxor = zipWith (xor)

mrepeat :: Word8 -> Int -> [Word8]
mrepeat = flip replicate

--------------------------------------------------------------------------------
-- ** Conversion from words to integers.

unroll :: Integer -> [Word8]
unroll = unfoldr stepR
  where
    stepR 0 = Nothing
    stepR i = Just (fromIntegral i, i `shiftR` 8)

roll :: [Word8] -> Integer
roll = foldr stepL 0
  where
    stepL b a = a `shiftL` 8 .|. fromIntegral b

----------------------------------------

prop_octets_id :: Integer -> Property
prop_octets_id i = i >= 0 ==> roll (unroll i) === i

--------------------------------------------------------------------------------
-- ** Testing & QuickCheck.

-- In WPA2: DK = PBKDF2(HMAC−SHA1, passphrase, ssid, 4096, 256).
wpa2 pswd salt = pbkdf2 pswd salt 4096 256

-- HMAC_SHA1("key", "The quick brown fox jumps over the lazy dog") =
--   0xde7c9b85b8b78aa6bc8a7a36f70a90701c9db4d9
msg = S.encode "The quick brown fox jumps over the lazy dog"
key = S.encode "key"             
res = 0xde7c9b85b8b78aa6bc8a7a36f70a90701c9db4d9 :: Integer

--------------------------------------------------------------------------------
-- the end.
