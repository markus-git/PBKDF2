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

---------------------------------------------------------------------
-- * PBKDF2.
--
-- Pseudocode specification for PBKDF2:
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
      f i = foldr1 mxor (take (fromInteger c) (us i))

      ts :: [[Word8]]
      ts = map f [1..l]
  in
  take (fromInteger dkLen) (concat ts)

-- INT (i) is a four-octet encoding of the integer i,
-- most significant octet first.
int :: Integer -> [Word8]
int i | length o > 4 = error "size of INT(i) > four-octet"
      | length o < 4 = replicate (4 - length o) 0x00 ++ o
      | otherwise    = o
  where o = unroll i

---------------------------------------------------------------------
-- ** HMAC-SHA1.
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
-- Where
--   * '∥' is concatenation
--   * '⊕' is exclusive or (XOR)
--   * '*' is repetition.
--   * 'blocksize' is that of the underlying hash function
--      (64 for SHA1)
--      
hmac :: [Word8] -- message, an octet string.
     -> [Word8] -- encryption key, an octet string.
     -> [Word8] -- encoded message, an octet string.
hmac msg ikey =
  let key = case compare (length ikey) blocksize of
        GT -> hash ikey
        LT -> ikey ++ (0x00 `repeat` (blocksize - length ikey))
        EQ -> ikey
      o_key_pad = (0x5c `repeat` blocksize) `mxor` key
      i_key_pad = (0x36 `repeat` blocksize) `mxor` key
  in
  hash(o_key_pad ++ hash(i_key_pad ++ msg))
  where
    repeat    = flip replicate :: Word8 -> Int -> [Word8]    
    blocksize = 64 :: Int

-- length in octets of pseudorandom function output, 
-- a positive integer. (SHA1 outputs 160 bits).
hLen :: Integer
hLen = 160 `div` 8

-- underlying pseudorandom function (hLen denotes the 
-- length in octets of the pseudorandom function output).
hash :: [Word8] -> [Word8]
hash = unroll . SHA1.toInteger . SHA1.hash

---------------------------------------------------------------------
-- ** Helpers.

mdiv :: Integer -> Integer -> Integer
mdiv a b = ceiling ((fromIntegral a) / (fromIntegral b))

mxor :: [Word8] -> [Word8] -> [Word8]
mxor = zipWith (xor)

unroll :: Integer -> [Word8]
unroll = unfoldr stepR
  where
    stepR 0 = Nothing
    stepR i = Just (fromIntegral i, i `shiftR` 8)

roll :: [Word8] -> Integer
roll = foldr stepL 0
  where
    stepL b a = a `shiftL` 8 .|. fromIntegral b

----------------------------------------------------------------------
-- Older stuff.

unpackWord160 :: SHA1.Word160 -> [Word8]
unpackWord160 (SHA1.Word160 a b c d e) = concatMap octets [a, b, c, d, e] 

octets :: Word32 -> [Word8]
octets w = 
    [ fromIntegral (w `shiftR` 24)
    , fromIntegral (w `shiftR` 16)
    , fromIntegral (w `shiftR` 8)
    , fromIntegral w
    ]

----------------------------------------------------------------------
-- ** Testing & QuickCheck.

-- DK = PBKDF2(HMAC−SHA1, passphrase, ssid, 4096, 256) in WPA2.

wpa2 pswd salt = pbkdf2 pswd salt 4096 256

-- HMAC_SHA1("key", "The quick brown fox jumps over the lazy dog") =
--   0xde7c9b85b8b78aa6bc8a7a36f70a90701c9db4d9

-- For some reason, my hmac function, the one imported from a library,
-- and the wiki's example, all produce different hashes.
msg = S.encode "The quick brown fox jumps over the lazy dog"
key = S.encode "key"             
res = 0xde7c9b85b8b78aa6bc8a7a36f70a90701c9db4d9 :: Integer

prop_octets_id :: Integer -> Property
prop_octets_id i = i >= 0 ==> roll (unroll i) === i

---------------------------------------------------------------------
-- the end.
