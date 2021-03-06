module PBKDF2 where

import Data.Bits
import Data.Word
import Data.Char (ord)
import Data.List (unfoldr, intersperse)

-- for converting between words of different size and other numbers.
import qualified Codec.Binary.UTF8.String as S
import Numeric

-- for testing.
import Debug.Trace
import Test.QuickCheck (quickCheck, Property)
import qualified Test.QuickCheck  as Q
import qualified Data.HMAC        as HMAC (hmac_sha1)
import qualified Data.Digest.SHA1 as SHA1

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

-- *** I have slightly modified the algorithm and skipped 'r', which is used to
-- drop any extra blocks introduced by rounding 'l'. Since these are dropped
-- from the last blocks, we could just as well grab the 'dkLen' first blocks
-- instead. This is under the assumption that 'dkLen' is a multiple of 8.
pbkdf2 :: Password -> Salt -> Int -> Int -> Hash
pbkdf2 pswd salt c dkLen
  | dkLen > (2^32 - 1) * hLen = error "derived key too long"
  | otherwise =
  let l  = dkLen `mdiv` hLen

      us :: Int -> [[Word8]]
      us i = take c
           $ iterate (hmac pswd)
           $ hmac pswd (salt ++ int4b i)

      f :: Int -> [Word8]
      f i = foldr1 mxor (us i)

      ts :: [[Word8]]
      ts = map f [1..l]
  in
  take dkLen $ concat ts

-- length in octest of pseudorandom function input, SHA1 blocks are 512 bits.
blocksize :: Int
blocksize = 64
  
-- length in octets of pseudorandom function output, SHA1 outputs 160 bits.
hLen :: Int
hLen = 20

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
-- To compute HMAC over the data 'text' we perform
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
--------------------------------------------------------------------------------

hmac :: [Word8] -- message, an octet string.
     -> [Word8] -- encryption key, an octet string.
     -> [Word8] -- encoded message, an octet string.
hmac msg key =
  let sized_key = hmac_padded_key key
      o_key_pad = (0x5c `mrepeat` blocksize) `mxor` sized_key
      i_key_pad = (0x36 `mrepeat` blocksize) `mxor` sized_key
  in
  sha1(o_key_pad ++ sha1(i_key_pad ++ msg))

hmac_padded_key :: [Word8] -> [Word8]
hmac_padded_key key = k ++ (0x00 `mrepeat` (blocksize - length k))
  where k | length key > blocksize = sha1 key
          | otherwise              = key

----------------------------------------

prop_hmac_key_len :: [Word8] -> Property
prop_hmac_key_len key = length (hmac_padded_key key) Q.=== blocksize

--------------------------------------------------------------------------------
-- * SHA1
--
-- ...
--
--------------------------------------------------------------------------------

data Block = H !Word32 !Word32 !Word32 !Word32 !Word32

addBlock :: Block -> Block -> Block
addBlock (H a1 b1 c1 d1 e1) (H a2 b2 c2 d2 e2) =
  H (a1+a2) (b1+b2) (c1+c2) (d1+d2) (e1+e2)

-- underlying pseudorandom function (hLen denotes the length in octets of the
-- pseudorandom function output).
sha1 :: [Word8] -> [Word8]
sha1 msg =
  let f :: Int -> Word32 -> Word32 -> Word32 -> Word32
      f t b c d
        | 0  <= t && t <= 19 = (b .&. c) .|. ((complement b) .&. d)
        | 20 <= t && t <= 39 = b `xor` c `xor` d
        | 40 <= t && t <= 59 = (b .&. c) .|. (b .&. d) .|. (c .&. d)
        | 60 <= t && t <= 79 = b `xor` c `xor` d

      k :: Int -> Word32
      k t
        | 0  <= t && t <= 19 = 0x5a827999
        | 20 <= t && t <= 39 = 0x6ed9eba1
        | 40 <= t && t <= 59 = 0x8f1bbcdc
        | 60 <= t && t <= 79 = 0xca62c1d6

      step :: [Word32] -> Int -> Block -> Block
      step w t (H a b c d e) = (H temp a (b `rotateL` 30) c d)
        where
          temp = (a `rotateL` 5) + (f t b c d) + e + (w !! t) + (k t)

      block :: [Word32] -> Block -> Block
      block ws ib = foldl (\b i -> step ws i b) ib [0..79]

      process :: [[Word32]] -> Block -> Block
      process ws ib = foldl (\b w -> b `addBlock` block w b) ib ws

      words :: Block -> [Word8]
      words (H a b c d e) = padding $ unroll $
          (fromIntegral a `shiftL` 128) +
          (fromIntegral b `shiftL` 96)  +
          (fromIntegral c `shiftL` 64)  +
          (fromIntegral d `shiftL` 32)  +
          (fromIntegral e)
        where
          padding :: [Word8] -> [Word8]
          padding xs = 0x00 `mrepeat` (length xs - hLen) ++ xs
  in
  words $ process (sha1_preprocess msg) (sha1_init)

-- ...
sha1_init :: Block
sha1_init = H 0x67452301 0xefcdab89 0x98badcfe 0x10325476 0xc3d2e1f0

-- ...
sha1_padding :: [Word8] -> [Word8]
sha1_padding msg =
    msg ++ [0x80] ++ (0x00 `mrepeat` padding) ++ int8b (mbits msg)
  where
    blocks :: Int
    blocks = (length msg + 1) `mod` 64
    
    padding :: Int
    padding = if (blocks > 56) then (56 + 64 - blocks) else (56 - blocks)  

-- A message is processed in successive 512-bit chunks, where each chunk is
-- is broken into sixteen 32-bit big-endian words and then exdented into
-- eighty 32-bit words according to:
--
--    for i from 16 to 79
--      w[i] = (w[i-3] xor w[i-8] xor w[i-14] xor w[i-16]) leftrotate 1
-- 
sha1_preprocess :: [Word8] -> [[Word32]]
sha1_preprocess = map (extend . map b2w . mchunk 4) . mchunk 64 . sha1_padding
  where
    word :: [Word32] -> Int -> Word32
    word w i =
     (       (w !! (i-3))
       `xor` (w !! (i-8))
       `xor` (w !! (i-14))
       `xor` (w !! (i-16))
     )
     `rotateL` 1

    extend :: [Word32] -> [Word32]
    extend ws = foldl (\w i -> w ++ [word w i]) ws [16..79]

----------------------------------------

prop_sha1_padding_len :: [Word8] -> Property
prop_sha1_padding_len msg = length (sha1_padding msg) `mod` 64 Q.=== 0

prop_sha1_preprocess_len :: [Word8] -> Property
prop_sha1_preprocess_len msg = error "todo"

--------------------------------------------------------------------------------
-- ** Operations from above specifications.

mbits :: [Word8] -> Int
mbits = (8*) . length

mdiv :: Int -> Int -> Int
mdiv a b = ceiling ((fromIntegral a) / (fromIntegral b))

mxor :: [Word8] -> [Word8] -> [Word8]
mxor = zipWith (xor)

mrepeat :: Word8 -> Int -> [Word8]
mrepeat = flip replicate

mchunk :: Int -> [a] -> [[a]]
mchunk s [] = []
mchunk s xs = let (h,t) = splitAt s xs in h : mchunk s t

----------------------------------------

int8b :: Int -> [Word8]
int8b i = mint i 8

int4b :: Int -> [Word8]
int4b i = mint i 4

-- INT i b is a b-octet encoding of the integer i, most significant octet first.
mint :: Int -> Int -> [Word8]
mint num bytes
  | length o > bytes = error "INT(i): size too big."
  | length o < bytes = (0x00 `mrepeat` (bytes - length o)) ++ o
  | otherwise        = o
  where o = unroll (fromIntegral num)

--------------------------------------------------------------------------------
-- ** Conversion between word and integer types.

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

b2w :: [Word8] -> Word32
b2w = fromIntegral . roll

----------------------------------------

prop_octets_id :: Integer -> Property
prop_octets_id i = i >= 0 Q.==> roll (unroll i) Q.=== i

--------------------------------------------------------------------------------
-- ** Testing & QuickCheck.

-- In WPA2: DK = PBKDF2(HMAC−SHA1, passphrase, ssid, 4096, 256).
wpa2 pswd salt = pbkdf2 pswd salt 4096 256

-- HMAC_SHA1("key", "The quick brown fox jumps over the lazy dog") =
--   0xde7c9b85b8b78aa6bc8a7a36f70a90701c9db4d9
msg = S.encode "The quick brown fox jumps over the lazy dog"
key = S.encode "key"             
res = 0xde7c9b85b8b78aa6bc8a7a36f70a90701c9db4d9 :: Integer

----------------------------------------

hash :: [Word8] -> [Word8]
hash = padding . unroll . SHA1.toInteger . SHA1.hash
  where
    padding :: [Word8] -> [Word8]
    padding xs = 0x00 `mrepeat` (length xs - hLen) ++ xs

--------------------------------------------------------------------------------
-- the end.
