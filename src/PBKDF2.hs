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

type Password = [Word8] -- password, an octet string.
type Salt     = [Word8] -- salt, an octet string.
type Hash     = [Word8] -- derived key, a dkLen-octet string.

pbkdf2 :: Password -> Salt -> Integer -> Integer -> Hash 
pbkdf2 pswd salt c dkLen =
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
-- ** Pre-defined parts (since we're going with SHA1).

-- Pseudocode specification for HMAC-SHA1.
--
--  function hmac (key, message) {
--    if (length(key) > blocksize) {
--        key = hash(key)
--    }
--    if (length(key) < blocksize) {
--        key = key ∥ [0x00 * (blocksize - length(key))]
--    }
--   
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
--      
hmac :: [Word8] -- message, an octet string.
     -> [Word8] -- encryption key, an octet string.
     -> [Word8] -- encoded message, an octet string.
hmac msg key =
      let nkey = case compare (length key) blocksize of
            GT -> hash key
            LT -> key ++ replicate (blocksize - length key) 0x00
            EQ -> key

          opad = (replicate blocksize 0x5c) `mxor` nkey
          ipad = (replicate blocksize 0x36) `mxor` nkey
      in
      hash(opad ++ hash(ipad ++ msg))
  where 
    blocksize :: Int 
    blocksize = 64

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
mxor = zipWith (.|.)

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
