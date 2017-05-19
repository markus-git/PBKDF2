{-# language FlexibleContexts    #-}
{-# language ScopedTypeVariables #-}
{-# language GADTs               #-}

module Soft where

import Co

import Data.Bits (Bits)
import Control.Applicative
import Control.Monad hiding ((>>))

import Feldspar
import Feldspar.Software

import qualified Feldspar.Software.Compile as Soft

import Prelude (undefined, flip, (.), ($), Bool(..), Num(..), Integral)

--------------------------------------------------------------------------------
-- * Software
--------------------------------------------------------------------------------

type SRef    = Reference Software

type SArr    = Array  Software
type SIrr    = IArray Software
type SIx     = Ix     Software

type SBool   = SExp Bool
type SWord8  = SExp Word8
type SWord16 = SExp Word16
type SWord32 = SExp Word32
type SWord64 = SExp Word64

type SBlock = Block Software
type SB     = B     Software

--------------------------------------------------------------------------------
-- ** PBKDF2
--------------------------------------------------------------------------------
-- todo: in the example, we assume the password <35 chars and salt =16 chars.

pbkdf2 :: SArr SWord8 -> SArr SWord8 -> SWord8 -> SWord8 -> Software (SArr SWord8)
pbkdf2 password salt c dkLen =
  do let l = dkLen `div` 20

     let us_init :: SWord32 -> Software (SArr SWord8)
         us_init i = do
           bits  <- int4b i
           whole <- salt +++ bits
           hmac password whole

     let f :: SWord32 -> Software (SArr SWord8)
         f i = foldlM (\u _ -> hmac password u >>= mxor u) (us_init i) 1 (c-1)

     let ts :: Software (SArr SWord8)
         ts = concatMapM (\i -> f (i2n i)) 0 (l-1)

     slice 0 dkLen <$> ts

--------------------------------------------------------------------------------

concatMapM
  :: (SExp Index -> Software (SArr SWord8))
  -> SExp Index
  -> SExp Index
  -> Software (SArr SWord8)
concatMapM fun lower upper =
  do res :: SArr SWord8 <- newArr (20 + 20 * (i2n (upper - lower)) :: SIx)
     for lower upper $ \i ->
       do let ix = i*20
          n <- fun i
          copyArr (slice (ix) (ix+19) res) n
     return res

foldlM
  :: (SType' b, Integral b)
  => (SArr a -> SExp b -> Software ())
  -> Software (SArr a)
  -> SExp b
  -> SExp b
  -> Software (SArr a)
foldlM fun init lower upper =
  do u <- init
     for lower upper $ \i ->
       do fun u i
     return u

int4b :: SWord32 -> Software (SArr SWord8)
int4b i =
  do arr :: SArr SWord8 <- newArr 4
     setArr arr 0 $ i2n (i >> 24)
     setArr arr 1 $ i2n (i >> 16)
     setArr arr 2 $ i2n (i >> 8)
     setArr arr 3 $ i2n (i)
     return arr

mxor :: SArr SWord8 -> SArr SWord8 -> Software ()
mxor u n =
  do ui :: SIrr SWord8 <- unsafeFreezeArr u
     ni :: SIrr SWord8 <- unsafeFreezeArr n
     for 0 (length u) $ \i ->
       setArr u i ((ui ! i) `xor` (ni ! i))

--------------------------------------------------------------------------------
-- ** Simplified example of HMAC-SHA1.
--------------------------------------------------------------------------------
-- todo: for simplicity, this only creates a single block. For more blocks,
--       simply exdent the length of the padded key and ipad/opad to the length
--       of an entire block.

hmac :: SArr SWord8 -> SArr SWord8 -> Software (SArr SWord8)
hmac msg {-<35-} key {-20-} =
  do opad <- hmac_xpad (0x5c) key
     ipad <- hmac_xpad (0x36) key
     temp <- hmac_prf ipad msg
     hmac_prf opad temp

hmac_prf :: SArr SWord8 -> SArr SWord8 -> Software (SArr SWord8)
hmac_prf a b = (a +++ b) >>= sha1

hmac_xpad :: SWord8 -> SArr SWord8 -> Software (SArr SWord8)
hmac_xpad v key {-20-} =
  do pad  :: SArr SWord8 <- newArr 20
     ikey :: SIrr SWord8 <- unsafeFreezeArr key
     for 0 19 $ \i -> setArr pad i (v `xor` (ikey ! i))
     return pad

--------------------------------------------------------------------------------

(+++) :: SArr SWord8 -> SArr SWord8 -> Software (SArr SWord8)
(+++) a {-20-} b {-<35-} =
  do let len = length a + length b
     ia :: SIrr SWord8 <- unsafeFreezeArr a
     ib :: SIrr SWord8 <- unsafeFreezeArr b
     c  :: SArr SWord8 <- newArr len
     copyArr c a
     copyArr (slice (length b) len c) b
     return c

--------------------------------------------------------------------------------
-- ** Simplified example of SHA1.
--------------------------------------------------------------------------------
-- todo: for simplicity, this one handles only a single block. For more blocks,
--       simply extend the hardcoded limits on arrays to variables and add an
--       extra fold to 'sha1' for applying the inner (do ..) to each block.

sha1 :: SArr SWord8 -> Software (SArr SWord8)
sha1 message {-<55-} =
  do let f :: SWord8 -> SWord32 -> SWord32 -> SWord32 -> SWord32
         f t b c d =
           (0  <= t && t <= 19) ?? ((b .&. c) .|. (complement b .&. d)) $
           (20 <= t && t <= 39) ?? (b `xor` c `xor` d) $
           (40 <= t && t <= 59) ?? ((b .&. c) .|. (b .&. d) .|. (c .&. d))
                                 $ (b `xor` c `xor` d)

     let k :: SWord8 -> SWord32
         k t =
           (0  <= t && t <= 19) ?? 0x5a827999 $
           (20 <= t && t <= 39) ?? 0x6ed9eba1 $
           (40 <= t && t <= 59) ?? 0x8f1bbcdc
                                 $ 0xca62c1d6

     let step :: SIrr SWord32 -> SWord8 -> SBlock -> Software ()
         step w t block@(ra, rb, rc, rd, re) =
           do (a, b, c, d, e) <- freeze_block block
              temp <- shareM $
                (a |<<| 5) + (f t b c d) + e + (w !! t) + (k t)
              setRef re (d)
              setRef rd (c)
              setRef rc (b |<<| 30)
              setRef rb (a)
              setRef ra (temp)

     -- format the message according to SHA1.
     p  <- sha1_pad    message
     w  <- sha1_extend p
     -- fetch the initial 160-bit block.
     ib <- init_block
     -- process block of w.
     (do -- copy current block.
          cb <- copy_block ib
          -- iterate step over block.
          for (0) (79) $ \i -> step w i cb
          -- add new block to previous block.
          add_block ib cb)
     -- translate the final block into an array of octets.
     sha1_block ib

--------------------------------------------------------------------------------

sha1_pad :: SArr (SExp Word8) -> Software (SArr (SExp Word8))
sha1_pad message =
  do let size = 64 :: SWord8
     let len  = length message :: SWord8
     bits <- shareM (i2n len * 8 :: SWord64)
     imsg :: SIrr (SExp Word8) <- unsafeFreezeArr message
     pad  :: SArr (SExp Word8) <- newArr size
     -- copy original message.
     for (0) (len-1) $ \i ->
       setArr pad i (imsg !! i)
     -- add the single one.
     setArr pad len 1
     -- fill with zeroes.
     for (len+1) (size-9) $ \i ->
       setArr pad i 0
     -- add length in last 8 8-bits.
     for (size-8) (size-1) $ \i ->
       setArr pad i (i2n (bits >> (i2n (8 * ((size-1) - i)))))
     return pad

sha1_extend :: SArr (SExp Word8) -> Software (SIrr (SExp Word32))
sha1_extend pad =
  do ipad :: SIrr (SExp Word8)  <- unsafeFreezeArr pad
     ex   :: SArr (SExp Word32) <- newArr (80)
     -- truncate original block.
     for (0) (15) $ \i ->
       setArr ex i
         (   (i2n $ ipad ! ((i*4)))
           + (i2n $ ipad ! ((i*4)+1) << 8)
           + (i2n $ ipad ! ((i*4)+2) << 16)
           + (i2n $ ipad ! ((i*4)+3) << 32)
         )
     -- extend block with new words.
     iex :: SIrr (SExp Word32) <- unsafeFreezeArr ex
     for 16 79 $ \i ->
       setArr ex i $
         (       (iex ! (i-3))
           `xor` (iex ! (i-8))
           `xor` (iex ! (i-14))
           `xor` (iex ! (i-16))
         ) |<<| 1
     unsafeFreezeArr ex

-- Translate a 160-bit block into an array of 20 8-bits.
sha1_block :: SBlock -> Software (SArr (SExp Word8))
sha1_block (a, b, c, d, e) =
  do ta  <- unsafeFreezeRef a
     tb  <- unsafeFreezeRef b
     tc  <- unsafeFreezeRef c
     td  <- unsafeFreezeRef d
     te  <- unsafeFreezeRef e
     out <- newArr 20
     let shift i = 8 * (3 - (i2n i :: SExp Word32))
     for 0 3 $ \i -> setArr out (i)    (i2n (ta `shiftR` shift i) :: SExp Word8)
     for 0 3 $ \i -> setArr out (i+4)  (i2n (tb `shiftR` shift i) :: SExp Word8)
     for 0 3 $ \i -> setArr out (i+8)  (i2n (tc `shiftR` shift i) :: SExp Word8)
     for 0 3 $ \i -> setArr out (i+12) (i2n (td `shiftR` shift i) :: SExp Word8)
     for 0 3 $ \i -> setArr out (i+16) (i2n (te `shiftR` shift i) :: SExp Word8)
     return out

--------------------------------------------------------------------------------

(??) :: SType a => SBool -> SExp a -> SExp a -> SExp a
(??) = (?)

(!!) :: SType a => SIrr (SExp a) -> SWord8 -> SExp a
(!!) = (!)

(<<) :: (SType' a, Bits a) => SExp a -> SWord32 -> SExp a
(<<) = shiftL

(>>) :: (SType' a, Bits a) => SExp a -> SWord32 -> SExp a
(>>) = shiftR

(|<<|) :: (SType' a, Bits a) => SExp a -> SWord32 -> SExp a
(|<<|) = rotateL

(|>>|) :: (SType' a, Bits a) => SExp a -> SWord32 -> SExp a
(|>>|) = rotateR

foldlSM
  :: (SBlock -> SWord8 -> Software ()) -- update function.
  -> SBlock -- initial block.
  -> SWord8 -- lower range.
  -> SWord8 -- upper range.
  -> Software SBlock
foldlSM f b l u =
  do for l u (\ix -> f b ix)
     return b

--------------------------------------------------------------------------------

test_pbkdf2 = Soft.icompile $ do
  m <- msg
  s <- salt16
  pbkdf2 m s 10 3

test_hmac = Soft.icompile $ do
  m <- msg
  s <- salt20
  hmac m s

test_sha1 = Soft.icompile $ do
  m <- msg
  sha1 m

--------------------------------------------------------------------------------
