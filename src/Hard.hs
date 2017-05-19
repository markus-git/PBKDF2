{-# language FlexibleContexts    #-}
{-# language ScopedTypeVariables #-}
{-# language GADTs               #-}

module Hard where

import Co

import Data.Bits (Bits)
import Control.Applicative
import Control.Monad hiding ((>>))

import Feldspar
import Feldspar.Hardware

import qualified Feldspar.Hardware.Compile as Hard

import Prelude (flip, (.), ($), Bool(..), Num(..), Integer(..))

--------------------------------------------------------------------------------
-- * Hardware
--------------------------------------------------------------------------------

type HRef    = Reference Hardware

type HArr    = Array  Hardware
type HIrr    = IArray Hardware
type HIx     = Ix     Hardware

type HBool   = HExp Bool
type HInt    = HExp Integer
type HWord8  = HExp Word8
type HWord16 = HExp Word16
type HWord32 = HExp Word32
type HWord64 = HExp Word64

type HBlock = Block Hardware
type HB     = B     Hardware

--------------------------------------------------------------------------------
-- ** SHA1
--------------------------------------------------------------------------------
-- todo: same as for the software version.

sha1 :: HArr HWord8 -> Hardware (HArr HWord8)
sha1 message =
  do let f :: HInt -> HWord32 -> HWord32 -> HWord32 -> HWord32
         f t b c d =
           (0  <= t && t <= 19) ?? ((b .&. c) .|. (complement b .&. d)) $
           (20 <= t && t <= 39) ?? (b `xor` c `xor` d) $
           (40 <= t && t <= 59) ?? ((b .&. c) .|. (b .&. d) .|. (c .&. d))
                                 $ (b `xor` c `xor` d)

     let k :: HInt -> HWord32
         k t =
           (0  <= t && t <= 19) ?? 0x5a827999 $
           (20 <= t && t <= 39) ?? 0x6ed9eba1 $
           (40 <= t && t <= 59) ?? 0x8f1bbcdc
                                 $ 0xca62c1d6

     let step :: HIrr HWord32 -> HInt -> HBlock -> Hardware ()
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
     p  <- sha1_pad message
     w  <- sha1_extend p
     -- fetch the initial 160-bit block.
     ib <- init_block
     -- process block of w.
     (do -- copy the current block.
         cb <- copy_block ib
         -- iterate step over block.
         for (0) (79) $ \i -> step w i cb
         -- add new block to previous block.
         add_block ib cb)
     -- translate the final block into an array of octets.
     sha1_block ib

-- ghdl
--------------------------------------------------------------------------------

sha1_pad :: HArr (HExp Word8) -> Hardware (HArr (HExp Word8))
sha1_pad message =
  do let size = 64 :: HInt
     let len  = length message :: HInt
     bits :: HWord64           <- shareM (i2n len * 8)
     imsg :: HIrr (HExp Word8) <- unsafeFreezeArr message
     pad  :: HArr (HExp Word8) <- newArr size
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
       setArr pad i (i2n (bits >> (8 * ((size-1) - i))))
     -- return padded message.
     return pad

sha1_extend :: HArr (HExp Word8) -> Hardware (HIrr (HExp Word32))
sha1_extend pad =
  do ipad :: HIrr (HExp Word8)  <- unsafeFreezeArr pad
     ex   :: HArr (HExp Word32) <- newArr (80)
     -- truncate original block.
     for (0) (15) $ \i ->
       setArr ex i
         (   (i2n $ ipad ! ((i*4)))
           + (i2n $ ipad ! ((i*4)+1) << 8)
           + (i2n $ ipad ! ((i*4)+2) << 16)
           + (i2n $ ipad ! ((i*4)+3) << 24)
         )
     -- extend block with new words.
     iex :: HIrr (HExp Word32) <- unsafeFreezeArr ex
     for (16) (79) $ \i ->
       setArr ex i $ 
         (       (iex ! (i-3))
           `xor` (iex ! (i-8))
           `xor` (iex ! (i-14))
           `xor` (iex ! (i-16))
         ) |<<| 1
     unsafeFreezeArr ex

-- Translate a 160-bit block into an array of 20 8-bits.
sha1_block :: HBlock -> Hardware (HArr (HExp Word8))
sha1_block (a, b, c, d, e) =
  do ta  <- unsafeFreezeRef a
     tb  <- unsafeFreezeRef b
     tc  <- unsafeFreezeRef c
     td  <- unsafeFreezeRef d
     te  <- unsafeFreezeRef e
     out <- newArr 20
     let shift i = 8 * (3 - i)
     for 0 3 $ \i -> setArr out (i)    (i2n (ta >> (shift i)))
     for 0 3 $ \i -> setArr out (i+4)  (i2n (tb >> (shift i)))
     for 0 3 $ \i -> setArr out (i+8)  (i2n (tc >> (shift i)))
     for 0 3 $ \i -> setArr out (i+12) (i2n (td >> (shift i)))
     for 0 3 $ \i -> setArr out (i+16) (i2n (te >> (shift i)))
     return out

--------------------------------------------------------------------------------
  
(??) :: HType a => HBool -> HExp a -> HExp a -> HExp a
(??) = (?)

(!!) :: HType a => HIrr (HExp a) -> HInt -> HExp a
(!!) = (!)

(<<) :: (HType' a, Bits a) => HExp a -> HInt -> HExp a
(<<) = shiftL

(>>) :: (HType' a, Bits a) => HExp a -> HInt -> HExp a
(>>) = shiftR

(|<<|) :: (HType' a, Bits a) => HExp a -> HInt -> HExp a
(|<<|) = rotateL

(|>>|) :: (HType' a, Bits a) => HExp a -> HInt -> HExp a
(|>>|) = rotateR

foldlHM
  :: (HBlock -> HInt -> Hardware ()) -- update function.
  -> HBlock -- initial block.
  -> HInt -- lower range.
  -> HInt -- upper range.
  -> Hardware HBlock
foldlHM f b l u =
  do for l u (\ix -> f b ix)
     return b

--------------------------------------------------------------------------------

test_sha1 = Hard.icompile $ do
  m <- msg
  sha1 m

--------------------------------------------------------------------------------
