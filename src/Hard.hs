{-# language FlexibleContexts    #-}
{-# language ScopedTypeVariables #-}
{-# language GADTs               #-}

module Hard where

import Co

import Control.Applicative
import Control.Monad

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
--
-- todo: same assumption as for software version.
--
--------------------------------------------------------------------------------

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
                a `rotateL` (5 :: HWord32) + (f t b c d) + e + (w !! t) + (k t)
              setRef re (d)
              setRef rd (c)
              setRef rc (b `rotateL` (30 :: HWord32))
              setRef rb (a)
              setRef ra (temp)

          -- format the message according to SHA1.
     w  <- sha1_extend message
     -- fetch the initial 160-bit block.
     ib <- init_block
     -- process the first (and only!) block of w.
     cb <- copy_block ib
     foldlHM (\b ix -> step w ix b) cb 0 79
     -- add new block to previous block.
     fb <- add_block ib cb
     -- translate the final block into an array of octets.
     sha1_block fb
     return message

--------------------------------------------------------------------------------

sha1_pad :: HArr (HExp Word8) -> Hardware (HArr (HExp Word8))
sha1_pad message =
  do let len = length message
     bits <- shareM (i2n len * 8 :: HExp Word64)
     pad  <- newArr 64
     -- copy original message.
     --copyArr pad message
     for (0) (len - 1) $ \i ->
       do v <- getArr message i
          setArr pad i v
     -- add the single one.
     setArr  pad len 1
     -- fill with zeroes.
     for (len + 1) (55) $ \i -> setArr pad i 0
     -- add length in last 8 8-bits.
     for (56) (63) $ \i ->
       do let shift = (8 * (63 - i)) :: HExp Integer
          val <- shareM ((bits `shiftR` shift) :: HExp Word64)
          setArr pad i (i2n val)
     return pad

sha1_extend :: HArr (HExp Word8) -> Hardware (HIrr (HExp Word32))
sha1_extend message =
  do pad    :: HArr (HExp Word8)  <- sha1_pad message
     ex     :: HArr (HExp Word32) <- newArr 80
     -- truncate original block.
     ipad   :: HIrr (HExp Word8) <- unsafeFreezeArr pad
     for 0 15 (\(i :: HExp Integer) ->
       setArr ex i
         (   (i2n $ ipad ! (i*4  ))
           + (i2n $ ipad ! (i*4+1)) `shiftL` (8  :: HExp Word32)
           + (i2n $ ipad ! (i*4+2)) `shiftL` (16 :: HExp Word32)
           + (i2n $ ipad ! (i*4+3)) `shiftL` (24 :: HExp Word32)
         ))
     -- extend block with new words.
     iex   :: HIrr (HExp Word32) <- unsafeFreezeArr ex
     for 16 79 (\(i :: HExp Integer) ->
       setArr ex i $ flip rotateL (1 :: HExp Word32)
         (       (iex ! (i-3 ))
           `xor` (iex ! (i-8 ))
           `xor` (iex ! (i-14))
           `xor` (iex ! (i-16))
         ))
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
     let shift i = 8 * (3 - (i2n i :: HExp Word32))
     for 0 3 $ \i -> setArr out (i)    (i2n (ta `shiftR` shift i) :: HExp Word8)
     for 0 3 $ \i -> setArr out (i+4)  (i2n (tb `shiftR` shift i) :: HExp Word8)
     for 0 3 $ \i -> setArr out (i+8)  (i2n (tc `shiftR` shift i) :: HExp Word8)
     for 0 3 $ \i -> setArr out (i+12) (i2n (td `shiftR` shift i) :: HExp Word8)
     for 0 3 $ \i -> setArr out (i+16) (i2n (te `shiftR` shift i) :: HExp Word8)
     return out

--------------------------------------------------------------------------------
  
(??) :: HBool -> HWord32 -> HWord32 -> HWord32
(??) = (?)

(!!) :: HIrr HWord32 -> HInt -> HWord32
(!!) = (!)

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

test = Hard.icompile (msg >>= sha1 >> return ())

--------------------------------------------------------------------------------
