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

sha1 :: Integer -> HArr HWord8 -> Hardware (HArr HWord8)
sha1 blocks message =
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
     let b = value blocks
     p  <- sha1_pad    b message
     w  <- sha1_extend b p
     -- fetch the initial 160-bit block.
     ib <- init_block
     -- process the blocks of w.
     for (0) (b-1) (\(i :: HExp Integer) ->
       do -- copy the current block.
          cb <- copy_block ib
          -- iterate step over block.
          for (0) (79) $ \i -> step w i cb
          -- add new block to previous block.
          add_block ib cb)
     -- translate the final block into an array of octets.
     sha1_block ib

--------------------------------------------------------------------------------

sha1_pad :: HInt -> HArr (HExp Word8) -> Hardware (HArr (HExp Word8))
sha1_pad blocks message =
  do let len = length message :: HInt
     bits :: HWord64           <- shareM (i2n len * 8)
     size :: HInt              <- shareM (64 * blocks)
     imsg :: HIrr (HExp Word8) <- unsafeFreezeArr message
     pad  :: HArr (HExp Word8) <- newArr (64 * blocks)
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
       setArr pad i (i2n (bits `shiftR` (8 * ((size-1) - i))))
     return pad

sha1_extend :: HInt -> HArr (HExp Word8) -> Hardware (HIrr (HExp Word32))
sha1_extend blocks pad =
  do ipad :: HIrr (HExp Word8)  <- unsafeFreezeArr pad
     ex   :: HArr (HExp Word32) <- newArr (80 + blocks)
     -- truncate original block.
     for (0) (blocks-1) $ (\(b :: HExp Integer) -> do
       po <- shareM (b * 16)
       bo <- shareM (b * 80)
       for (0) (15) (\(i :: HExp Integer) ->
         setArr ex (b+i)
           (   (i2n $ ipad ! (po+(i*4)))
             + (i2n $ ipad ! (po+(i*4)+1)) `shiftL` (8  :: HExp Integer)
             + (i2n $ ipad ! (po+(i*4)+2)) `shiftL` (16 :: HExp Integer)
             + (i2n $ ipad ! (po+(i*4)+3)) `shiftL` (24 :: HExp Integer)
           )))
     -- extend block with new words.
     iex :: HIrr (HExp Word32) <- unsafeFreezeArr ex
     for (0) (blocks-1) (\(b :: HExp Integer) -> do
       bo <- shareM (b * 80)
       for (bo+16) (bo+79) (\(i :: HExp Integer) ->
         setArr ex i $ flip rotateL (1 :: HExp Word32)
           (       (iex ! (i-3))
             `xor` (iex ! (i-8))
             `xor` (iex ! (i-14))
             `xor` (iex ! (i-16))
           )))
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
  
(??) :: HType a => HBool -> HExp a -> HExp a -> HExp a
(??) = (?)

(!!) :: HType a => HIrr (HExp a) -> HInt -> HExp a
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

test = Hard.icompile (msg >>= sha1 2 >> return ())

--------------------------------------------------------------------------------
