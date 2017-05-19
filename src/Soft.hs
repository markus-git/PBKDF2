{-# language FlexibleContexts    #-}
{-# language ScopedTypeVariables #-}
{-# language GADTs               #-}

module Soft where

import Co

import Control.Applicative
import Control.Monad

import Feldspar
import Feldspar.Software

import qualified Feldspar.Software.Compile as Soft

import Prelude (undefined, flip, (.), ($), Bool(..), Num(..))

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
-- ** HMAC-SHA1
--------------------------------------------------------------------------------

hmac :: SArr SWord8 -> SArr SWord8 -> Software (SArr SWord8)
hmac msg key = undefined

--------------------------------------------------------------------------------
-- ** SHA1
--------------------------------------------------------------------------------
--
-- todo: for simplicity we have assumed that SHA1 only ever reveieves <55
--       octets to hash, and thus only needs one 512-bit block.
--
--------------------------------------------------------------------------------

sha1 :: SArr SWord8 -> Software (SArr SWord8)
sha1 message =
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
                a `rotateL` (5 :: SWord32) + (f t b c d) + e + (w !! t) + (k t)
              setRef re (d)
              setRef rd (c)
              setRef rc (b `rotateL` (30 :: SWord32))
              setRef rb (a)
              setRef ra (temp)

     -- format the message according to SHA1.
     p  <- sha1_pad message
     w  <- sha1_extend p
     -- fetch the initial 160-bit block.
     ib <- init_block
     -- process the blocks of w.
     blocks <- shareM (length w `div` 80)
     for (0) (blocks-1) (\(i :: SExp Word8) ->
       do let w' = slice ((i*80)+0) ((i*80)+79) w
          -- copy current block..
          cb <- copy_block ib
          -- iterate step over block.
          for (0) (79) $ \j -> step w j cb
          -- add new block to previous block.
          add_block ib cb)
     -- translate the final block into an array of octets.
     sha1_block ib

--------------------------------------------------------------------------------

sha1_pad :: SArr (SExp Word8) -> Software (SArr (SExp Word8))
sha1_pad message =
  do let len = length message
     bits <- shareM (i2n len * 8 :: SExp Word64)
     size <- shareM (64 * (1 + (len `div` 64)))
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
       setArr pad i (i2n (bits `shiftR` (8 * ((size-1) - i))))
     return pad

sha1_extend :: SArr (SExp Word8) -> Software (SIrr (SExp Word32))
sha1_extend pad =
  do let len = length pad
     blocks <- shareM (len `div` 64)
     ipad :: SIrr (SExp Word8)  <- unsafeFreezeArr pad
     ex   :: SArr (SExp Word32) <- newArr (80 * blocks)
     -- truncate original block.
     for (0) (blocks-1) $ (\(b :: SExp Word8) -> do
       po <- shareM (b * 16)
       bo <- shareM (b * 80)
       for (0) (15) (\(i :: SExp Word8) ->
         setArr ex (b+i)
           (   (i2n $ ipad ! (po+(i*4)))
             + (i2n $ ipad ! (po+(i*4)+1)) `shiftL` (8  :: SExp Word32)
             + (i2n $ ipad ! (po+(i*4)+2)) `shiftL` (16 :: SExp Word32)
             + (i2n $ ipad ! (po+(i*4)+3)) `shiftL` (24 :: SExp Word32)
           )))
     -- extend block with new words.
     iex :: SIrr (SExp Word32) <- unsafeFreezeArr ex
     for (0) (blocks-1) (\(b :: SExp Word8) -> do
       bo <- shareM (b * 80)
       for (bo+16) (bo+79) (\(i :: SExp Word8) ->
         setArr ex i $ flip rotateL (1 :: SExp Word32)
           (       (iex ! (i-3))
             `xor` (iex ! (i-8))
             `xor` (iex ! (i-14))
             `xor` (iex ! (i-16))
           )))
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

test = Soft.icompile (msg >>= sha1 >> return ())

--------------------------------------------------------------------------------
