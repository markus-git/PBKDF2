{-# language FlexibleContexts #-}
{-# language GADTs #-}

{-# language ScopedTypeVariables #-}

module Co where

import Control.Applicative
import Control.Monad

import qualified Language.VHDL              as V
import qualified Language.Embedded.Hardware as H

import Feldspar
import Feldspar.Software hiding (Word)
import Feldspar.Hardware hiding (Word)

import qualified Feldspar.Software.Compile as Soft
import qualified Feldspar.Hardware.Compile as Hard

import Prelude (flip, undefined, Num(..), ($), (.))
import qualified Prelude as P

--------------------------------------------------------------------------------
-- Short-hands.

type SRef    = Reference Software

type SArr    = Array  Software
type SIrr    = IArray Software
type SIx     = Ix     Software

type SBool   = SExp P.Bool
type SWord8  = SExp Word8
type SWord16 = SExp Word16
type SWord32 = SExp Word32
type SWord64 = SExp Word64

--------------------------------------------------------------------------------
-- * SHA1
--
-- ...
--
-- *** For simplicity, lets assume we only reveieve <55 8-bits to hash,
--     that is, SHA1 pre-processing will only create one block.
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

     let step :: SIrr SWord32 -> SWord8 -> Block -> Software ()
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
     w  <- sha1_extend message
     -- fetch the initial 160-bit block.
     ib <- init_block
     -- process the first (and only!) block of w.
     cb <- copy_block ib
     foldlM (\b ix -> step w ix b) cb 0 79
     -- add new block to previous block.
     fb <- add_block ib cb
     -- translate the final block into an array of octets.
     arr_block fb

----------------------------------------

foldlM
  :: (Block -> SWord8 -> Software ()) -- update function.
  -> Block  -- initial block.
  -> SWord8 -- lower range.
  -> SWord8 -- upper range.
  -> Software Block
foldlM f b l u =
  do for l u (\ix -> f b ix)
     return b

(??) :: SBool -> SWord32 -> SWord32 -> SWord32
(??) = (?)

(!!) :: SIrr SWord32 -> SWord8 -> SWord32
(!!) = (!)

----------------------------------------

-- A block reperesents the 160-bit blocks that SHA1 operates over.
type Block =
  (SRef SWord32, SRef SWord32, SRef SWord32, SRef SWord32, SRef SWord32)

-- Short-hand for a block with unwrapped references.
type B =
  (SWord32, SWord32, SWord32, SWord32, SWord32)

-- Creates a new block based on the initial values given by SHA1.
init_block :: Software Block
init_block =
  do a <- initRef 0x67452301
     b <- initRef 0xefcdab89
     c <- initRef 0x98badcfe
     d <- initRef 0x10325476
     e <- initRef 0xc3d2e1f0
     return (a, b, c, d, e)

-- Creates a new block by copying the values of the given block.
copy_block :: Block -> Software Block
copy_block (a, b, c, d, e) =
  do a' <- initRef =<< unsafeFreezeRef a
     b' <- initRef =<< unsafeFreezeRef b
     c' <- initRef =<< unsafeFreezeRef c
     d' <- initRef =<< unsafeFreezeRef d
     e' <- initRef =<< unsafeFreezeRef e
     return (a', b', c', d', e')

-- Freezes each reference of a block.
freeze_block :: Block -> Software B
freeze_block (a, b, c, d, e) =
  do a' <- unsafeFreezeRef a
     b' <- unsafeFreezeRef b
     c' <- unsafeFreezeRef c
     d' <- unsafeFreezeRef d
     e' <- unsafeFreezeRef e
     return (a', b', c', d', e')

-- Joins two blocks by inplace, pair-wise adding values of the second block
-- into the first block.
add_block :: Block -> Block -> Software Block
add_block block@(a, b, c, d, e) (a', b', c', d', e') =
  do ta <- unsafeFreezeRef a; ta' <- unsafeFreezeRef a'; setRef a (ta + ta')
     tb <- unsafeFreezeRef b; tb' <- unsafeFreezeRef b'; setRef b (tb + tb')
     tc <- unsafeFreezeRef c; tc' <- unsafeFreezeRef c'; setRef c (tc + tc')
     td <- unsafeFreezeRef d; td' <- unsafeFreezeRef d'; setRef d (td + td')
     te <- unsafeFreezeRef e; te' <- unsafeFreezeRef e'; setRef e (te + te')
     return block

-- Translate a 160-bit block into an array of 20 8-bits.
arr_block :: Block -> Software (SArr SWord8)
arr_block (a, b, c, d, e) =
  do ta  <- unsafeFreezeRef a
     tb  <- unsafeFreezeRef b
     tc  <- unsafeFreezeRef c
     td  <- unsafeFreezeRef d
     te  <- unsafeFreezeRef e
     out <- newArr 20
     let shift i = 8 * (3 - (i2n i)) :: SWord32
     for 0 3 $ \i -> setArr out (i)      $ i2n (ta `shiftR` shift i)
     for 0 3 $ \i -> setArr out (i + 4)  $ i2n (tb `shiftR` shift i)
     for 0 3 $ \i -> setArr out (i + 8)  $ i2n (tc `shiftR` shift i)
     for 0 3 $ \i -> setArr out (i + 12) $ i2n (td `shiftR` shift i)
     for 0 3 $ \i -> setArr out (i + 16) $ i2n (te `shiftR` shift i)
     return out

----------------------------------------

sha1_pad :: SArr SWord8 -> Software (SArr SWord8)
sha1_pad message =
  do let len = length message
     bits <- shareM (i2n len * 8 :: SWord64)
     pad  <- newArr 64
     -- copy original message.
     copyArr pad message
     -- add the single one.
     setArr  pad len 1
     -- fill with zeroes.
     for (len + 1) (55) $ \i -> setArr pad i 0
     -- add length in last 8 8-bits.
     for (56) (63) $ \i ->
       let shift = (8 * (63 - (i2n i))) :: SWord32
       in  setArr pad i (i2n (bits `shiftR` shift))
     return pad

sha1_extend :: SArr SWord8 -> Software (SIrr SWord32)
sha1_extend message =
  do pad    :: SArr SWord8  <- sha1_pad message
     ex     :: SArr SWord32 <- newArr 80
     -- truncate original block.
     ipad   :: SIrr SWord8  <- unsafeFreezeArr pad
     for 0 15 (\(i :: SExp Word8) ->
       setArr ex i
         (   (i2n $ ipad ! (i*4  ))
           + (i2n $ ipad ! (i*4+1)) `shiftL` (8  :: SWord32)
           + (i2n $ ipad ! (i*4+2)) `shiftL` (16 :: SWord32)
           + (i2n $ ipad ! (i*4+3)) `shiftL` (24 :: SWord32)
         ))
     -- extend block with new words.
     iex   :: SIrr SWord32 <- unsafeFreezeArr ex
     for 16 79 (\(i :: SWord8) ->
       setArr ex i $ flip rotateL (1 :: SWord32)
         (       (iex ! (i-3 ))
           `xor` (iex ! (i-8 ))
           `xor` (iex ! (i-14))
           `xor` (iex ! (i-16))
         ))
     unsafeFreezeArr ex

--------------------------------------------------------------------------------

test_sha1 :: Software ()
test_sha1 =
  do m <- msg

-- The msg is "The quick brown fox jumps over the lazy dog",
-- represented with an Word8 encoding of its characters. 
msg :: Software (SArr SWord8)
msg = initArr [84,104,101,32,113,117,105,99,107,32,98,114,111,119,110,32,102,111,120,32,106,117,109,112,115,32,111,118,101,114,32,116,104,101,32,108,97,122,121,32,100,111,103]

--------------------------------------------------------------------------------
