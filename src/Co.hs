{-# language FlexibleContexts #-}
{-# language GADTs #-}

{-# language ScopedTypeVariables #-}

module Co where

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

type SArr  a = Array  Software (SExp a)
type SIArr a = IArray Software (SExp a)
type SIx     = Ix     Software

type SBool   = SExp P.Bool
type SWord8  = SExp Word8
type SWord16 = SExp Word16
type SWord32 = SExp Word32

--------------------------------------------------------------------------------
-- * SHA1
--
-- ...
--
-- *** For simplicity, lets assume we only reveieve <55 8-bits to hash,
--     that is, SHA1 pre-processing will only create one block.
--------------------------------------------------------------------------------

sha1 :: SArr Word8 -> Software (SArr Word8)
sha1 msg =
  do b <- sha1_init
     p <- sha1_preprocess msg -- only returns one block.

     let f :: SWord8 -> SWord32 -> SWord32 -> SWord32 -> SWord32
         f t b c d =
           (0  <= t && t <= 19 :: SBool) ? ((b .&. c) .|. ((complement b) .&. d)) $
           (20 <= t && t <= 39 :: SBool) ? (b `xor` c `xor` d) $
           (40 <= t && t <= 59 :: SBool) ? ((b .&. c) .|. (b .&. d) .|. (c .&. d))
                                         $ (b `xor` c `xor` d)

     let k :: SWord8 -> SWord32
         k t =
           (0  <= t && t <= 19 :: SBool) ? 0x5a827999 $
           (20 <= t && t <= 39 :: SBool) ? 0x6ed9eba1 $
           (40 <= t && t <= 59 :: SBool) ? 0x8f1bbcdc
                                         $ 0xca62c1d6

     let step :: SIArr Word32 -> SWord8 -> SArr Word32 -> Software ()
         step w t arr =
           do b   <- unsafeFreezeArr arr
              ft  <- shareM (f t (b!!1) (b!!2) (b!!3))
              kt  <- shareM (k t)
              tmp <- shareM (
                ((b!!0) `rotateL` (5 :: SWord32)) + ft + (b!!4) + (w!!t) + kt)
              setArr arr 0 $ tmp
              setArr arr 1 $ b!!0
              setArr arr 2 $ (b!!1) `rotateL` (30 :: SWord32)
              setArr arr 3 $ b!!2
              setArr arr 4 $ b!!3
     
     let block :: SIArr Word32 -> SArr Word32 -> Software ()
         block w b = for (0 :: SWord8) (79 :: SWord8) $ \i -> step w i b

     let process :: SIArr Word32 -> SArr Word32 -> Software ()
         process w b = block w b -- we only have one block.

     let words :: SArr Word32 -> Software (SArr Word8)
         words b =
           do b'  <- unsafeFreezeArr b
              out <- newArr 20
              for (0 :: SWord8) (4 :: SWord8) $ \i ->
                do let bi = (b'!!i)
                   setArr out ((i*4))   (i2n (bi))
                   setArr out ((i*4)+1) (i2n (bi `shiftR` (8  :: SWord32)))
                   setArr out ((i*4)+2) (i2n (bi `shiftR` (16 :: SWord32)))
                   setArr out ((i*4)+3) (i2n (bi `shiftR` (24 :: SWord32)))
              return out

     process p b
     words   b

(!!) :: IArray Software (SExp Word32) -> SExp Word8 -> SExp Word32
(!!) arr ix = arr ! ix

----------------------------------------

sha1_init :: Software (SArr Word32)
sha1_init = initArr [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0]

sha1_padding :: SArr Word8 -> Software (SArr Word8)
sha1_padding msg =
  do m :: SIArr Word8 <- unsafeFreezeArr msg
     p :: SArr  Word8 <- newArr (value 64)
     let len  = length msg     :: SExp Word8
         pad  = 56 - (len + 1) :: SExp Word8
     -- copy message.
     for 0 (len - 1) $ \i ->
       setArr p i (m ! i)
     -- add a one.
     setArr p len 1
     -- fill zeroes.
     for (len + 1) 56 $ \i ->
       setArr p i 0
     -- add msg length in bits.
     bits <- shareM (i2n (len * 8) :: SExp Word64)
     for 57 64 $ \i ->
       let ix = i2n (7 - (i - 57))   :: SExp Word32
           b8 = bits `shiftR` (8*ix) :: SExp Word64
       in  setArr p i (i2n b8)
           -- conversion should specify the significant part with a bit-wise
           -- and op.: i2n (b8 .&. (value 0xFF)), not sure if required though.
     return p

sha1_preprocess :: SArr Word8 -> Software (SIArr Word32)
sha1_preprocess msg =
  do pad  :: SArr  Word8  <- sha1_padding msg
     pad' :: SIArr Word8  <- unsafeFreezeArr pad
     ex   :: SArr  Word32 <- newArr (value 80)
     -- truncate original message.
     for 0 15 $ \(i :: SExp Word8) ->
       setArr ex i
         ( i2n ( pad' ! (i*4))
         + i2n ((pad' ! (i*4+1)) `shiftL` (8  :: SExp Word32))
         + i2n ((pad' ! (i*4+2)) `shiftL` (16 :: SExp Word32))
         + i2n ((pad' ! (i*4+3)) `shiftL` (24 :: SExp Word32))
         )
     -- extend with new words.
     for 16 79 $ \(i :: SExp Word8) ->
       setArr ex i $ flip rotateL (1 :: SExp Word32)
         (     (i2n (pad' ! (i-3)))
         `xor` (i2n (pad' ! (i-8)))
         `xor` (i2n (pad' ! (i-14)))
         `xor` (i2n (pad' ! (i-16)))
         )
     unsafeFreezeArr ex

----------------------------------------

-- The msg is "The quick brown fox jumps over the lazy dog",
-- represented with an Word8 encoding of its characters. 
msg :: Software (SArr Word8)
msg = initArr [84,104,101,32,113,117,105,99,107,32,98,114,111,119,110,32,102,111,120,32,106,117,109,112,115,32,111,118,101,114,32,116,104,101,32,108,97,122,121,32,100,111,103]

--------------------------------------------------------------------------------
