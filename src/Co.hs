{-# language ScopedTypeVariables #-}

module Co where

import Control.Monad

import qualified Language.VHDL              as V
import qualified Language.Embedded.Hardware as H

import Feldspar
import Feldspar.Software
import Feldspar.Hardware

import qualified Feldspar.Software.Compile as Soft
import qualified Feldspar.Hardware.Compile as Hard

import Prelude hiding (length)
import qualified Prelude as P

--------------------------------------------------------------------------------
-- Short-hands.

type SArr  a = Array  Software (SExp a)
type SIArr a = IArray Software (SExp a)
type SIx     = Ix     Software

--------------------------------------------------------------------------------
-- * SHA1
--
-- ...
--
-- *** For simplicity, lets assume we only reveieve <55 8-bits to hash.
--------------------------------------------------------------------------------

sha1 :: SArr Word8 -> Software (SArr Word8)
sha1 msg =
  do block <- sha1_init
     pad   <- sha1_padding msg

     return msg

-- The msg is "The quick brown fox jumps over the lazy dog",
-- represented with an Word8 encoding of its characters. 
msg :: Software (SArr Word8)
msg = initArr [84,104,101,32,113,117,105,99,107,32,98,114,111,119,110,32,102,111,120,32,106,117,109,112,115,32,111,118,101,114,32,116,104,101,32,108,97,122,121,32,100,111,103]

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

sha1_preprocess :: SArr Word8 -> Software (SArr Word32)
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
     return ex

--------------------------------------------------------------------------------
