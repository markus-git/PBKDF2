{-# language FlexibleContexts #-}
{-# language GADTs #-}

{-# language ScopedTypeVariables #-}

module Co where

import Data.Char  (digitToInt)
import Data.Maybe (listToMaybe)
import Numeric    (readInt)

import Control.Applicative
import Control.Monad

import qualified Language.VHDL              as V
import qualified Language.Embedded.Hardware as H

import Feldspar
import Feldspar.Software hiding (Word)
import Feldspar.Hardware hiding (Word)

import qualified Feldspar.Software.Compile as Soft
import qualified Feldspar.Hardware.Compile as Hard

import Prelude (error, undefined, fst, snd, elem, Num(..), Integral, String, Maybe(), ($), (.))
import qualified Prelude as P

--------------------------------------------------------------------------------
-- * Generic stuff.
--------------------------------------------------------------------------------
--
-- todo: i2n introduced a number of extra type constraints that I've yet to
--       hide. Most should be fixable though, as they can be derived from
--       'SyntaxM' instead ('SyntaxM m ... => PredicateOf (DomainOf m) ...'
--       and so on).
--
--------------------------------------------------------------------------------

-- A block reperesents the 160-bit blocks that SHA1 operates over.
type Block m =
  ( Reference m (Expr m Word32)
  , Reference m (Expr m Word32)
  , Reference m (Expr m Word32)
  , Reference m (Expr m Word32)
  , Reference m (Expr m Word32)
  )

-- Short-hand for a block with unwrapped references.
type B m =
  ( Expr m Word32
  , Expr m Word32
  , Expr m Word32
  , Expr m Word32
  , Expr m Word32
  )

-- Creates a new block based on the initial values given by SHA1.
init_block
  :: (References m, SyntaxM m (Expr m Word32), Num (Expr m Word32))
  => m (Block m)
init_block =
  do a <- initRef 0x67452301
     b <- initRef 0xefcdab89
     c <- initRef 0x98badcfe
     d <- initRef 0x10325476
     e <- initRef 0xc3d2e1f0
     return (a, b, c, d, e)

-- Creates a new block by copying the values of the given block.
copy_block :: (References m, SyntaxM m (Expr m Word32)) => Block m -> m (Block m)
copy_block (a, b, c, d, e) =
  do a' <- initRef =<< unsafeFreezeRef a
     b' <- initRef =<< unsafeFreezeRef b
     c' <- initRef =<< unsafeFreezeRef c
     d' <- initRef =<< unsafeFreezeRef d
     e' <- initRef =<< unsafeFreezeRef e
     return (a', b', c', d', e')

-- Freezes each reference of a block.
freeze_block :: (References m, SyntaxM m (Expr m Word32)) => Block m -> m (B m)
freeze_block (a, b, c, d, e) =
  do a' <- unsafeFreezeRef a
     b' <- unsafeFreezeRef b
     c' <- unsafeFreezeRef c
     d' <- unsafeFreezeRef d
     e' <- unsafeFreezeRef e
     return (a', b', c', d', e')

-- Joins two blocks by inplace, pair-wise adding values of the second block
-- into the first block.
add_block
  :: (References m, SyntaxM m (Expr m Word32), Num (Expr m Word32))
  => Block m -> Block m -> m (Block m)
add_block block@(a, b, c, d, e) (a', b', c', d', e') =
  do ta <- unsafeFreezeRef a; ta' <- unsafeFreezeRef a'; setRef a (ta + ta')
     tb <- unsafeFreezeRef b; tb' <- unsafeFreezeRef b'; setRef b (tb + tb')
     tc <- unsafeFreezeRef c; tc' <- unsafeFreezeRef c'; setRef c (tc + tc')
     td <- unsafeFreezeRef d; td' <- unsafeFreezeRef d'; setRef d (td + td')
     te <- unsafeFreezeRef e; te' <- unsafeFreezeRef e'; setRef e (te + te')
     return block

--------------------------------------------------------------------------------
-- * Test
--------------------------------------------------------------------------------

-- The msg is "The quick brown fox jumps over the lazy dog",
-- represented with an Word8 encoding of its characters. 
msg
  :: forall m
   . ( Arrays m
     , SyntaxM m (Expr m Word8)
     , Num (Internal (Expr m Word8))
     -- hmm...
     , PredicateOf (DomainOf m) (Internal (Expr m Word8))
     )
  => m (Array m (Expr m Word8))
msg = initArr [84,104,101,32,113,117,105,99,107,32,98,114,111,119,110,32,102,111,120,32,106,117,109,112,115,32,111,118,101,114,32,116,104,101,32,108,97,122,121,32,100,111,103]

----------------------------------------

readBin :: Integral a => String -> Maybe a
readBin = fmap fst . listToMaybe . readInt 2 (`elem` "01") digitToInt

--------------------------------------------------------------------------------
