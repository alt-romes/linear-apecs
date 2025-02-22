{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE LambdaCase            #-}

{-|
Stability : experimental

This module is experimental, and its API might change between point releases. Use at your own risk.
--}
module Apecs.Experimental.Components
  ( Redirect (..)
  , Head (..)
  ) where

import qualified Data.Vector.Unboxed as U
import qualified Prelude.Base
import qualified Data.Unrestricted.Linear as Ur

import Control.Functor.Linear as Linear

import Apecs.Core

-- | Pseudocomponent that when written to, actually writes @c@ to its entity argument.
--   Can be used to write to other entities in a 'cmap'.
data Redirect c = Redirect Entity c deriving (Prelude.Base.Eq, Show)

instance Eq c => Eq (Redirect c) where

instance Component c => Component (Redirect c) where
  type Storage (Redirect c) = RedirectStore (Storage c)

newtype RedirectStore s = RedirectStore s
type instance Elem (RedirectStore s) = Redirect (Elem s)

instance Has w m c => Has w m (Redirect c) where
  getStore = Ur.lift RedirectStore <$> getStore

instance (ExplSet m s) => ExplSet m (RedirectStore s) where
  explSet (RedirectStore s) _ (Redirect (Entity ety) c) = explSet s ety c


-- | Pseudocomponent that can be read like any other component, but will only
--   yield a single member when iterated over. Intended to be used as
--   @cmap $ Head (...) -> ...@
newtype Head c = Head c deriving (Eq, Show)
instance Component c => Component (Head c) where
  type Storage (Head c) = HeadStore (Storage c)

newtype HeadStore s = HeadStore s
type instance Elem (HeadStore s) = Head (Elem s)

instance Has w m c => Has w m (Head c) where
  getStore = Ur.lift HeadStore <$> getStore

instance (ExplGet m s) => ExplGet m (HeadStore s) where
  explExists (HeadStore s) ety = explExists s ety
  explGet (HeadStore s) ety = Ur.lift Head <$> explGet s ety

instance (ExplMembers m s) => ExplMembers m (HeadStore s) where
  explMembers (HeadStore s) = (\case Ur xs -> Ur (U.take 1 xs)) <$> explMembers s
