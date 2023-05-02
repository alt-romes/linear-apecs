{-# OPTIONS_GHC -fno-warn-unused-imports #-} -- For Data.Semigroup compatibility

{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE Strict                     #-}
{-# LANGUAGE TypeFamilies               #-}

module Apecs.Util (
  -- * Utility
  -- runGC,
  global,

  -- * EntityCounter
  EntityCounter(..), nextEntity, newEntity, newEntity_,
) where

import qualified Prelude.Base
import           Control.Functor.Linear as Linear hiding (get)
import           Control.Monad.IO.Class.Linear
import           Data.Monoid.Linear
import           System.Mem           (performMajorGC)

import           Apecs.Core
import           Apecs.Stores
import           Apecs.System

-- | Convenience entity, for use in places where the entity value does not matter, i.e. a global store.
global :: Entity
global = Entity (-1)

-- | Component used by newEntity to track the number of issued entities.
--   Automatically added to any world created with @makeWorld@
newtype EntityCounter = EntityCounter {getCounter :: Sum Int} deriving (Prelude.Base.Semigroup, Prelude.Base.Monoid, Prelude.Base.Eq, Semigroup, Monoid, Show)

instance Component EntityCounter where
  type Storage EntityCounter = ReadOnly (Global EntityCounter)

-- | Bumps the EntityCounter and yields its value
{-# INLINE nextEntity #-}
nextEntity :: (MonadIO m, Dupable w, Get w m EntityCounter) => SystemT w m (Ur Entity)
nextEntity = Linear.do
  Ur (EntityCounter n) <- get global
  setReadOnly global (EntityCounter $ n Prelude.Base.+ 1)
  return $ Ur $ Entity $ getSum n

-- | Writes the given components to a new entity, and yields that entity.
-- The return value is often ignored.
{-# INLINE newEntity #-}
newEntity :: (MonadIO m, Dupable w, Set w m c, Get w m EntityCounter)
          => c -> SystemT w m (Ur Entity)
newEntity c = Linear.do
  Ur ety <- nextEntity
  set ety c
  return (Ur ety)

-- | Writes the given components to a new entity without yelding the result.
-- Used mostly for convenience.
{-# INLINE newEntity_ #-}
newEntity_ :: (MonadIO m, Dupable world, Set world m component, Get world m EntityCounter)
           => component -> SystemT world m ()
newEntity_ component = Linear.do
  Ur entity <- nextEntity
  set entity component

-- | Explicitly invoke the garbage collector
-- ROMES:TODO: Why doesn't this instance work?
-- runGC :: Dupable w => System w ()
-- runGC = liftSystemIO $ performMajorGC
