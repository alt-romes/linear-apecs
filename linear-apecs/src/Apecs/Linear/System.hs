{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE Strict                #-}
{-# LANGUAGE LambdaCase            #-}

module Apecs.Linear.System where

import           Control.Functor.Linear as Linear hiding (modify)
import           Data.Proxy
import qualified Data.Vector.Unboxed  as U
import qualified Data.Unrestricted.Linear as Ur

import Apecs.Linear.Components ()
import Apecs.Linear.Core

-- | Run a system in a game world
{-# INLINE runSystem #-}
runSystem :: SystemT w m a -> w %1 -> m a
runSystem sys = runReaderT (unSystem sys)

-- | Run a system in a game world
{-# INLINE runWith #-}
runWith :: w %1 -> SystemT w m a -> m a
runWith = flip runSystem

-- | Read a Component
{-# INLINE get #-}
get :: forall w m c. (Dupable w, Get w m c) => Entity -> SystemT w m (Ur c)
get (Entity ety) = Linear.do
  Ur (s :: Storage c) <- getStore
  lift$ explGet s ety

-- | Writes a Component to a given Entity. Will overwrite existing Components.
{-# INLINE set #-}
set, ($=) :: forall w m c. (Dupable w, Set w m c) => Entity -> c -> SystemT w m ()
set (Entity ety) x = Linear.do
  Ur (s :: Storage c) <- getStore
  lift$ explSet s ety x

-- | @set@ operator
($=) = set
infixr 2 $=

-- | Returns whether the given entity has component @c@
{-# INLINE exists #-}
exists :: forall w m c. (Dupable w, Get w m c) => Entity -> Proxy c -> SystemT w m (Ur Bool)
exists (Entity ety) _ = Linear.do
  Ur (s :: Storage c) <- getStore
  lift$ explExists s ety

-- | Destroys component @c@ for the given entity.
{-# INLINE destroy #-}
destroy :: forall w m c. (Dupable w, Destroy w m c) => Entity -> Proxy c -> SystemT w m ()
destroy (Entity ety) ~_ = Linear.do
  Ur (s :: Storage c) <- getStore
  lift$ explDestroy s ety

-- | Applies a function, if possible.
{-# INLINE modify #-}
modify, ($~) :: forall w m cx cy. (Dupable w, Get w m cx, Set w m cy) => Entity -> (cx -> cy) -> SystemT w m ()
modify (Entity ety) f = Linear.do
  Ur (sx :: Storage cx) <- getStore
  Ur (sy :: Storage cy) <- getStore
  lift$ Linear.do
    Ur possible <- explExists sx ety
    if possible
       then Linear.do
          Ur x <- explGet sx ety
          explSet sy ety (f x)
       else pure ()

-- | @modify@ operator
($~) = modify
infixr 2 $~

-- | Maps a function over all entities with a @cx@, and writes their @cy@.
{-# INLINE cmap #-}
cmap :: forall w m cx cy. (Dupable w, Get w m cx, Members w m cx, Set w m cy)
     => (cx -> cy) -> SystemT w m ()
cmap f = Linear.do
  Ur (sx :: Storage cx) <- getStore
  Ur (sy :: Storage cy) <- getStore
  Ur sl <- lift$ explMembers sx
  Ur () <- Ur.runUrT $
    U.forM_ sl $ \ e -> Ur.UrT $ Linear.do
      Ur r <- lift $ explGet sx e
      () <- lift $ explSet sy e (f r)
      pure $ Ur ()
  pure ()

-- | Conditional @cmap@, that first tests whether the argument satisfies some property.
--   The entity needs to have both a cx and cp component.
{-# INLINE cmapIf #-}
cmapIf :: forall w m cp cx cy.
  ( Dupable w
  , Get w m cx
  , Get w m cp
  , Members w m cx
  , Members w m cp -- ROMES:TODO: How come doesn't normal apecs require this?
  , Set w m cy )
  => (cp -> Bool)
  -> (cx -> cy)
  -> SystemT w m ()
cmapIf cond f = Linear.do
  Ur (sp :: Storage cp) <- getStore
  Ur (sx :: Storage cx) <- getStore
  Ur (sy :: Storage cy) <- getStore
  Ur sl <- lift $ explMembers (sx,sp)
  Ur () <- Ur.runUrT $
    U.forM_ sl $ \ e -> Ur.UrT $ Linear.do
      Ur p <- lift $ explGet sp e
      if cond p
         then Linear.do
           Ur x <- lift $ explGet sx e
           () <- lift $ explSet sy e (f x)
           pure $ Ur ()
         else pure $ Ur ()
  pure ()

-- | Monadically iterates over all entites with a @cx@, and writes their @cy@.
{-# INLINE cmapM #-}
cmapM :: forall w m cx cy. (Dupable w, Get w m cx, Set w m cy, Members w m cx)
      => (cx -> SystemT w m (Ur cy)) -> SystemT w m ()
cmapM sys = Linear.do
  Ur (sx :: Storage cx) <- getStore
  Ur (sy :: Storage cy) <- getStore
  Ur sl <- lift$ explMembers sx
  Ur () <- Ur.runUrT $
    U.forM_ sl $ \ e -> Ur.UrT $ Linear.do
      Ur x <- lift$ explGet sx e
      Ur y <- sys x
      () <- lift$ explSet sy e y
      pure (Ur ())
  pure ()

-- | Monadically iterates over all entites with a @cx@
{-# INLINE cmapM_ #-}
cmapM_ :: forall w m c. (Dupable w, Get w m c, Members w m c)
       => (c -> SystemT w m ()) -> SystemT w m ()
cmapM_ sys = Linear.do
  Ur (s :: Storage c) <- getStore
  Ur sl <- lift$ explMembers s
  Ur () <- Ur.runUrT $
    U.forM_ sl $ \ ety -> Ur.UrT $ Linear.do
      Ur x <- lift$ explGet s ety
      () <- sys x
      pure (Ur ())
  pure ()

-- | Fold over the game world; for example, @cfold max (minBound :: Foo)@ will find the maximum value of @Foo@.
--   Strict in the accumulator.
{-# INLINE cfold #-}
cfold :: forall w m c a. (Dupable w, Members w m c, Get w m c)
      => (a -> c -> a) -> a -> SystemT w m (Ur a)
cfold f a0 = Linear.do
  Ur (s :: Storage c) <- getStore
  Ur sl <- lift$ explMembers s
  Ur.runUrT $
    U.foldM' (\a e -> Ur.UrT $ (\case (Ur c) -> Ur (f a c)) <$> lift (explGet s e)) a0 sl

-- | Monadically fold over the game world.
--   Strict in the accumulator.
{-# INLINE cfoldM #-}
cfoldM :: forall w m c a. (Dupable w, Members w m c, Get w m c)
       => (a -> c -> SystemT w m (Ur a)) -> a -> SystemT w m (Ur a)
cfoldM sys a0 = Linear.do
  Ur (s :: Storage c) <- getStore
  Ur sl <- lift$ explMembers s
  Ur.runUrT $
    U.foldM' (\a e -> Ur.UrT (lift (explGet s e) >>= (\(Ur x) -> sys a x))) a0 sl

-- | Monadically fold over the game world.
--   Strict in the accumulator.
{-# INLINE cfoldM_ #-}
cfoldM_ :: forall w m c a. (Dupable w, Members w m c, Get w m c)
       => (a -> c -> SystemT w m (Ur a)) -> a -> SystemT w m ()
cfoldM_ sys a0 = Linear.do
  Ur (s :: Storage c) <- getStore
  Ur sl <- lift$ explMembers s
  Ur () <- Ur.runUrT $
    U.foldM'_ (\a e -> Ur.UrT (lift (explGet s e) >>= (\(Ur x) -> sys a x))) a0 sl
  pure ()

-- | Collect matching components into a list by using the specified test/process function.
--   You can use this to preprocess data before returning.
--   And you can do a test here that depends on data from multiple components.
--   Pass "Just" to simply collect all the items.
{-# INLINE collect #-}
collect :: forall components w m a. (Dupable w, Get w m components, Members w m components)
        => (components -> Maybe a)
        -> SystemT w m (Ur [a])
collect f = cfold (\acc x -> maybe acc (: acc) (f x)) []
