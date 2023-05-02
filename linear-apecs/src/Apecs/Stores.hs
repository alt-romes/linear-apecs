{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE Strict                #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}

module Apecs.Stores
  ( Map, Cache, Unique,
    Global,
    Cachable,
    ReadOnly, setReadOnly, destroyReadOnly
    -- Register, regLookup
  ) where

import qualified Prelude.Base as Base
import qualified Control.Monad as Base
import qualified Data.Unrestricted.Linear as Ur
import           Control.Functor.Linear as Linear
import           Control.Monad.IO.Class.Linear
import           System.IO.Linear
import           Data.IORef (IORef, modifyIORef')
import           Data.Bits                   (shiftL, (.&.))
import qualified Data.IntMap.Strict          as M
import           Data.Proxy
import           Data.Typeable               (Typeable, typeRep)
import qualified Data.Vector.Mutable         as VM
import qualified Data.Vector.Unboxed         as U
import qualified Data.Vector.Unboxed.Mutable as UM
import           GHC.TypeLits

import           Apecs.Core

-- | A map based on 'Data.IntMap.Strict'. O(log(n)) for most operations.
newtype Map c = Map (IORef (M.IntMap c))

type instance Elem (Map c) = c
instance MonadIO m => ExplInit m (Map c) where
  explInit = liftIO$ Ur.lift Map <$> newIORef Base.mempty

instance (MonadIO m, Typeable c) => ExplGet m (Map c) where
  explExists (Map ref) ety = liftIO$ Ur.lift (M.member ety) <$> readIORef ref
  explGet    (Map ref) ety = liftIO$ flip fmap (Ur.lift (M.lookup ety) <$> readIORef ref) $ \case
    Ur (Just c) -> Ur c
    Ur notFound -> error $ unwords
      [ "Reading non-existent Map component"
      , show (typeRep notFound)
      , "for entity"
      , show ety
      ]
  {-# INLINE explExists #-}
  {-# INLINE explGet #-}

instance MonadIO m => ExplSet m (Map c) where
  {-# INLINE explSet #-}
  explSet (Map ref) ety x = liftSystemIO$
    modifyIORef' ref (M.insert ety x)

instance MonadIO m => ExplDestroy m (Map c) where
  {-# INLINE explDestroy #-}
  explDestroy (Map ref) ety = liftIO $ Linear.do
    Ur x <- readIORef ref
    writeIORef ref (M.delete ety x)

instance MonadIO m => ExplMembers m (Map c) where
  {-# INLINE explMembers #-}
  explMembers (Map ref) = liftIO$ Ur.lift (U.fromList Base.. M.keys) <$> readIORef ref

-- | A Unique contains zero or one component.
--   Writing to it overwrites both the previous component and its owner.
--   Its main purpose is to be a 'Map' optimized for when only ever one component inhabits it.
newtype Unique c = Unique (IORef (Maybe (Int, c)))
type instance Elem (Unique c) = c
instance MonadIO m => ExplInit m (Unique c) where
  explInit = liftIO$ Ur.lift Unique <$> newIORef Nothing

instance (MonadIO m, Typeable c) => ExplGet m (Unique c) where
  {-# INLINE explGet #-}
  explGet (Unique ref) _ = liftIO$ flip fmap (readIORef ref) $ \case
    Ur (Just (_, c))  -> Ur c
    Ur notFound -> error $ unwords
      [ "Reading non-existent Unique component"
      , show (typeRep notFound)
      ]

  {-# INLINE explExists #-}
  explExists (Unique ref) ety = liftIO$ Ur.lift (Base.maybe False ((Base.== ety) Base.. Base.fst)) <$> readIORef ref

instance MonadIO m => ExplSet m (Unique c) where
  {-# INLINE explSet #-}
  explSet (Unique ref) ety c = liftIO$ writeIORef ref (Just (ety, c))

instance MonadIO m => ExplDestroy m (Unique c) where
  {-# INLINE explDestroy #-}
  explDestroy (Unique ref) ety = Linear.do
    Ur x <- liftIO (readIORef ref)
    case x of
      Nothing -> pure ()
      Just (i, _)
        | i == ety  -> liftIO (writeIORef ref Nothing)
        | otherwise -> pure ()

instance MonadIO m => ExplMembers m (Unique c) where
  {-# INLINE explMembers #-}
  explMembers (Unique ref) = liftIO$ flip fmap (readIORef ref) $ \case
    Ur Nothing -> Ur Base.mempty
    Ur (Just (ety, _)) -> Ur (U.singleton ety)

-- | A 'Global' contains exactly one component.
--   The initial value is 'mempty' from the component's 'Monoid' instance.
--   Querying a 'Global' at /any/ Entity yields this one component, effectively sharing the component between /all/ entities.
--
--   A Global component can be read with @'get' 0@ or @'get' 1@ or even @'get' undefined@.
--   The convenience entity 'global' is defined as -1, and can be used to make operations on a global more explicit, i.e. 'Time t <- get global'.
--
--   You also can read and write Globals during a 'cmap' over other components.
newtype Global c = Global (IORef c)
type instance Elem (Global c) = c
instance (Monoid c, MonadIO m) => ExplInit m (Global c) where
  {-# INLINE explInit #-}
  explInit = liftIO$ Ur.lift Global <$> newIORef mempty

instance MonadIO m => ExplGet m (Global c) where
  {-# INLINE explGet #-}
  explGet (Global ref) _ = liftIO$ readIORef ref
  {-# INLINE explExists #-}
  explExists _ _ = return (Ur True)

instance MonadIO m => ExplSet m (Global c) where
  {-# INLINE explSet #-}
  explSet (Global ref) _ c = liftIO$ writeIORef ref c

-- | Class of stores that behave like a regular map, and can therefore safely be cached.
--   This prevents stores like `Unique` and 'Global', which do /not/ behave like simple maps, from being cached.
class Cachable s
instance Cachable (Map s)
instance (KnownNat n, Cachable s) => Cachable (Cache n s)

-- | A cache around another store.
--   Caches store their members in a fixed-size vector, so read/write operations become O(1).
--   Caches can provide huge performance boosts, especially when working with large numbers of components.
--
--   The cache size is given as a type-level argument.
--
--   Note that iterating over a cache is linear in cache size, so sparsely populated caches might /decrease/ performance.
--   In general, the exact size of the cache does not matter as long as it reasonably approximates the number of components present.
--
--   The cache uses entity (-2) internally to represent missing entities.
--   If you manually manipulate Entity values, be careful that you do not use (-2)
--
--   The actual cache is not necessarily the given argument, but the next biggest power of two.
--   This is allows most operations to be expressed as bit masks, for a large potential performance boost.
data Cache (n :: Nat) s =
  Cache Int (UM.IOVector Int) (VM.IOVector (Elem s)) s

cacheMiss :: t
cacheMiss = error "Cache miss! If you are seeing this during normal operation, please open a bug report at https://github.com/jonascarpay/apecs"

type instance Elem (Cache n s) = Elem s

instance (MonadIO m, ExplInit m s, KnownNat n, Cachable s) => ExplInit m (Cache n s) where
  {-# INLINE explInit #-}
  explInit = Linear.do
    let n = fromIntegral$ natVal (Proxy @n) :: Int
        size = Base.head Base.. Base.dropWhile (Base.<n) $ Base.iterate (`shiftL` 1) 1
        mask = size - 1
    Ur tags  <- liftSystemIOU$ UM.replicate size (-2)
    Ur cache <- liftSystemIOU$ VM.replicate size cacheMiss
    Ur child <- explInit
    return $ Ur $ Cache mask tags cache child

instance (MonadIO m, ExplGet m s) => ExplGet m (Cache n s) where
  {-# INLINE explGet #-}
  explGet (Cache mask tags cache s) ety = Linear.do
    let index = ety .&. mask
    tag <- liftSystemIO $ UM.unsafeRead tags index
    if tag == ety
       then liftSystemIOU $ VM.unsafeRead cache index
       else explGet s ety

  {-# INLINE explExists #-}
  explExists (Cache mask tags _ s) ety = Linear.do
    tag <- liftSystemIO$ UM.unsafeRead tags (ety .&. mask)
    if tag == ety then return (Ur True) else explExists s ety

instance (MonadIO m, ExplSet m s) => ExplSet m (Cache n s) where
  {-# INLINE explSet #-}
  explSet (Cache mask tags cache s) ety x = Linear.do
    let index = ety .&. mask
    Ur tag <- liftSystemIOU$ UM.unsafeRead tags index
    if (tag /= (-2) && tag /= ety)
       then Linear.do
         Ur cached <- liftSystemIOU$ VM.unsafeRead cache index
         explSet s tag cached
       else pure ()
    liftSystemIO$ UM.unsafeWrite tags  index ety
    liftSystemIO$ VM.unsafeWrite cache index x

instance (MonadIO m, ExplDestroy m s) => ExplDestroy m (Cache n s) where
  {-# INLINE explDestroy #-}
  explDestroy (Cache mask tags cache s) ety = Linear.do
    let index = ety .&. mask
    Ur tag <- liftSystemIOU$ UM.unsafeRead tags (ety .&. mask)
    liftSystemIO $
      Base.when (tag == ety) $ do
        UM.unsafeWrite tags  index (-2)
        VM.unsafeWrite cache index cacheMiss
    explDestroy s ety

instance (MonadIO m, ExplMembers m s) => ExplMembers m (Cache n s) where
  {-# INLINE explMembers #-}
  explMembers (Cache mask tags _ s) = Linear.do
    Ur cached <- liftSystemIOU$ U.filter (Base./= (-2)) Base.<$> U.freeze tags
    let etyFilter ety = (Base./= ety) Base.<$> UM.unsafeRead tags (ety .&. mask)
    Ur stored <- explMembers s >>= \case (Ur xs) -> liftSystemIOU (U.filterM etyFilter xs)
    return $! Ur (cached U.++ stored)

-- | Wrapper that makes a store read-only by hiding its 'ExplSet' and 'ExplDestroy' instances.
--   This is primarily used to protect the 'EntityCounter' from accidental overwrites.
--   Use 'setReadOnly' and 'destroyReadOnly' to override.
newtype ReadOnly s = ReadOnly s
type instance Elem (ReadOnly s) = Elem s

instance (Functor m, ExplInit m s) => ExplInit m (ReadOnly s) where
  explInit = (\case (Ur x) -> Ur (ReadOnly x)) <$> explInit

instance ExplGet m s => ExplGet m (ReadOnly s) where
  explExists (ReadOnly s) = explExists s
  explGet    (ReadOnly s) = explGet s
  {-# INLINE explExists #-}
  {-# INLINE explGet #-}

instance ExplMembers m s => ExplMembers m (ReadOnly s) where
  {-# INLINE explMembers #-}
  explMembers (ReadOnly s) = explMembers s

setReadOnly :: forall w m s c.
  ( Has w m c
  , Storage c ~ ReadOnly s
  , Elem s ~ c
  , ExplSet m s
  , Dupable w
  ) => Entity -> c -> SystemT w m ()
setReadOnly (Entity ety) c = Linear.do
  Ur (ReadOnly s) <- getStore
  lift $ explSet s ety c

destroyReadOnly :: forall w m s c.
  ( Has w m c
  , Storage c ~ ReadOnly s
  , Elem s ~ c
  , ExplDestroy m s
  , Dupable w
  ) => Entity -> Proxy c -> SystemT w m ()
destroyReadOnly (Entity ety) _ = Linear.do
  Ur (ReadOnly s :: Storage c) <- getStore
  lift $ explDestroy s ety
