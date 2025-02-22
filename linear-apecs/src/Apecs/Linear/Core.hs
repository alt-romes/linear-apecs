{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}

module Apecs.Linear.Core where

import qualified Prelude.Base as Base
import           Control.Functor.Linear
import qualified Data.Functor.Linear as Data.Linear
import           Control.Monad.Catch
import           Control.Monad.IO.Class.Linear
-- import           Control.Monad.Reader
import qualified Data.Vector.Unboxed  as U

-- | An Entity is just an integer, used to index into a component store.
--   In general, use @newEntity@, @cmap@, and component tags instead of manipulating these directly.
--
--   For performance reasons, negative values like (-1) are reserved for stores to represent special values, so avoid using these.
newtype Entity = Entity {unEntity :: Int} deriving (FromInteger, Multiplicative, MultIdentity, Semiring, Additive, AddIdentity, AdditiveGroup, Ring, Num, Eq, Ord, Show, Enum, Base.Num, Base.Eq,
                                                    Dupable, Consumable, Movable)

-- | A SystemT is a newtype around `ReaderT w m a`, where `w` is the game world variable.
--   Systems serve to
--
--   * Allow type-based lookup of a component's store through @getStore@.
--
--   * Lift side effects into their host Monad.
newtype SystemT w m a = SystemT {unSystem :: ReaderT w m a} deriving (Data.Linear.Functor, Data.Linear.Applicative, Functor, Monad, Applicative, MonadTrans)

instance (MonadIO m, Dupable w) => MonadIO (SystemT w m) where
  liftIO io = SystemT (ReaderT \r -> case consume r of () -> liftIO io)

type System w a = SystemT w IO a

-- deriving instance Monad m => MonadReader w (SystemT w m)

-- | A component is defined by specifying how it is stored.
--   The constraint ensures that stores and components are mapped one-to-one.
class (Elem (Storage c) ~ c) => Component c where
  type Storage c

-- | @Has w m c@ means that world @w@ can produce a @Storage c@.
--   It is parameterized over @m@ to allow stores to be foreign.
class (Monad m, Component c) => Has w m c where
  getStore :: SystemT w m (Ur (Storage c))

-- | The type of components stored by a store, e.g. @Elem (Map c) = c@.
type family Elem s

-- | Indicates that the store @s@ can be initialized.
--   Generally, \"base\" stores like @Map c@ can be initialized, but composite stores like @MaybeStore s@ cannot.
class ExplInit m s where
  -- | Initialize a new empty store.
  explInit :: m (Ur s)

-- | Stores that we can read using @explGet@ and @explExists@.
--   For some entity @e@, @eplGet s e@ is only guaranteed to be safe if @explExists s e@ returns @True@.
class Monad m => ExplGet m s where
  -- | Reads a component from the store. What happens if the component does not exist is left undefined, and might not necessarily crash.
  explGet :: s -> Int -> m (Ur (Elem s))
  -- | Returns whether there is a component for the given index.
  explExists :: s -> Int -> m (Ur Bool)

-- | Stores that can be written.
class Monad m => ExplSet m s where
  -- | Writes a component to the store.
  explSet :: s -> Int -> Elem s -> m ()

-- | Stores that components can be removed from.
class Monad m => ExplDestroy m s where
  -- | Destroys the component for a given index.
  explDestroy :: s -> Int -> m ()

-- | Stores that we can request a list of member entities for.
class Monad m => ExplMembers m s where
  -- | Returns an unboxed vector of member indices
  explMembers :: s -> m (Ur (U.Vector Int))

type Get     w m c = (Has w m c, ExplGet     m (Storage c))
type Set     w m c = (Has w m c, ExplSet     m (Storage c))
type Members w m c = (Has w m c, ExplMembers m (Storage c))
type Destroy w m c = (Has w m c, ExplDestroy m (Storage c))
