{-|
This module forms the apecs Prelude.
It selectively re-exports the user-facing functions from the submodules.
-}
module Apecs.Linear (
  -- * Core types
    SystemT(..), System, Component(..), Entity(..), Has(..), Not(..),
    Get, Set, Destroy, Members,

  -- * Stores
    Map, Unique, Global, Cache,
    explInit,

  -- * Systems
    get, set, ($=),
    destroy, exists,
    modify, ($~),
    cmap,  cmapM,  cmapM_,
    cfold, cfoldM, cfoldM_, collect,

  -- * Other
    runSystem, runWith,
    -- runGC,
    EntityCounter, newEntity, newEntity_, global,
    -- makeWorld, makeWorldAndComponents,

  -- * Re-exports
    -- asks, ask, liftIO, lift,
    Proxy (..)
) where

-- import           Control.Monad.IO.Class (liftIO)
-- import           Control.Monad.Reader (ask, asks, lift)
import           Data.Proxy

import           Apecs.Linear.Components
import           Apecs.Linear.Core
import           Apecs.Linear.Stores
import           Apecs.Linear.System
-- import           Apecs.TH
import           Apecs.Linear.Util
