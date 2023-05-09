{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE QualifiedDo           #-}
{-# LANGUAGE LinearTypes           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE Strict                #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

import Prelude hiding (IO)
import qualified Control.Monad
import           Criterion
import qualified Criterion.Main  as C
import           Criterion.Types
import           Linear

import qualified Prelude.Base

import Control.Functor.Linear as Linear
import Streaming.Prelude.Linear
import System.IO.Linear

import           Apecs.Linear

-- pos_vel
newtype ECSPos = ECSPos (V2 Float) deriving (Prelude.Base.Eq, Show, Prelude.Base.Num)
instance Component ECSPos where type Storage ECSPos = Cache 10000 (Map ECSPos)

newtype ECSVel = ECSVel (V2 Float) deriving (Prelude.Base.Eq, Show, Prelude.Base.Num)
instance Component ECSVel where type Storage ECSVel = Cache 1000 (Map ECSVel)

-- makeWorld "PosVel" [''ECSPos, ''ECSVel]

data PosVel = PosVel (Ur (Storage ECSPos)) (Ur (Storage ECSVel)) (Ur (Storage EntityCounter))

instance Consumable PosVel where
  consume (PosVel (Ur a) (Ur b) (Ur c)) = ()

instance Dupable PosVel where
  dup2 (PosVel (Ur a) (Ur b) (Ur c)) = (PosVel (Ur a) (Ur b) (Ur c), PosVel (Ur a) (Ur b) (Ur c))

instance Has PosVel IO EntityCounter where
  getStore = SystemT $ ReaderT $ \(PosVel (Ur a) (Ur b) (Ur c)) -> pure (Ur c)

instance Has PosVel IO ECSPos where
  getStore = SystemT $ ReaderT $ \(PosVel (Ur a) (Ur b) (Ur c)) -> pure (Ur a)

instance Has PosVel IO ECSVel where
  getStore = SystemT $ ReaderT $ \(PosVel (Ur a) (Ur b) (Ur c)) -> pure (Ur b)

initPosVel :: IO PosVel
initPosVel = PosVel <$> explInit <*> explInit <*> explInit

posVelInit :: SystemT PosVel IO ()
posVelInit = Linear.do
  mapM_ (forget pure) $ replicateM 1000 $ newEntity (ECSPos 0, ECSVel 1)
  mapM_ (forget pure) $ replicateM 9000 $ newEntity (ECSPos 0)

posVelStep :: SystemT PosVel IO ()
posVelStep = cmap $ \(ECSVel v, ECSPos p) -> ECSPos (p Prelude.Base.+ v)

main :: Prelude.Base.IO ()
main = C.defaultMainWith (C.defaultConfig {timeLimit = 10})
  [ bgroup "pos_vel"
    [ bench "init" $ whnfIO (withLinearIO $ initPosVel >>= runSystem (move <$> posVelInit))
    , bench "step" $ whnfIO (withLinearIO $ initPosVel >>= runSystem (posVelInit >> move <$> posVelStep))
    ]
  ]

