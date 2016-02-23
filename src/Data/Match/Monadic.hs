{-# LANGUAGE
    GADTs
  , TypeOperators
  #-}

module Data.Match.Monadic where

import Data.Match (Algebras, Match(..), fold, transAlg)
import Data.Match.Fix (Fix())
import Data.Match.Subset ((<:)(..))
import Data.ConstrainedList (TraversableList(..), Traversables(trep))

import Prelude hiding (sequence)
import Data.Traversable (sequence)
import Control.Monad (liftM)

mliftWith :: Monad m => TraversableList fs -> Match fs a b -> Match fs (m a) (m b)
mliftWith TNil       Void       = Void
mliftWith (TCons ts) (k ::: ks) = (liftM k . sequence) ::: mliftWith ts ks

mlift :: (Monad m, Traversables fs) => Match fs a b -> Match fs (m a) (m b)
mlift = mliftWith trep

transMAlg :: (Monad m, Traversables fs, fs <: gs) => Algebras fs (m (Fix gs))
transMAlg = mlift transAlg

transM :: (Monad m, Traversables fs, fs <: gs) => Fix fs -> m (Fix gs)
transM = fold transMAlg
