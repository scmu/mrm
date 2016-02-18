{-# LANGUAGE
    GADTs
  , KindSignatures
  , DataKinds
  , TypeOperators
  #-}

module Data.Match.Fix where

import Data.Match.Membership

data Fix (fs :: [* -> *]) where
    In :: Functor f => Elem f fs -> f (Fix fs) -> Fix fs

inn :: (Mem f fs, Functor f) => f (Fix fs) -> Fix fs
inn = In witness
