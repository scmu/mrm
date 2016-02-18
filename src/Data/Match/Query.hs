{-# LANGUAGE GADTs #-}

module Data.Match.Query where

import Data.Match (Algebras, Match(..), fold)
import Data.Match.Fix (Fix())
import Data.ConstrainedList (FoldableList(..), Foldables(frep))

import Data.Foldable (foldMap)
import Data.Monoid (Monoid())

queryMapMatch :: Monoid b => FoldableList fs -> (a -> b) -> Match fs a b
queryMapMatch FNil k       = Void
queryMapMatch (FCons xs) k = foldMap k ::: queryMapMatch xs k

queryAlg :: (Monoid a, Foldables fs) => Algebras fs a
queryAlg = queryMapMatch frep id

emptyQuery :: (Monoid a, Foldables fs) => Fix fs -> a
emptyQuery = fold queryAlg
