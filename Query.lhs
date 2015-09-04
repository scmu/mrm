> {-# LANGUAGE
>  DataKinds, KindSignatures, GADTs, TypeOperators, RankNTypes,
>  DeriveFunctor, DeriveFoldable, DeriveTraversable,
>  MultiParamTypeClasses, FlexibleInstances, FlexibleContexts,
>  UndecidableInstances, OverlappingInstances, NoMonomorphismRestriction, LambdaCase, StandaloneDeriving
>  #-}

> module MRM.Query where

> import Data.Foldable hiding (fold, elem)
> import Data.Monoid

> import MRM.Infrastructure

> queryMapMatch :: Monoid b => 
>  FFList fs -> (a -> b) -> Matches fs a b
> queryMapMatch FFNil k        = Void
> queryMapMatch (FFCons xs) k  = foldMap k ::: queryMapMatch xs k

> queryAlg :: (Monoid a, Foldables fs) => Algebras fs a
> queryAlg = queryMapMatch ffrep id

> emptyQuery :: (Monoid a, Foldables fs) => Fix fs -> a
> emptyQuery = fold queryAlg