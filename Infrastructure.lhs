> {-# LANGUAGE
>  DataKinds, KindSignatures, GADTs, TypeOperators, RankNTypes,
>  DeriveFunctor, DeriveFoldable, DeriveTraversable, StandaloneDeriving,
>  MultiParamTypeClasses, FlexibleInstances, FlexibleContexts,
>  UndecidableInstances, OverlappingInstances, NoMonomorphismRestriction, 
>  FunctionalDependencies, ScopedTypeVariables
>  #-}

> module MRM.Infrastructure 
>        (Fix(In), Elem(..), Mem(..), (:-), inn, inns,
>         Matches((:::), Void), Algebras, extractAt, match,
>         overrideAt, (>::), prj, fold, para,
>         undefs, generateMatches, generateMatches',
>         generateMatches2, constMatches,
>         Sub(..), (<:)(..), refl, subSub,
>         subFix, transAlg', transAlg,
>         subOp, subMatches', subMatches,
>         (<<^), (^<<), (&&&), Union(..),
>         FList(..), Functors(..), FFList(..), Foldables(..),
>         TList(..), Traversables(..),
>         module MRM.FListProps) where

> import Data.Foldable hiding (fold, elem)
> import Data.Traversable

> import MRM.FListProps

> type (f :: * -> *) :- (fs :: [* -> *]) = f ': fs

> infixr 6 :-



> data Fix (fs :: [* -> *]) where
>   In :: Functor f => Elem f fs -> f (Fix fs) -> Fix fs

> data Elem (f :: * -> *) (fs :: [* -> *]) where
>   Here   :: Elem f (f :- fs)
>   There  :: Elem f fs -> Elem f (g :- fs)

> class Mem f fs where
>   witness :: Elem f fs
> instance Mem f (f :- fs) where
>   witness = Here
> instance (Mem f fs) => Mem f (g :- fs) where
>   witness = There witness

> inn :: (Mem f fs, Functor f) => f (Fix fs) -> Fix fs
> inn = In witness



> data Matches (fs :: [* -> *]) (a :: *) (b :: *) where
>   Void   :: Matches '[] a b
>   (:::)  :: Functor f => (f a -> b) -> Matches fs a b  
>                                     -> Matches (f :- fs) a b
> infixr 6 :::

> extractAt :: Elem f fs -> Matches fs a b -> (f a -> b)
> extractAt  Here         (f :::  _)  = f
> extractAt  (There pos)  (_ ::: fs)  = extractAt pos fs

> match :: Matches fs (Fix fs) b -> Fix fs -> b
> match fs (In pos xs) = extractAt pos fs xs

> overrideAt ::  Elem f fs -> (f a -> b) ->
>                  Matches fs a b -> Matches fs a b
> overrideAt Here        g (_ ::: fs) = g ::: fs
> overrideAt (There pos) g (f ::: fs) = f ::: overrideAt pos g fs

> (>::) :: Mem f fs =>  (f a -> b) ->
>                         Matches fs a b -> Matches fs a b
> (>::) = overrideAt witness

> prj :: (fs <: fs, Mem f fs) => Fix fs -> Maybe (f (Fix fs))
> prj = match (Just >:: constMatches Nothing)

> infixr 6 >::

> undefs' :: FList fs -> Matches fs a b
> undefs' FNil = Void
> undefs' (FCons xs) = undefined ::: undefs' xs

> undefs :: Functors fs => Matches fs a b
> undefs = undefs' frep

> generateMatches' :: (forall f. Functor f => Elem f fs -> f a -> b) ->
>                     Sub gs fs -> Matches gs a b
> generateMatches' f SNil = Void
> generateMatches' f (SCons pos ss) = f pos ::: generateMatches' f ss

> generateMatches :: (fs <: fs) =>
>                    (forall f. Functor f => Elem f fs -> f a -> b) ->
>                    Matches fs a b
> generateMatches f = generateMatches' f srep

> constMatches :: (fs <: fs) => b -> Matches fs a b
> constMatches y = generateMatches (\_ _ -> y)

> generateMatches2 :: (forall f. Functor f => f a -> b) ->
>                FList fs -> Matches fs a b
> generateMatches2 f FNil = Void
> generateMatches2 f (FCons ss) = f ::: generateMatches2 f ss

> constMatches2 :: Functors fs => b -> Matches fs a b
> constMatches2 y = generateMatches2 (\_ -> y) frep



> type Algebras fs a = Matches fs a a

> fold :: Algebras fs a -> Fix fs -> a
> fold ks (In pos xs) = extractAt pos ks (fmap (fold ks) xs)

> para :: (fs <: fs) => Matches fs (a, Fix fs) a -> Fix fs -> a
> para ks = fst . fold (ks &&& (inns <<^ snd))



> mfold :: (forall r. (r -> a) -> Matches gs r a) -> Fix gs -> a
> mfold f (In pos xs) = extractAt pos (f (mfold f)) xs



> data Sub (fs :: [* -> *]) (gs :: [* -> *]) where
>   SNil   ::  Sub '[] gs
>   SCons  ::  (Functor f) =>
>              Elem f gs -> Sub fs' gs -> Sub (f :- fs') gs

> class fs <: gs where
>   srep :: Sub fs gs
> infix 5 <:

> instance '[] <: gs where
>   srep = SNil

> instance  (Functor f, Mem f gs, fs <: gs) => 
>           (f :- fs) <: gs where
>   srep = SCons witness srep

> refl :: FList fs -> Sub fs fs
> refl FNil       = SNil
> refl (FCons xs) = SCons Here (subSub (refl xs))

> subSub :: Sub fs gs -> Sub fs (g :- gs)
> subSub SNil            = SNil
> subSub (SCons pos ss)  = SCons (There pos) (subSub ss)



> subFix :: (fs <: gs) => Fix fs -> Fix gs
> subFix = fold transAlg

> transAlg' :: Sub fs gs -> Algebras fs (Fix gs)
> transAlg' SNil            = Void
> transAlg' (SCons pos xs)  = In pos ::: transAlg' xs
>
> transAlg :: (fs <: gs) => Algebras fs (Fix gs)
> transAlg = transAlg' srep

> inns :: (fs <: fs) => Algebras fs (Fix fs)
> inns = transAlg

> subOp :: (fs <: gs) => (Fix gs -> c) -> Fix fs -> c 
> subOp f = f . subFix 

> subMatches' :: Sub fs gs -> Matches gs r a -> Matches fs r a
> subMatches' SNil            _   = Void
> subMatches' (SCons pos xs)  as  = extractAt pos as ::: subMatches' xs as
>
> subMatches :: (fs <: gs) => Matches gs r a -> Matches fs r a
> subMatches = subMatches' srep



> (<<^) :: Matches fs b c -> (a -> b) -> Matches fs a c
> Void <<^ g        = Void
> (h ::: hs) <<^ g  = h . fmap g ::: hs <<^ g

> (^<<) :: (b -> c) -> Matches fs a b -> Matches fs a c
> g ^<< Void        = Void
> g ^<< (h ::: hs)  = g . h ::: g ^<< hs

> instance Functor (Matches fs a) where
>   fmap = (^<<)

> infixr 7 <<^, ^<<

> (&&&) ::  Matches fs a b -> Matches fs a c 
>           -> Matches fs a (b,c)
> Void &&& Void = Void
> (h ::: hs) &&& (k ::: ks) = (\x -> (h x, k x)) ::: (hs &&& ks)

> infixr 5 &&&

> class Union fs gs hs | fs gs -> hs where
>  union ::  Matches fs a b -> Matches gs a b -> 
>              Matches hs a b

> instance Union '[] gs gs where
>  union Void hs = hs

> instance Union fs gs hs => Union (f :- fs) gs (f :- hs) where
>   union (k ::: ks) ws = k ::: union ks ws
