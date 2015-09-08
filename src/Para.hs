{-# LANGUAGE
 DataKinds, KindSignatures, GADTs, TypeOperators, RankNTypes,
 DeriveFunctor, DeriveFoldable, DeriveTraversable, StandaloneDeriving,
 MultiParamTypeClasses, FlexibleInstances, FlexibleContexts,
 UndecidableInstances, OverlappingInstances, NoMonomorphismRestriction,
 FunctionalDependencies, ScopedTypeVariables
 #-}

module Para where

import Data.Matches
import Term

{- A reviewer raised the question: in the function "subst",
   is it possible *not* to apply subsitution to the subexpression?

   Here are some demos.
-}

-- Of course, we can always resort to direct recursion,
-- with the help of "match".

subst' :: (fs <: fs, Mem Var fs, Mem Lam fs) => String -> Fix fs -> Fix fs -> Fix fs
subst' v t = match
    ((\(Var w) -> if (v == w) then t else var w)   >::
     (\(Lam w e) ->
       if (v == w) then lam w e
                   else lam w (subst' v t e))  >::
     transAlg)


-- Or, we may use Mendler-style paramorphism. The following
-- mpara follows the pattern sugggested by Varmo's thesis.

mpara :: (forall r . (r -> (a, Fix gs)) -> Matches gs r a) -> Fix gs -> a
mpara ks (In pos xs) = extractAt pos (ks (fork (mpara ks) id)) xs

fork f g x = (f x, g x)

-- Since (r -> (a, Fix gs)) is isomorphic to (r -> a, r -> Fix gs),-- one may also define this alternative,

mpara' :: (forall r . (r -> a, r -> Fix gs) -> Matches gs r a) -> Fix gs -> a
mpara' ks (In pos xs) = extractAt pos (ks (mpara' ks, id)) xs

-- which can be used to define a substitition that does
-- not always apply the "substitute" operation to the
-- subtree:

subst'' :: (fs <: fs, Mem Var fs, Mem Lam fs) => String -> Fix fs -> Fix fs -> Fix fs
subst'' v t = mpara'
    (\(sub, rebuild) ->
       ((\(Var w) -> if (v == w) then t else var w)   >::
        (\(Lam w e) ->
         if (v == w) then lam w (rebuild e)
           else lam w (sub e))  >::
        mTransAlg rebuild ))

mTransAlg :: (fs <: fs) => (r -> Fix fs) -> Matches fs r (Fix fs)
mTransAlg rebuild = transAlg <<^ rebuild
