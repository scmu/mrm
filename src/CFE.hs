{-# LANGUAGE
 DataKinds, KindSignatures, GADTs, TypeOperators, RankNTypes,
 DeriveFunctor, DeriveFoldable, DeriveTraversable,
 MultiParamTypeClasses, FlexibleInstances, FlexibleContexts,
 UndecidableInstances, OverlappingInstances, NoMonomorphismRestriction,
 LambdaCase, StandaloneDeriving, ScopedTypeVariables,
 ViewPatterns, PatternSynonyms
 #-}

module CFE where

import Data.Matches
import Term

cfeAlg1 ::  (Foldables fs, fs <: fs,
             Mem Var fs, Mem App fs, Mem Lam fs, Mem Let fs) =>
            Algebras fs (Fix fs)
cfeAlg1 =  (\(App e1 e2) ->
             if isCF e1 then extractBody e1
                        else app e1 e2) >::
           transAlg
 where extractBody =
        match ((\(Lam x body) -> body) >:: transAlg)
       isCF = match ((\(Lam x body) -> not (x `elem` freeVars body)) >::
                     constMatches False)

cfe1 :: (Foldables fs, Mem Var fs, Mem App fs, Mem Lam fs,
         Mem Let fs, fs <: fs) =>
        Fix fs -> Fix fs
cfe1 = fold cfeAlg1

pattern LamP x body <- (prj -> Just (Lam x body))

cfeAlg2 ::  (Foldables fs, fs <: fs,
             Mem Var fs, Mem App fs, Mem Lam fs, Mem Let fs) =>
            Algebras fs (Fix fs)
cfeAlg2 =  (\case
              App (LamP x body) e2 | x `freeIn` body -> body
              App e1 e2                              -> app e1 e2) >::
           transAlg
  where x `freeIn` body = not (x `elem` freeVars body)

pattern AppP e1 e2 <- (prj -> Just (App e1 e2))

cfe3 :: (Foldables fs, fs <: fs,
         Mem Var fs, Mem App fs, Mem Lam fs, Mem Let fs) =>
        Fix fs -> Fix fs
cfe3 (AppP (LamP x body) e2)
  | x `freeIn` body     = body
  where x `freeIn` body = not (x `elem` freeVars body)
cfe3 (In pos gx)        = In pos (fmap cfe3 gx)

data Anno a x = Anno a x

anno :: Mem (Anno a) fs => a -> Fix fs -> Fix fs
anno a x = inn (Anno a x)

annoAlg :: (Mem (Anno a) gs) =>
           Sub fs gs -> Algebras fs a -> Algebras fs (Fix gs, a)
annoAlg SNil Void = Void
annoAlg (SCons pos ss) (k ::: ks) =
  (\xs -> let y = k (fmap snd xs)
          in (anno y (In pos (fmap fst xs)) , y)) ::: annoAlg ss ks

annotate :: (Mem (Anno a) gs, fs <: gs) =>
            Algebras fs a -> Fix fs -> (Fix gs, a)
annotate ks = fold (annoAlg srep ks)

getData :: (Functors fs) => Fix (Anno a ': fs) -> Fix (Anno a ': fs)
getData xs = match ((\(Anno y zs) -> zs) ::: undefs) xs

getAnno :: (Functors fs, Mem (Anno a) fs) => Fix fs -> a
getAnno xs = match ((\(Anno y xs) -> y) >:: undefs) xs

unannotate :: (fs <: fs) => Fix (Anno a ': fs) -> Fix fs
unannotate = fold unannoAlg
  where unannoAlg = (\(Anno _ xs) -> xs) ::: transAlg

type TermF = '[Var, App, Lam, Let]
type TermAF = Anno [VName] ': TermF
type Term = Fix TermF

pattern AnnoP y zs <- (prj -> Just (Anno y zs))

elim :: Fix (Anno [VName] ': TermF) -> Fix (Anno [VName] ': TermF)
elim (AnnoP (_ :: [VName]) (AppP (AnnoP (_ :: [VName]) (LamP x body)) e2))
  | not (x `elem` getAnno body) = body
elim (In pos xs) = In pos (fmap elim xs)

cfe2 :: Term -> Term
cfe2 = unannotate . elim . fst . annotate fVarsAlg

deriving instance Functor (Anno a)

e0 :: Term
e0 = ((lam "x" (lam "y" (var "z")) `app` var "w") `app` var "k")

e1 :: Term
e1 = (lam "x" (var "y"))

showAlg2 :: Algebras TermAF String
showAlg2 = (\(Anno y xs) -> "(Anno " ++ show y ++ " " ++ xs ++ ")")
    ::: showAlg

showExpr2 = fold showAlg2
