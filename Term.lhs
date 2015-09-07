> {-# LANGUAGE
>  DataKinds, KindSignatures, GADTs, TypeOperators, RankNTypes,
>  DeriveFunctor, DeriveFoldable, DeriveTraversable,
>  MultiParamTypeClasses, FlexibleInstances, FlexibleContexts,
>  UndecidableInstances, OverlappingInstances, NoMonomorphismRestriction, LambdaCase, StandaloneDeriving
>  #-}

> module MRM.Term where

> import Data.Foldable hiding (fold, elem)
> import Data.Traversable 
> import Control.Monad (MonadPlus(..), liftM, mzero)
> import Control.Monad.Reader (runReaderT)
> import Control.Monad.Reader.Class

> import MRM.Infrastructure
> import MRM.Query 
> import MRM.Monadic

> type VName = String

> data Var x  = Var VName     
> data App x  = App x x
> data Lam x  = Lam VName x
> data Let x  = Let VName x x 

> type ExprFunctors = '[Var, Let, Lam, App]

> var   :: Mem Var fs => VName -> Fix fs
> var = In witness . Var
>
> app   :: Mem App fs => Fix fs -> Fix fs -> Fix fs
> app e1 e2 = In witness $ App e1 e2
>
> lam   :: Mem Lam fs => VName -> Fix fs -> Fix fs
> lam x e = In witness $ Lam x e
>
> lett  :: Mem Let fs => VName -> Fix fs -> Fix fs -> Fix fs
> lett x e1 e2 = In witness $ Let x e1 e2

> type Expr = Fix ExprFunctors



> renameAlg ::  (fs <: gs, Mem Var fs, Mem Var gs) =>
>               Algebras fs (Fix gs)
> renameAlg = (\(Var s) -> var (s ++ "_")) >:: transAlg

> rename :: (fs <: fs, Mem Var fs) => Fix fs -> Fix fs
> rename = fold renameAlg



> desugarAlg ::  (fs <: gs, Mem App gs, Mem Lam gs) =>
>                Algebras (Let :- fs) (Fix gs)
> desugarAlg =  (\(Let x e1 e2) -> app (lam x e2) e1) :::
>               transAlg

> desugar ::  (fs <: fs, Mem App fs, Mem Lam fs) => 
>             Fix (Let :- fs) -> Fix fs
> desugar = fold desugarAlg



> substMatch :: (fs <: fs, Mem Var fs, Mem Lam fs) =>
>   String -> Fix fs -> Matches fs (Fix fs, Fix fs) (Fix fs)
> substMatch v t =
>   (\(Var w)    -> if (v == w) then t else var w)   >::
>   (\(Lam w (e',e)) -> 
>     if (v == w) then lam w e else lam w e')  >::
>   transAlg <<^ fst

> subst ::  (fs <: fs, Mem Var fs, Mem Lam fs) =>
>           String -> Fix fs -> Fix fs -> Fix fs
> subst v t = para (substMatch v t)




> fVarsAlg :: (Foldables fs, Mem Var fs, Mem Lam fs, Mem Let fs) =>
>   Algebras fs [VName]
> fVarsAlg =  (\(Var x) -> [x]) >::
>             (\(Lam x vs) -> vs `setminus` x) >::
>             (\(Let x vs ws) -> (vs ++ ws) `setminus` x) >::
>             queryAlg
>   where xs `setminus` x = filter (not . (x==)) xs 

> freeVars :: (Foldables fs, Mem Lam fs, Mem Var fs, Mem Let fs) =>
>   Fix fs -> [VName]
> freeVars = fold fVarsAlg



> data Lam' x = Lam' x

> lam' :: Mem Lam' fs => Fix fs -> Fix fs
> lam' e = In witness $ Lam' e


> deBruijn ::  (  MonadReader [VName] m, fs <: gs, 
>                 Mem Lam fs, Mem Var fs, Traversables fs,
>                 Mem Lam' gs, Mem Var gs) =>
>              Fix fs -> m (Fix gs)
> deBruijn = fold deBruijnAlg where
>   deBruijnAlg =
>         (\(Lam v e) -> liftM lam' (local (v:) e)) >::
>         (\(Var v) -> do  env <- ask
>                          case position v env of
>                            Nothing -> return (var v)
>                            Just i -> return (var (numId i))) >::
>         transMAlg
>   numId :: Int -> VName
>   numId n = "_" ++ show n

> position :: Eq a => a -> [a] -> Maybe Int
> position x [] = Nothing
> position x (y:xs) | x == y = Just 0
>                   | otherwise = fmap (1+) (position x xs)



> showAlg :: (fs <: '[Lam, Var, Let, App]) => Algebras fs String
> showAlg = subMatches $
>  (\(Lam x e) -> "(\\" ++ x ++ " -> " ++ e ++")") :::
>  (\(Var x) -> x) :::
>  (\(Let x e1 e2) -> 
>            "(let " ++ x ++ " = " ++ e1 ++ 
>            " in " ++ e2 ++ ")") :::
>  (\(App e1 e2) -> "(" ++ e1 ++ " @ " ++ e2 ++ ")") ::: Void

> showExpr = fold showAlg



> deriving instance Show x => Show (Lam x)
> deriving instance Show x => Show (Var x)
> deriving instance Show x => Show (Let x)
> deriving instance Show x => Show (App x)

> deriving instance Functor Lam
> deriving instance Functor Var
> deriving instance Functor Let
> deriving instance Functor App

> deriving instance Foldable Lam
> deriving instance Foldable Var
> deriving instance Foldable Let
> deriving instance Foldable App

> deriving instance Traversable Lam
> deriving instance Traversable Var
> deriving instance Traversable Let
> deriving instance Traversable App

> deriving instance Show x => Show (Lam' x)
> deriving instance Traversable Lam'
> deriving instance Functor Lam'
> deriving instance Foldable Lam'