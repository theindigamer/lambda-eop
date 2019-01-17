{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}

module Eop where

import Bound
import Bound.Name

import Data.Coerce
import Control.Monad
import Data.Bifunctor
import Data.Bifoldable

bimapInScope :: Bifunctor p => (a -> c) -> (b -> d) -> Scope z (p a) b -> Scope z (p c) d
bimapInScope f g = Scope . bimap f (second (bimap f g)) . unscope

bifoldMapInScope :: (Bifoldable p, Monoid m) => (a -> m) -> (b -> m) -> Scope z (p a) b -> m
bifoldMapInScope f g = bifoldMap f (foldMap (bifoldMap f g)) . unscope

data BinOp = Plus | Times

-- Program variables x
-- Source expressions
-- e ::= () | x | u | λx. e | e 1 @ e 2 | fix u. e
--   | Λα. e | e[τ] | (e:τ)
--   | (e 1 , e 2 ) | proj k e
--   | inj k e | case(e, x 1 .e 1 , x 2 .e 2 )
data Exp o t e
  = EUnit
  | EInt !Int
  | EBin !BinOp (Exp o t e) (Exp o t e)
  | EVar e
  | EFixVar e
  | ELam (Scope () (Exp o t) e)
  | EApp (Exp o t e) (Exp o t e)
  | EFix (Scope () (Exp o t) e)
  | ETyLam (Scope () (Exp' o e) t)
  | ETyApp (Exp o t e) (Type o t)

newtype Exp' o e t = Exp' { getExp :: Exp o t e }

instance Functor (Exp o t) where
  fmap = second

instance Bifunctor (Exp o) where
  bimap :: (t -> s) -> (a -> b) -> Exp o t a -> Exp o s b
  bimap f g = \case
    EUnit -> EUnit
    EInt i -> EInt i
    EBin b e1 e2 -> EBin b (bimap f g e1) (bimap f g e2)
    EVar e -> EVar (g e)
    EFixVar e -> EFixVar (g e)
    ELam s -> ELam (bimapInScope f g s)
    EApp e1 e2 -> EApp (bimap f g e1) (bimap f g e2)
    EFix s -> EFix (bimapInScope f g s)
    ETyLam s -> ETyLam (bimapInScope g f s)
    ETyApp e t -> ETyApp (bimap f g e) (fmap f t)

instance Foldable (Exp o t) where
  foldMap = bifoldMap (const mempty)

instance Bifoldable (Exp o) where
  bifoldMap f g = \case
    EUnit -> mempty
    EInt _ -> mempty
    EBin _ e1 e2 -> bifoldMap f g e1 <> bifoldMap f g e2
    EVar e -> g e
    EFixVar e -> g e
    ELam s -> bifoldMapInScope f g s
    EApp e1 e2 -> bifoldMap f g e1 <> bifoldMap f g e2
    EFix s -> bifoldMapInScope f g s
    ETyLam s -> bifoldMapInScope g f s
    ETyApp e t -> bifoldMap f g e <> foldMap f t

instance Applicative (Exp o t) where
  pure = EVar
  (<*>) = ap

co :: Exp' o a (Var () (Exp' o a t)) -> Exp o (Var () (Exp o t a)) a
co = first coerce . coerce

instance Monad (Exp o t) where
  (>>=) x f = case x of
    EUnit -> EUnit
    EInt i -> EInt i
    EBin b e1 e2 -> EBin b (e1 >>= f) (e2 >>= f)
    EVar e -> f e
    EFixVar e -> f e
    ELam s -> ELam (s >>>= f)
    EApp e1 e2 -> EApp (e1 >>= f) (e2 >>= f)
    EFix s ->
      let tmp = unscope s in
      EFix (s >>>= f)
    ETyLam s ->
      -- a -> Exp o t b
      -- a -> Exp o (Var () (Exp' o a)) b
      let tmp' = first (second (f =<<)) $ co (unscope s)
          tmp = Exp' $ first (second (Exp' . (f =<<) . getExp)) $ getExp (unscope s) -- >>= f
      in undefined
    ETyApp e t -> ETyApp (e >>= f) t

instance Bifunctor (Exp' o) where
  bimap f g = Exp' . bimap g f . getExp

instance Foldable (Exp' o e) where
  foldMap = bifoldMap (const mempty)

instance Bifoldable (Exp' o) where
  bifoldMap f g = bifoldMap g f . getExp

-- Evaluation order vars. a
-- Evaluation orders      ε ::= V | N | a
data Evo o = EvoV | EvoN | EvoVar o
  deriving (Functor, Foldable, Traversable)

-- Type variables         α
-- Valuenesses            φ ::= val | Top
-- Source types           τ ::= 1 | α | ∀α. τ | Д a . τ | τ1 -ε-> τ2
data Type o t
  = TUnit
  | TInt
  | TVar t
  | TForall (Scope () (Type o) t)
  | TForallEvo (Scope () (Type' t) o)
  | TFun (Type o t) (Evo o) (Type o t)
  | TSum (Type o t) (Evo o) (Type o t)
  | TProd (Type o t) (Evo o) (Type o t)
  | TFix (Evo o) (Scope () (Type o) t)

newtype Type' t o = Type' { getType :: Type o t }

instance Functor (Type o) where
  fmap = second

instance Bifunctor Type where
  bimap f g = \case
    TUnit -> TUnit
    TInt -> TInt
    TVar t -> TVar (g t)
    TForall s -> TForall (bimapInScope f g s)
    TForallEvo s -> TForallEvo (bimapInScope g f s)
    TFun t1 eo t2 -> TFun (bimap f g t1) (fmap f eo) (bimap f g t2)
    TSum t1 eo t2 -> TSum (bimap f g t1) (fmap f eo) (bimap f g t2)
    TProd t1 eo t2 -> TProd (bimap f g t1) (fmap f eo) (bimap f g t2)
    TFix eo s -> TFix (fmap f eo) (bimapInScope f g s)

instance Foldable (Type o) where
  foldMap = bifoldMap (const mempty)

instance Bifoldable Type where
  bifoldMap f g = \case
    TUnit -> mempty
    TInt -> mempty
    TVar t -> g t
    TForall s -> bifoldMapInScope f g s
    TForallEvo s -> bifoldMapInScope g f s
    TFun t1 eo t2 -> bifoldMap f g t1 <> foldMap f eo <> bifoldMap f g t2
    TSum t1 eo t2 -> bifoldMap f g t1 <> foldMap f eo <> bifoldMap f g t2
    TProd t1 eo t2 -> bifoldMap f g t1 <> foldMap f eo <> bifoldMap f g t2
    TFix eo s -> foldMap f eo <> bifoldMapInScope f g s

instance Bifunctor Type' where
  bimap f g = Type' . bimap g f . getType

instance Bifoldable Type' where
  bifoldMap f g = bifoldMap g f . getType
