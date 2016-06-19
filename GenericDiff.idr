module Main
-- module Diff

import Data.Fin
import Data.Vect

import Pretty

-- Check all subsequent functions for totality by default.
-- Can be applied to individual functions.
%default total
-- %default partial -- relax totality check for subsequent functions

%access public export

infixr 5 >=>, <=<

(>=>) : (Monad m) => (a -> m b) -> (b -> m c) -> (a -> m c)
(>=>) f g = \x => f x >>= g

(<=<) : (Monad m) => (b -> m c) -> (a -> m b) -> (a -> m c)
(<=<) g f = f >=> g

-- Universe for sums of products of types

data TypeIx : (n : Nat) -> Type where
  CTypeIx : Fin n -> TypeIx n

data Con : (n : Nat) -> Type where
  CCon : List (TypeIx n) -> Con n

data Typ : (n : Nat) -> Type where
  CTyp : List (Con n) -> Typ n

data Fam : (n : Nat) -> Type where
  CFam : Vect n (Typ n) -> Fam n

constructors : Typ n -> List (Con n)
constructors (CTyp cs) = cs

-- Vect n (List (List (Fin n)))

namespace SampleTypes
  mutual
    data Expr : Type where
      Add : Expr -> Term -> Expr
      One : Expr
    data Term : Type where
      Neg : Expr -> Term

    exprTyp : Typ 2
    exprTyp = CTyp [CCon [CTypeIx FZ, CTypeIx (FS FZ)], CCon []]

    termTyp : Typ 2
    termTyp = CTyp [CCon [CTypeIx FZ]]

    exprTermFam : Fam 2
    exprTermFam = CFam [exprTyp, termTyp]

data Env : {a : Type} -> (i : a -> Type) -> List a -> Type where
  Nil  : Env i []
  (::) : {code : a} -> {codes : List a} -> i code -> Env i codes -> Env i (code :: codes)

interpCon : {n : Nat} -> Con n -> (TypeIx n -> Type) -> Type
interpCon (CCon fields) i = Env i fields

interpTyp : {n : Nat} -> Typ n -> (TypeIx n -> Type) -> Type
interpTyp (CTyp cs) i =
  DPair (Fin (length cs)) (\conIx => interpCon (index conIx (fromList cs)) i)

getType : {n : Nat} -> Fam n -> TypeIx n -> Typ n
getType (CFam types) (CTypeIx m) = index m types

interpFam : {n : Nat} -> Fam n -> (TypeIx n -> Type) -> TypeIx n -> Type
interpFam types i n = interpTyp (getType types n) i

data Mu : {n : Nat} -> (fam : Fam n) -> (t : TypeIx n) -> Type where
  CMu : interpFam fam (Mu fam) t -> Mu fam t

-- Some values from SampleTypes encoded in the universe
namespace Samples
  one : Mu SampleTypes.exprTermFam (CTypeIx FZ)
  one = CMu (FS FZ ** [])

  negOne : Mu SampleTypes.exprTermFam (CTypeIx (FS FZ))
  negOne = CMu (FZ ** [CMu (FS FZ ** [])])

  addOneNegOne : Mu SampleTypes.exprTermFam (CTypeIx FZ)
  addOneNegOne = CMu (FZ ** [CMu (FS FZ ** []), CMu (FZ ** [CMu (FS FZ ** [])])])

data ConIx : {n : Nat} -> (fam : Fam n) -> (tix : TypeIx n) -> Type where
  CConIx : Fin (Prelude.List.length (constructors (getType fam tix))) -> ConIx fam tix

||| Constructor index paired with the corresponding type index within family.
data Ixs : {n : Nat} -> (fam : Fam n) -> Type where
  -- NB dependent pair
  CIxs : (tix : TypeIx n) -> ConIx fam tix -> Ixs fam

typeIx : {n : Nat} -> {fam : Fam n} -> Ixs fam -> TypeIx n
typeIx (CIxs tix _) = tix

fields : {n : Nat} -> {fam : Fam n} -> Ixs fam -> List (TypeIx n)
fields (CIxs tix (CConIx cix)) =
  case Data.Vect.index cix $ fromList $ constructors $ getType fam tix of
    CCon fs => fs




