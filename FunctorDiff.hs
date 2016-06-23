{-# LANGUAGE DeriveFoldable       #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module FunctorDiff where

import Control.Arrow (second)
import Data.Foldable
import Data.Function (on)
import Data.List (sortBy)
import Data.Monoid
import Data.Ord (comparing)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TL
import Text.PrettyPrint.Leijen.Text (Pretty(..))
import qualified Text.PrettyPrint.Leijen.Text as PP

newtype Fix f = Fix { unFix :: f (Fix f) }

deriving instance (Show (f (Fix f))) => Show (Fix f)
deriving instance (Eq   (f (Fix f))) => Eq   (Fix f)
deriving instance (Ord  (f (Fix f))) => Ord  (Fix f)

cata :: (Functor f) => (f a -> a) -> Fix f -> a
cata alg = go
  where
    go = alg . fmap go . unFix

size :: forall f. (Functor f, Foldable f, Diff f) => Fix f -> Int
size = getSum . cata alg
  where
    alg :: f (Sum Int) -> Sum Int
    alg e
      | null $ children e = Sum 1
      | otherwise         = fold e

instance (Pretty (f (Fix f))) => Pretty (Fix f) where
  pretty = pretty . unFix

class Diff (f :: * -> *) where
  data Context f :: * -> *
  -- | Get immediate children of a node.
  children :: f a -> [(a, Context f a)]
  plugIn   :: Context f a -> a -> f a
  childAt  :: f a -> Context f b -> Maybe a

data Change f where
  Take :: Context f (Fix f) -> Change f
  Drop :: Context f (Fix f) -> Change f
  -- Replace :: Fix f -> Fix f -> Change f

deriving instance (Show (Context f (Fix f))) => Show (Change f)
deriving instance (Eq (Context f (Fix f)))   => Eq (Change f)
deriving instance (Ord (Context f (Fix f)))  => Ord (Change f)

instance (Pretty (Context f (Fix f))) => Pretty (Change f) where
  pretty (Take x) = pretty x
  pretty (Drop x) = "!" <> pretty x

type Path f = [Change f]

substructures :: forall f. (Diff f) => Fix f -> [(Fix f, Path f)]
substructures = go
  where
    go :: Fix f -> [(Fix f, Path f)]
    go x = case children $ unFix x of
      [] -> [(x, [])]
      cs  ->
        [ s
        | (child, childCtx)           <- cs
        , (grandChild, grandChildCtx) <- substructures child
        , s                           <- [ ( grandChild
                                           , Drop childCtx : grandChildCtx
                                           )
                                         , ( Fix $ plugIn childCtx grandChild
                                           , Take childCtx : grandChildCtx
                                           )
                                         ]
        ]

data Prim = PrimSum | PrimProd
  deriving (Show, Eq, Ord)

data ExprF e =
    Lit Int
  | Var Text
  | Add e e
  | Mul e e
  | Abs e
  | Apply Prim [e]
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

type Expr = Fix ExprF

data LeftRight a = L a | R a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

leftRight :: (a -> b) -> (a -> b) -> LeftRight a -> b
leftRight f _ (L x) = f x
leftRight _ g (R y) = g y

instance Diff ExprF where
  data Context ExprF e =
      CtxAdd (LeftRight e)
    | CtxMul (LeftRight e)
    | CtxAbs
    | CtxApply Prim [e] [e]
    deriving (Show, Eq, Ord, Functor, Foldable, Traversable)
  children = \case
    Lit _      -> []
    Var _      -> []
    Add x y    -> [(x, CtxAdd $ R y), (y, CtxAdd $ L x)]
    Mul x y    -> [(x, CtxMul $ R y), (y, CtxMul $ L x)]
    Abs x      -> [(x, CtxAbs)]
    Apply p xs -> [ (x, CtxApply p ls rs) | (ls, x, rs) <- splits xs ]
  plugIn ctx x = case ctx of
    CtxAdd (L y)     -> Add y x
    CtxAdd (R y)     -> Add x y
    CtxMul (L y)     -> Mul y x
    CtxMul (R y)     -> Mul x y
    CtxAbs           -> Abs x
    CtxApply p ls rs -> Apply p $ ls ++ x : rs
  childAt (Add x y)    (CtxAdd c) = Just $ leftRight (const y) (const x) c
  childAt (Mul x y)    (CtxMul c) = Just $ leftRight (const y) (const x) c
  childAt (Abs x)      CtxAbs     = Just x
  childAt (Apply p xs) (CtxApply p' ls rs)
    | p == p'
    , lsLen + length rs + 1 == length xs
    , x : _ <- drop lsLen xs
    = Just x
    where
      lsLen = length ls
  childAt _ _ = Nothing

-- | Split list into triple of prefix, element and suffix
splits :: forall a. [a] -> [([a], a, [a])]
splits []     = []
splits (x:xs) = go [] x xs
  where
    go :: [a] -> a -> [a] -> [([a], a, [a])]
    go prefix x suffix = (reverse prefix, x, suffix) : rest
      where
        rest = case suffix of
                 []     -> []
                 y : ys -> go (x : prefix) y ys

common :: forall a b. (Ord a) => [(a, b)] -> [(a, b)] -> [(b, b)]
common xs ys = go (order xs) (order ys)
  where
    order = sortBy (comparing fst)

    go :: [(a, b)] -> [(a, b)] -> [(b, b)]
    go []                 _                  = []
    go _                  []                 = []
    go xs'@((x, x') : xs) ys'@((y, y') : ys) =
      case compare x y of
        EQ -> (x', y') : go xs ys
        LT -> go xs ys'
        GT -> go xs' ys

takes :: Path f -> Path f
takes = filter (\case { Take{}  -> True; Drop{} -> False })

largest :: [(Path f, Path f)] -> (Path f, Path f)
largest = maximumBy $ comparing $ \(x, y) -> length (takes x) + length (takes y)

diff :: (Diff f, Ord (f (Fix f))) => Fix f -> Fix f -> (Path f, Path f)
diff old new = largest $ (common `on` substructures) old new

-- Ghci stuff

instance Pretty Prim where
  pretty = \case
    PrimSum  -> "sum"
    PrimProd -> "prod"

instance (Pretty e) => Pretty (ExprF e) where
  pretty = \case
    Lit n        -> PP.int n
    Var v        -> pretty v
    Add x y      -> pretty x PP.<+> "+" PP.<+> pretty y
    Mul x y      -> pretty x PP.<+> "*" PP.<+> pretty y
    Abs x        -> "|" <> pretty x <> "|"
    Apply p args ->
      pretty p <> PP.parens (PP.sep $ PP.punctuate "," $ map pretty args)

-- newtype Marker a = Marker a
--
-- instance (Pretty a) => Pretty (Marker a) where
--   pretty (Marker x) = ">" <> pretty x <> "<"

instance (Pretty a) => Pretty (Context ExprF a) where
  pretty ctx = pretty $ plugIn (pretty <$> ctx) "_"

sampleExpr :: Expr
sampleExpr =
  Fix $ Apply PrimSum
    [ Fix $ Add (Fix (Var "x")) (Fix (Lit 1))
    , Fix $ Mul (Fix (Var "x")) (Fix (Var "x"))
    ]

test :: IO ()
test = do
  let xs = sortBy (comparing (size . fst)) $ substructures sampleExpr
  mapM_ (\(x, y) -> TL.putStrLn $ display $ pretty x PP.<+> pretty y) xs

sampleExpr' :: Expr
sampleExpr' =
  Fix $ Apply PrimSum
    [ Fix $ Add (Fix (Var "y")) (Fix (Lit 1))
    , Fix $ Add (Fix (Var "y")) (Fix (Var "y"))
    ]

testDiff :: IO ()
testDiff = do
  let (x, y) = diff sampleExpr sampleExpr'
  TL.putStrLn $ display $ pretty x PP.</> pretty y

main :: IO ()
main = putStrLn "OK"

-- Utils

display :: (Pretty a) => a -> Text
display = PP.displayT . PP.renderPretty 0.8 100 . pretty

