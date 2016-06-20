----------------------------------------------------------------------------
-- |
-- Module      :  SexpDiff
-- Copyright   :  (c) Sergey Vinokurov 2016
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Created     :  Sunday, 19 June 2016
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE DeriveFoldable       #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TupleSections        #-}
{-# LANGUAGE UndecidableInstances #-}

module SexpDiff where

import Control.Arrow
import Control.Monad.State
import Data.Bifunctor
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as M
import Data.Monoid
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TL
-- import Data.Vector (Vector)
-- import qualified Data.Vector as V
import Text.PrettyPrint.Leijen.Text (Pretty(..))
import qualified Text.PrettyPrint.Leijen.Text as PP

data Wildcard = Wildcard
  deriving (Show, Eq, Ord)

instance Pretty Wildcard where
  pretty _ = "_"

data SexpF e =
    Num Int
  | Double Double
  | Symbol Text
  | String Text
  | Nil
  | Cons e e
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

consSpine :: Sexp -> Maybe [Sexp]
consSpine (Fix (Cons x xs)) = (x :) <$> consSpine xs
consSpine (Fix Nil)         = return []
consSpine _                 = Nothing

instance {-# OVERLAPS #-} Pretty (Fix SexpF) where
  pretty = \case
    Fix (Num n)            -> PP.int n
    Fix (Double x)         -> PP.double x
    Fix (Symbol s)         -> PP.text s
    Fix (String s)         -> PP.dquotes $ PP.text $ TL.pack $ show $ TL.unpack s
    Fix Nil                -> "()"
    Fix (Cons x (Fix Nil)) -> PP.parens $ pretty x
    Fix (Cons x xs)        ->
      PP.parens $ pretty x PP.<+> tail
      where
        tail =
          case consSpine xs of
            Just xs' -> PP.align (PP.sep $ map pretty xs')
            Nothing  -> "." PP.<+> pretty xs

instance (Pretty e) => Pretty (SexpF e) where
  pretty = \case
    Num n    -> PP.int n
    Double x -> PP.double x
    Symbol s -> PP.text s
    String s -> PP.dquotes $ PP.text $ TL.pack $ show $ TL.unpack s
    Nil      -> "()"
    Cons x y -> PP.parens $ pretty x PP.<+> "." PP.<+> pretty y

-- data SexpF e =
--     Num Int
--   | Double Double
--   | Symbol Text
--   | String Text
--   | List [e]
--   | Vector [e]
--   deriving (Show, Eq, Ord, Functor)
--
-- instance (Pretty e) => Pretty (SexpF e) where
--   pretty (Num n)         = PP.int n
--   pretty (Double x)      = PP.double x
--   pretty (Symbol s)      = PP.text s
--   pretty (String s)      = PP.dquotes $ PP.text $ TL.pack $ show $ TL.unpack s
--   pretty (List [])       = "()"
--   pretty (List [x])      = PP.parens $ pretty x
--   pretty (List (x:xs))   = PP.parens $ pretty x PP.<+> PP.align (PP.sep $ map pretty xs)
--   pretty (Vector [])     = "[]"
--   pretty (Vector [x])    = PP.brackets $ pretty x
--   pretty (Vector (x:xs)) = PP.brackets $ pretty x PP.<+> PP.align (PP.sep $ map pretty xs)

-- | DiffF that starts from the string end and grows to the beginning.
data DiffF a e where
  Ins :: a -> e -> DiffF a e
  Del :: a -> e -> DiffF a e
  Cpy :: a -> e -> DiffF a e
  Mod :: a -> a -> e -> DiffF a e
  End :: DiffF a e

deriving instance (Show a, Show e) => Show (DiffF a e)
deriving instance Functor (DiffF a)
deriving instance Foldable (DiffF a)
deriving instance Traversable (DiffF a)

instance (Pretty a, Pretty e) => Pretty (DiffF a e) where
  pretty (Ins x d)   = "+" <> pretty x <> pretty d
  pretty (Del x d)   = "-" <> pretty x <> pretty d
  pretty (Cpy x d)   = "=" <> pretty x <> pretty d
  pretty (Mod x y d) = "/" <> pretty x <> "/" <> pretty y <> "/" <> pretty d
  pretty End         = mempty

-- | DiffF that starts from the string beginning and grows to the end.
data RevDiffF a e where
  RevIns :: a -> e -> RevDiffF a e
  RevDel :: a -> e -> RevDiffF a e
  RevCpy :: a -> e -> RevDiffF a e
  RevMod :: a -> a -> e -> RevDiffF a e
  RevEnd :: RevDiffF a e

deriving instance (Show a, Show e) => Show (RevDiffF a e)
deriving instance Functor (RevDiffF a)
deriving instance Foldable (RevDiffF a)
deriving instance Traversable (RevDiffF a)

instance (Pretty a, Pretty e) => Pretty (RevDiffF a e) where
  pretty (RevIns x d)   = pretty d <> "+" <> pretty x
  pretty (RevDel x d)   = pretty d <> "-" <> pretty x
  pretty (RevCpy x d)   = pretty d <> "=" <> pretty x
  pretty (RevMod x y d) = pretty d <> "/" <> pretty x <> "/" <> pretty y <> "/"
  pretty RevEnd         = mempty

unRevDiff :: forall a. RevDiff a -> Diff a
unRevDiff d = go d (Fix End)
  where
    go :: RevDiff a -> Diff a -> Diff a
    go (Fix (RevIns x d)) acc   = go d $ Fix $ Ins x acc
    go (Fix (RevDel x d)) acc   = go d $ Fix $ Del x acc
    go (Fix (RevCpy x d)) acc   = go d $ Fix $ Cpy x acc
    go (Fix (RevMod x y d)) acc = go d $ Fix $ Mod x y acc
    go (Fix RevEnd) acc         = acc

newtype C f g a = C { unC :: f (g a) }
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance (Pretty (f (g a))) => Pretty (C f g a) where
  pretty (C x) = pretty x

newtype Fix f = Fix { unFix :: f (Fix f) }

deriving instance (Eq (f (Fix f)))   => Eq (Fix f)
deriving instance (Ord (f (Fix f)))  => Ord (Fix f)
deriving instance (Show (f (Fix f))) => Show (Fix f)

cata :: (Functor f) => (f a -> a) -> Fix f -> a
cata alg = go
  where
    go = alg . fmap go . unFix

cataM :: (Traversable f, Monad m) => (f a -> m a) -> Fix f -> m a
cataM alg = go
  where
    go = alg <=< traverse go . unFix

para :: (Functor f) => (f (a, Fix f) -> a) -> Fix f -> a
para alg = go
  where
    go = alg . fmap (go &&& id) . unFix

paraM :: (Traversable f, Monad m) => (f (a, Fix f) -> m a) -> Fix f -> m a
paraM alg = go
  where
    go = alg <=< traverse (\x -> (,x) <$> go x) . unFix

type Sexp      = Fix SexpF
type Diff a    = Fix (DiffF a)
type RevDiff a = Fix (RevDiffF a)

data TreeF a b e = Node
  { payload    :: a
  , identifier :: b
  , children   :: [e]
  } deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance (Pretty a, Pretty b, Pretty e) => Pretty (TreeF a b e) where
  pretty Node {payload, identifier, children} =
    pretty payload <> "!" <> pretty identifier PP.<$>
      PP.indent 2 (PP.vsep $ map pretty children)

type Tree a = Fix (TreeF a ())

instance Bifunctor (TreeF a) where
  bimap f g (Node x y zs) = Node x (f y) (g <$> zs)

mapPayload :: (a -> b) -> TreeF a c e -> TreeF b c e
mapPayload f t = t { payload = f $ payload t }

data TreeDiff a where
  TreeIns :: a -> Int -> TreeDiff a -> TreeDiff a
  TreeDel :: a -> Int -> TreeDiff a -> TreeDiff a
  TreeCpy :: a -> Int -> TreeDiff a -> TreeDiff a
  -- TreeMod :: a -> a -> Int -> TreeDiff a -> TreeDiff a
  TreeEnd :: TreeDiff a

deriving instance (Show a) => Show (TreeDiff a)

class Cost a where
  cost :: a -> Int

instance Cost (TreeDiff a) where
  cost = go 0
    where
      go !acc = \case
        TreeIns _ _ d -> go (1 + acc) d
        TreeDel _ _ d -> go (1 + acc) d
        TreeCpy _ _ d -> go acc d
        TreeEnd       -> acc

minCost :: (Cost a) => a -> a -> a
minCost x y
  | cost x <= cost y = x
  | otherwise        = y

data EnumState a = EnumState
  { freeIndex   :: !Int
  , cachedTrees :: Map (TreeF a () Int) (Fix (TreeF a Int))
  } deriving (Show, Eq, Ord)

enumerateTree :: forall a. (Ord a) => Tree a -> Fix (TreeF a Int)
enumerateTree = flip evalState emptyState . cataM alg
  where
    emptyState :: EnumState a
    emptyState = EnumState
      { freeIndex   = 0
      , cachedTrees = mempty
      }
    alg :: TreeF a () (Fix (TreeF a Int))
        -> State (EnumState a) (Fix (TreeF a Int))
    alg tree = do
      res <- gets $ M.lookup key . cachedTrees
      case res of
        Just t  -> return t
        Nothing -> do
          idx <- gets freeIndex
          let tree' = Fix $ tree { identifier = idx }
          modify $ \s -> s
            { freeIndex   = idx + 1
            , cachedTrees = M.insert key tree' $ cachedTrees s
            }
          return tree'
      where
        key :: TreeF a () Int
        key = identifier . unFix <$> tree

sampleSexp :: Sexp
sampleSexp =
  Fix (Cons fooPair (Fix (Cons fooPair (Fix Nil))))
  where
    fooSym = Fix (Symbol "foo")
    fooPair =
      Fix (Cons
            fooSym
            (Fix (Cons
                   fooSym
                   (Fix Nil))))

diffTrees :: forall a. (Ord a) => [Tree a] -> [Tree a] -> TreeDiff a
diffTrees xs ys = go xs ys
  where
    go :: (Ord b) => [Fix (TreeF a b)] -> [Fix (TreeF a b)] -> TreeDiff a
    go        []                               []                        = TreeEnd
    go        []                               (Fix (Node y _ ys) : ys') = TreeIns y (length ys) $ go [] (ys ++ ys')
    go        (Fix (Node x _ xs) : xs')        []                        = TreeDel x (length xs) $ go (xs ++ xs') []
    go xsFull@(Fix (Node x _ xs) : xs') ysFull@(Fix (Node y _ ys) : ys')
      | x == y && xsLen == ysLen = cpyDiff
      | otherwise                = best2
      where
        xsLen = length xs
        ysLen = length ys
        best2 = minCost
                  (TreeIns y ysLen $ go xsFull      (ys ++ ys'))
                  (TreeDel x xsLen $ go (xs ++ xs') ysFull)
        cpyDiff = TreeCpy x xsLen $ go (xs ++ xs') (ys ++ ys')
        -- best3 = minCost cpyDiff best2

type SexpTree = Tree (SexpF Wildcard)

sexpTree :: Sexp -> SexpTree
sexpTree = cata alg
  where
    alg :: SexpF SexpTree -> SexpTree
    alg = \case
      Num n    -> Fix $ Node (Num n) () []
      Double x -> Fix $ Node (Double x) () []
      Symbol s -> Fix $ Node (Symbol s) () []
      String s -> Fix $ Node (String s) () []
      Nil      -> Fix $ Node Nil () []
      Cons x y -> Fix $ Node (Cons Wildcard Wildcard) () [x, y]

diffSexpNaive :: Sexp -> Sexp -> TreeDiff (SexpF Wildcard)
diffSexpNaive x y = diffTrees [sexpTree x] [sexpTree y]

data Mod c a =
    ModChanged (c a)
  | ModCpy a
  | ModEnd
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

onChanged :: (forall a. c a -> c' a) -> Mod c a -> Mod c' a
onChanged f (ModChanged x) = ModChanged $ f x
onChanged _ (ModCpy x)     = ModCpy x
onChanged _ ModEnd         = ModEnd

data ModIns a = ModIns a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance (Pretty a) => Pretty (ModIns a) where
  pretty = \case
    ModIns x -> "+" <> pretty x

data ModDel a = ModDel a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance (Pretty a) => Pretty (ModDel a) where
  pretty = \case
    ModDel x -> "-" <> pretty x

data ModChange a =
    ModInsert a
  | ModDelete a
  | ModChange a a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance (Pretty a, Pretty (c a)) => Pretty (Mod c a) where
  pretty = \case
    ModChanged x -> pretty x
    ModCpy x     -> pretty x
    ModEnd       -> "END"

instance (Pretty a) => Pretty (ModChange a) where
  pretty = \case
    ModInsert x   -> "+" <> pretty x
    ModDelete x   -> "-" <> pretty x
    ModChange x y -> pretty x <> "->" <> pretty x

instance (Pretty (f (Fix f))) => Pretty (Fix f) where
  pretty (Fix x) = pretty x

data CollectType (changeType :: * -> *) where
  CollectIns :: CollectType ModIns
  CollectDel :: CollectType ModDel

collectsChanges
  :: (MonadState (TreeDiff (SexpF Wildcard)) m)
  => CollectType ct
  -> m (Fix (C (Mod ct) SexpF))
collectsChanges typ = do
  diff <- get
  case diff of
    TreeIns pat _ d ->
      case typ of
        CollectIns -> do
          put d
          Fix . C . ModChanged . ModIns <$> traverse (\_ -> collectsChanges typ) pat
        CollectDel -> put d *> collectsChanges typ
    TreeDel pat _ d ->
      case typ of
        CollectIns -> put d *> collectsChanges typ
        CollectDel -> do
          put d
          Fix . C . ModChanged . ModDel <$> traverse (\_ -> collectsChanges typ) pat
    TreeCpy pat _ d -> do
      put d
      Fix . C . ModCpy <$> traverse (\_ -> collectsChanges typ) pat
    TreeEnd ->
      pure $ Fix $ C ModEnd

-- recoverSexp :: TreeDiff (SexpF Wildcard) -> Fix (C (Mod ModChange) SexpF)
-- recoverSexp diff =
--   zipChanges deletes inserts
--   where
--     inserts :: Fix (C (Mod ModIns) SexpF)
--     inserts = evalState (collectsChanges CollectIns) diff
--     deletes :: Fix (C (Mod ModDel) SexpF)
--     deletes = evalState (collectsChanges CollectDel) diff
--
--     zipChanges :: Fix (C (Mod ModDel) SexpF) -> Fix (C (Mod ModIns) SexpF) -> Fix (C (Mod ModChange) SexpF)
--     zipChanges (Fix (ModChanged (C (ModDel y)))) (Fix (C (ModChanged (ModIns x)))) =
--       Fix $ C $ ModChanged $ ModChange x y
--
--     zipChanges (Fix (C (ModCpy x))) (Fix (C (ModCpy y)))
--       | (Wildcard <$ x) == (Wildcard <$ y) =
--         let xs = toList x
--             ys = toList y
--         in Fix $
--            C $
--            ModCpy $
--            flip evalState (zipWith zipChanges xs ys) $
--            traverse (\_ -> gets head >>= \z -> modify tail *> pure z) x
--
--       | otherwise                          = error "Different ModCpy shapes"
--     zipChanges x                    (Fix (C ModEnd))     =
--       cata (Fix . C . onChanged (\(ModDel z) -> ModDelete z) . unC) x
--     zipChanges (Fix (C ModEnd))     y                    =
--       cata (Fix . C . onChanged (\(ModIns z) -> ModInsert z) . unC) y

splitDiff :: TreeDiff (SexpF Wildcard) -> (Fix (C (Mod ModDel) SexpF), Fix (C (Mod ModIns) SexpF))
splitDiff diff = (deletes, inserts)
  where
    inserts :: Fix (C (Mod ModIns) SexpF)
    inserts = evalState (collectsChanges CollectIns) diff
    deletes :: Fix (C (Mod ModDel) SexpF)
    deletes = evalState (collectsChanges CollectDel) diff

test :: Sexp -> Sexp -> IO ()
test x y = do
  TL.putStrLn $ "x = " <> display x
  TL.putStrLn $ "y = " <>  display y
  -- TL.putStrLn $ "difference: " <> display (recoverSexp $ diffSexpNaive x y)
  let diff                    = diffSexpNaive x y
      (deletions, insertions) = splitDiff diff
  TL.putStrLn $ display $ "deletions" PP.<$> PP.indent 2 (pretty deletions)
  TL.putStrLn $ display $ "insertions" PP.<$> PP.indent 2 (pretty insertions)

-- Utils

display :: (Pretty a) => a -> Text
display = PP.displayT . PP.renderPretty 0.8 100 . pretty

-- ppArray :: (Pretty a) => Array (Int, Int) a -> Doc
-- ppArray arr = PP.vcat
--   [ PP.hsep $ map (PP.fill maxWidth) $ PP.punctuate ","
--       [ pretty $ arr Array.! (i, j)
--       | j <- [jStart..jEnd]
--       ]
--   | i <- [iStart..iEnd]
--   ]
--   where
--     ((iStart, jStart), (iEnd, jEnd)) = Array.bounds arr
--     maxWidth = 1 + maximum (map (length . display') $ Array.elems arr)

-- ppTable :: (Pretty a) => [[a]] -> Doc
-- ppTable xss = PP.vcat
--   [ PP.hsep $ map (PP.fill maxWidth) $ PP.punctuate "," $ map pretty xs
--   | xs <- xss
--   ]
--   where
--     maxWidth = 1 + maximum (map (length . display') $ concat xss)

