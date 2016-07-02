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

{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE QuasiQuotes                #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE UndecidableInstances       #-}

module SexpDiff where

import Control.Arrow
import Control.Monad.Except
import Control.Monad.Free
import Control.Monad.State
import Data.Bifunctor
import Data.Copointed
import Data.Foldable
import Data.Functor.Classes
import Data.Map (Map)
import qualified Data.Map as M
import Data.Monoid
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TL
import Data.Void
-- import Data.Vector (Vector)
-- import qualified Data.Vector as V
import Text.PrettyPrint.Leijen.Text (Pretty(..), Doc)
import qualified Text.PrettyPrint.Leijen.Text as PP

import Data.Elisp
import Data.Elisp.TH

data Wildcard = Wildcard
  deriving (Show, Eq, Ord)

instance Pretty Wildcard where
  pretty = const "_"

-- data SexpF e =
--     Num Int
--   | Double Double
--   | Symbol Text
--   | String Text
--   | Nil
--   | Cons e e
--   deriving (Show, Eq, Ord, Functor, Foldable, Traversable)
--
-- consSpine :: Sexp -> Maybe [Sexp]
-- consSpine (Fix (Cons x xs)) = (x :) <$> consSpine xs
-- consSpine (Fix Nil)         = return []
-- consSpine _                 = Nothing
--
-- instance {-# OVERLAPS #-} Pretty (Fix SexpF) where
--   pretty = \case
--     Fix (Num n)            -> PP.int n
--     Fix (Double x)         -> PP.double x
--     Fix (Symbol s)         -> PP.text s
--     Fix (String s)         -> PP.dquotes $ PP.text $ TL.pack $ show $ TL.unpack s
--     Fix Nil                -> "()"
--     Fix (Cons x (Fix Nil)) -> PP.parens $ pretty x
--     Fix (Cons x xs)        ->
--       PP.parens $ pretty x PP.<+> tail
--       where
--         tail =
--           case consSpine xs of
--             Just xs' -> PP.align (PP.sep $ map pretty xs')
--             Nothing  -> "." PP.<+> pretty xs
--
-- instance (Pretty e) => Pretty (SexpF e) where
--   pretty = \case
--     Num n    -> PP.int n
--     Double x -> PP.double x
--     Symbol s -> PP.text s
--     String s -> PP.dquotes $ PP.text $ TL.pack $ show $ TL.unpack s
--     Nil      -> "()"
--     Cons x y -> PP.parens $ pretty x PP.<+> "." PP.<+> pretty y
--
-- type Sexp      = Fix SexpF

newtype C f g a = C { unC :: f (g a) }
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance (Pretty (f (g a))) => Pretty (C f g a) where
  pretty (C x) = pretty x

instance (Pretty (f (g (Fix (C f g))))) => Pretty (Fix (C f g)) where
  pretty = pretty . unC . unFix

instance (IsNil (f (g a))) => IsNil (C f g a) where
  isNil (C x) = isNil x

instance (HasSymbol (f (g a))) => HasSymbol (C f g a) where
  getSymbol (C x) = getSymbol x

unFix :: Fix f -> f (Fix f)
unFix (Fix x) = x

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

futu :: (Functor f) => (a -> Free f a) -> a -> Fix f
futu coalg = free (futu coalg) Fix . coalg

free :: (Functor f) => (a -> b) -> (f b -> b) -> Free f a -> b
free f _ (Pure x) = f x
free f g (Free x) = g $ fmap (free f g) x

-- Diff on trees

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

-- | Populate node identifiers with integers in order to make sharing explicit.
enumerateTrees :: forall a. (Ord a) => [Tree a] -> [Tree a] -> ([Fix (TreeF a Int)], [Fix (TreeF a Int)])
enumerateTrees x y =
  flip evalState emptyState $ do
    x' <- traverse (cataM alg) x
    y' <- traverse (cataM alg) y
    pure (x', y')
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

diffTrees :: forall a. (Ord a) => [Tree a] -> [Tree a] -> TreeDiff a
diffTrees xs ys = flip evalState mempty $ memoizeBy (map (identifier . unFix)) go xs' ys'
  where
    (xs',  ys') = enumerateTrees xs ys
    go
      :: (Ord b, MonadState (Map ([Int], [Int]) (TreeDiff a)) m)
      => ([Fix (TreeF a b)] -> [Fix (TreeF a b)] -> m (TreeDiff a))
      -> [Fix (TreeF a b)]
      -> [Fix (TreeF a b)]
      -> m (TreeDiff a)
    go _         []                               []                        = pure TreeEnd
    go rec       []                               (Fix (Node y _ ys) : ys') = TreeIns y (length ys) <$> rec [] (ys ++ ys')
    go rec       (Fix (Node x _ xs) : xs')        []                        = TreeDel x (length xs) <$> rec (xs ++ xs') []
    go rec xsFull@(Fix (Node x _ xs) : xs') ysFull@(Fix (Node y _ ys) : ys')
      | x == y && xsLen == ysLen = cpyDiff
      | otherwise                = best2
      where
        xsLen = length xs
        ysLen = length ys
        best2 = minCost
                  <$> (TreeIns y ysLen <$> rec xsFull      (ys ++ ys'))
                  <*> (TreeDel x xsLen <$> rec (xs ++ xs') ysFull)
        cpyDiff = TreeCpy x xsLen <$> rec (xs ++ xs') (ys ++ ys')
        -- best3 = minCost <$> cpyDiff <*> best2

memoizeBy
  :: forall a b c m. (Ord b, MonadState (Map (b, b) c) m)
  => (a -> b)
  -> ((a -> a -> m c) -> a -> a -> m c)
  -> (a -> a -> m c)
memoizeBy key f = g
  where
    g :: a -> a -> m c
    g x y = do
      store <- get
      let k = (key x, key y)
      case M.lookup k store of
        Just x  -> pure x
        Nothing -> do
          z <- f g x y
          modify $ M.insert k z
          pure z

-- Functor modifiers for pretty-printing

data Mod c a =
    ModChanged (c a)
  | ModCpy a
  | ModEnd -- TODO - remove this case
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance (Copointed c) => Copointed (Mod c) where
  copoint (ModChanged x) = copoint x
  copoint (ModCpy x)     = x
  copoint ModEnd         = error "copoint called on ModEnd"

instance (IsNil (c a), IsNil a) => IsNil (Mod c a) where
  isNil (ModChanged x) = isNil x
  isNil (ModCpy x)     = isNil x
  isNil ModEnd         = False

instance (HasSymbol (c a), HasSymbol a) => HasSymbol (Mod c a) where
  getSymbol (ModChanged x) = getSymbol x
  getSymbol (ModCpy x)     = getSymbol x
  getSymbol ModEnd         = Nothing

onChanged :: (forall a. c a -> c' a) -> Mod c a -> Mod c' a
onChanged f (ModChanged x) = ModChanged $ f x
onChanged _ (ModCpy x)     = ModCpy x
onChanged _ ModEnd         = ModEnd

newtype ModIns a = ModIns a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable, IsNil, HasSymbol)

instance Eq1 ModIns where
  eq1 = (==)

instance Copointed ModIns where
  copoint (ModIns x) = x

instance (Pretty a) => Pretty (ModIns a) where
  pretty = \case
    ModIns x -> "+" <> pretty x

newtype ModDel a = ModDel a
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable, IsNil, HasSymbol)

instance Eq1 ModDel where
  eq1 = (==)

instance Copointed ModDel where
  copoint (ModDel x) = x

instance (Pretty a) => Pretty (ModDel a) where
  pretty = \case
    ModDel x -> "-" <> pretty x

instance (Pretty a, Pretty (c a)) => Pretty (Mod c a) where
  pretty = \case
    ModChanged x -> pretty x
    ModCpy x     -> pretty x
    ModEnd       -> "END"

instance (Eq1 c) => Eq1 (Mod c) where
  eq1 (ModChanged x) (ModChanged y) = x `eq1` y
  eq1 ModChanged{}   _              = False
  eq1 (ModCpy x)     (ModCpy y)     = x == y
  eq1 ModCpy{}       _              = False
  eq1 ModEnd         ModEnd         = True
  eq1 ModEnd         _              = False

-- instance
--   ( Pretty (c (SexpF (Fix (C (Mod c) SexpF))))
--   , IsNil (c (SexpF (Fix (C (Mod c) SexpF))))
--   , HasSymbol (c (SexpF (Fix (C (Mod c) SexpF))))
--   ) => Pretty (Fix (C (Mod c) SexpF)) where
--   pretty = pretty . unC . unFix

-- data ModChange a =
--     ModInsert a
--   | ModDelete a
--   | ModChange a a
--   deriving (Show, Eq, Ord, Functor, Foldable, Traversable)
--
-- instance (Pretty a) => Pretty (ModChange a) where
--   pretty = \case
--     ModInsert x   -> "+" <> pretty x
--     ModDelete x   -> "-" <> pretty x
--     ModChange x y -> pretty x <> "->" <> pretty y

data CollectType (changeType :: * -> *) where
  CollectIns :: CollectType ModIns
  CollectDel :: CollectType ModDel

collectsChanges
  :: forall f m ct. (Traversable f, MonadState (TreeDiff (f Wildcard)) m)
  => CollectType ct
  -> m (Fix (C (Mod ct) f))
collectsChanges typ = go
  where
    go :: m (Fix (C (Mod ct) f))
    go = do
      diff <- get
      case diff of
        TreeIns pat _ d ->
          case typ of
            CollectIns -> do
              put d
              Fix . C . ModChanged . ModIns <$> traverse (\_ -> go) pat
            CollectDel -> put d *> go
        TreeDel pat _ d ->
          case typ of
            CollectIns -> put d *> go
            CollectDel -> do
              put d
              Fix . C . ModChanged . ModDel <$> traverse (\_ -> go) pat
        TreeCpy pat _ d -> do
          put d
          Fix . C . ModCpy <$> traverse (\_ -> go) pat
        TreeEnd -> -- error "TreeEnd should never be reached"
          pure $ Fix $ C ModEnd

splitDiff
  :: forall f. (Traversable f)
  => TreeDiff (f Wildcard)
  -> (Fix (C (Mod ModDel) f), Fix (C (Mod ModIns) f))
splitDiff diff = (deletes, inserts)
  where
    inserts :: Fix (C (Mod ModIns) f)
    inserts = evalState (collectsChanges CollectIns) diff
    deletes :: Fix (C (Mod ModDel) f)
    deletes = evalState (collectsChanges CollectDel) diff

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

-- Linearization of lists in sexp to get nicer diffs

data SexpSignatureF e =
    SignAtom (SexpAtom Void)
  | SignListCons e e
  | SignListNil NilRepr
  | SignVectorCons e e
  | SignVectorNil
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

type SexpSignature = Fix SexpSignatureF

type SignTree = Tree (SexpSignatureF Wildcard)

stripProperties :: SexpAtom a -> SexpAtom Void
stripProperties = \case
  Integer n    -> Integer n
  Float x      -> Float x
  Symbol sym   -> Symbol sym
  String str _ -> String str $ StringProperties []
  Character c  -> Character c

toSexpSignature :: Sexp -> SignTree
toSexpSignature = cata alg . futu expandComposites
  where
    alg :: SexpSignatureF SignTree -> SignTree
    alg x = Fix $ Node (Wildcard <$ x) () $ toList x
    expandComposites :: Sexp -> Free SexpSignatureF Sexp
    expandComposites = \case
      Fix (Atom a)        -> Free $ SignAtom $ stripProperties a
      Fix (Nil repr)      -> Free $ SignListNil repr
      Fix (List x xs end) ->
        foldr (\x acc -> Free $ SignListCons (Pure x) acc) (Pure end) (x : xs)
      Fix (Vector xs)     ->
        foldr (\x acc -> Free $ SignVectorCons (Pure x) acc) (Free SignVectorNil) xs
      Fix HashTable{}     -> error "cannot convert hash table to sexp signature"

-- toSexp :: TreeDiff (SexpSignatureF Wildcard) -> TreeDiff (SexpF Wildcard)
-- toSexp = undefined

diffSexp :: Sexp -> Sexp -> TreeDiff (SexpSignatureF Wildcard)
diffSexp x y = diffTrees [toSexpSignature x] [toSexpSignature y]

toSexp :: forall f. (Functor f, Copointed f) => Fix (C (Mod f) SexpSignatureF) -> Fix (C (Mod f) SexpF)
toSexp = cata (Fix . C. fmap alg . unC)
  where
    alg :: SexpSignatureF (Fix (C (Mod f) SexpF)) -> SexpF (Fix (C (Mod f) SexpF))
    alg = \case
     SignAtom atom  -> Atom $ absurd <$> atom
     SignListCons x (Fix (C xs)) -> case xs' of
         List y ys end -> List x (y : ys) end
         Nil _         -> List x [] (Fix (C xs))
         _             -> error "Cons applied to non-list tail"
         where
           xs' :: SexpF (Fix (C (Mod f) SexpF))
           xs' = copoint xs
       -- Fix $ C $ flip fmap xs $ \case
       --   List xs' -> List (x : xs')
     SignListNil repr   -> Nil repr
     SignVectorCons _ _ -> undefined
     SignVectorNil      -> Vector mempty


sexpToTree :: Sexp -> Tree (SexpF Wildcard)
sexpToTree = cata alg
  where
    alg :: SexpF (Tree (SexpF Wildcard)) -> Tree (SexpF Wildcard)
    alg x = Fix $ Node (Wildcard <$ x) () $ toList x

diffSexp' :: Sexp -> Sexp -> TreeDiff (SexpF Wildcard)
diffSexp' x y = diffTrees [sexpToTree x] [sexpToTree y]

-- Compression

data ModSubtree f a =
    ModAtomic (f a)
  | ModSubtree a -- ^ Whole subtree was affected - inserted, deleted, etc.
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance (Copointed f) => Copointed (ModSubtree f) where
  copoint = \case
    ModAtomic x  -> copoint x
    ModSubtree x -> x

instance (Pretty (ModIns a), Pretty a) => Pretty (ModSubtree ModIns a) where
  pretty = \case
    ModAtomic x  -> pretty x
    ModSubtree x -> "++" <> pretty x

instance (Pretty (ModDel a), Pretty a) => Pretty (ModSubtree ModDel a) where
  pretty = \case
    ModAtomic x  -> pretty x
    ModSubtree x -> "--" <> pretty x

instance (Eq1 f) => Eq1 (ModSubtree f) where
  eq1 (ModAtomic x)  (ModAtomic y)  = x `eq1` y
  eq1 ModAtomic{}    _              = False
  eq1 (ModSubtree x) (ModSubtree y) = x == y
  eq1 ModSubtree{}   _              = False

instance (IsNil a, IsNil (f a)) => IsNil (ModSubtree f a) where
  isNil (ModAtomic x)  = isNil x
  isNil (ModSubtree x) = isNil x

instance (HasSymbol a, HasSymbol (f a)) => HasSymbol (ModSubtree f a) where
  getSymbol (ModAtomic x)  = getSymbol x
  getSymbol (ModSubtree x) = getSymbol x


compress
  :: forall f g. (Functor f, Functor g, Foldable g, Copointed f, Eq1 f)
  => Fix (C (Mod f) g)
  -> Fix (C (Mod (ModSubtree f)) g)
compress = cata (alg . unC)
  where
    alg :: Mod f (g (Fix (C (Mod (ModSubtree f)) g)))
        -> Fix (C (Mod (ModSubtree f)) g)
    alg = \case
      ModChanged x
        | allSame $ fmap (const Wildcard) . unC . unFix <$> x' ->
          Fix $ C $ ModChanged $ ModSubtree $
          Fix . C . removeChanges . unC . unFix <$> x'
        | otherwise                                            ->
          Fix $ C $ ModChanged $ ModAtomic x
        where
          x' :: g (Fix (C (Mod (ModSubtree f)) g))
          x' = copoint x

          removeChanges :: Mod (ModSubtree f) a -> Mod (ModSubtree f) a
          removeChanges = \case
            ModChanged x -> ModCpy $ copoint x
            x@ModCpy{}   -> x
            x@ModEnd{}   -> x
      x@ModCpy{} -> Fix $ C $ onChanged ModAtomic x
      x@ModEnd{} -> Fix $ C $ onChanged ModAtomic x

allSame :: (Foldable f, Eq1 g, Eq a) => f (g a) -> Bool
allSame = go . toList
  where
    go []            = True
    go [_]           = True
    go (x:xs@(x':_)) = x `eq1` x' && go xs

-- Tests

oldSexp :: Sexp
oldSexp = stripPositions $ [sexp|
  (x (y) z)
  |]

newSexp :: Sexp
newSexp = stripPositions $ [sexp|
  (x y y z)
  |]

-- oldSexp :: Sexp
-- oldSexp = stripPositions $ [sexp|
--   (x (y z))
--   |]
--
-- newSexp :: Sexp
-- newSexp = stripPositions $ [sexp|
--   (x y y z)
--   |]

-- oldSexp :: Sexp
-- oldSexp = stripPositions $ [sexp|
--   (dolist (keymap (list vim:normal-mode-keymap
--                         vim:visual-mode-keymap
--                         vim:operator-pending-mode-keymap
--                         vim:motion-mode-keymap))
--     (def-keys-for-map keymap
--       ("g g" vim:motion-go-to-first-non-blank-beg)
--       ("G"   vim:motion-go-to-first-non-blank-end)
--       ("j"   nil)
--
--       ("%"   nil)
--       ;; short for matching
--       ("m"   vim:motion-jump-item)
--
--       ("q"   sp-up-sexp)))
--
--   |]
--
-- newSexp :: Sexp
-- newSexp = stripPositions $ [sexp|
--   (def-keys-for-map (vim:normal-mode-keymap
--                      vim:visual-mode-keymap
--                      vim:operator-pending-mode-keymap
--                      vim:motion-mode-keymap)
--     ("0"   vim:motion-beginning-of-line-or-digit-argument)
--     ("1"   vim:digit-argument)
--     ("2"   vim:digit-argument)
--     ("3"   vim:digit-argument)
--     ("4"   vim:digit-argument)
--     ("5"   vim:digit-argument)
--     ("6"   vim:digit-argument)
--     ("7"   vim:digit-argument)
--     ("8"   vim:digit-argument)
--     ("9"   vim:digit-argument)
--
--     ("g g" vim:motion-go-to-first-non-blank-beg)
--     ("G"   vim:motion-go-to-first-non-blank-end)
--     ("j"   nil)
--
--     ("%"   nil)
--     ;; short for matching
--     ("m"   vim:motion-jump-item)
--
--     ("q"   sp-up-sexp))
--   |]

-- sexp1 :: Text
-- sexp1 = TL.pack
--   "(ert-deftest eproj-tests/eproj-get-all-related-projects ()\
--   \  (let* ((path eproj-tests/project-with-git-with-related)\
--   \         (proj (eproj-get-project-for-path path)))\
--   \    (should (eproj-tests/paths=? path (eproj-project/root proj)))\
--   \    (should (not (null? (eproj-project/related-projects proj))))\
--   \    (should (equal (eproj-tests/normalize-file-list\
--   \                    (map #'eproj-project/root\
--   \                         (cons proj\
--   \                               (eproj-get-all-related-projects proj))))\
--   \                   (eproj-tests/normalize-file-list\
--   \                    (filter #'file-directory?\
--   \                            (directory-files\
--   \                             eproj-tests/folder-with-related-projects\
--   \                             t\
--   \                             directory-files-no-dot-files-regexp)))))))\
--   \"
--
-- sexp2 :: Text
-- sexp2 =
--   "(ert-deftest eproj-tests/eproj-get-all-related-projects ()\
--   \  (let* ((path eproj-tests/project-with-git-with-related)\
--   \         (proj (eproj-get-project-for-path path)))\
--   \    (should (eproj-tests/paths=? path (eproj-project/root proj)))\
--   \    (should (not (null? (eproj-project/related-projects proj))))\
--   \    (should (equal (eproj-tests/normalize-file-list\
--   \                    (-map #'eproj-project/root\
--   \                          (cons proj\
--   \                                (eproj-get-all-related-projects proj))))\
--   \                   (eproj-tests/normalize-file-list\
--   \                    (-filter #'file-directory?\
--   \                             (directory-files\
--   \                              eproj-tests/folder-with-related-projects\
--   \                              t\
--   \                              directory-files-no-dot-files-regexp)))))))\
--   \"


main :: IO ()
main = test oldSexp newSexp

test :: Sexp -> Sexp -> IO ()
test x y = do
  withHeading "x:" x
  withHeading "y:" y
  -- TL.putStrLn $ "difference: " <> display (recoverSexp $ diffSexp x y)
  TL.putStrLn $ TL.replicate 32 "-"
  let diff                      = diffSexp x y
      diff'                     = diffSexp' x y
      (deletions, insertions)   = splitDiff diff
      (deletions', insertions') = splitDiff diff'
      compress'                 = id
  withHeading "deletions:"   $ compress' $ toSexp deletions
  withHeading "insertions:"  $ compress' $ toSexp insertions
  TL.putStrLn $ TL.replicate 32 "-"
  withHeading "deletions':"  $ compress' deletions'
  withHeading "insertions':" $ compress' insertions'
  -- withHeading "diff:"       $ PP.text $ TL.pack $ show diff

-- pattern List' xs    = Fix (List xs)
-- pattern Atom' x     = Fix (Atom x)
-- pattern Symbol' sym = Fix (Atom (Symbol sym))

-- Utils

display :: (Pretty a) => a -> Text
display = PP.displayT . PP.renderPretty 0.8 100 . pretty

withHeading :: (Pretty a) => Doc -> a -> IO ()
withHeading heading x =
  TL.putStrLn $ display $ heading PP.<$> PP.indent 2 (pretty x)

