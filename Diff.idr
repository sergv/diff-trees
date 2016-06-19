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

data Diff : (a : Type) -> Type where
  Ins : a -> Diff a -> Diff a
  Del : a -> Diff a -> Diff a
  Cpy : a -> Diff a -> Diff a
  Mod : a -> a -> Diff a -> Diff a
  End : Diff a

-- implementation (Pretty a) => Pretty (Diff a) where
--   pretty (Ins x d) = text "+" <+> pretty x <+> pretty d
--   pretty (Del x d) = text "-" <+> pretty x <+> pretty d
--   pretty (Cpy x d) = text " " <+> pretty x <+> pretty d
--   pretty End       = neutral

implementation Pretty (Diff Char) where
  pretty (Ins x d)   = text "+" <+> char x </> pretty d
  pretty (Del x d)   = text "-" <+> char x </> pretty d
  pretty (Cpy x d)   = text " " <+> char x </> pretty d
  pretty (Mod x y d) = text "/" <+> char x <+> text "/" <+> char y </> pretty d
  pretty End         = neutral

-- implementation Pretty (Lazy (Diff Char)) where
--   pretty = pretty . Force

insert : a -> List a -> Maybe (List a)
insert x xs = Just (x :: xs)

delete : (Eq a) => a -> List a -> Maybe (List a)
delete _ []        = Nothing
delete x (y :: ys) = if x == y then Just ys else Nothing

patch : (Eq a) => Diff a -> List a -> Maybe (List a)
patch (Ins x d)   = insert x <=< patch d
patch (Del x d)   =              patch d <=< delete x
patch (Cpy x d)   = insert x <=< patch d <=< delete x
patch (Mod x y d) = insert y <=< patch d <=< delete x
patch End         = \xs => case xs of
  [] => Just xs
  _  => Nothing

interface HasCost a where
  cost : a -> Nat

implementation HasCost (Diff a) where
  cost (Ins _ d)   = S $ cost d
  cost (Del _ d)   = S $ cost d
  cost (Cpy _ d)   = cost d
  cost (Mod _ _ d) = S $ cost d
  cost End         = Z

minDiff : (HasCost a) => a -> a -> a
minDiff x y = if cost x <= cost y
  then x
  else y

diff : (Eq a) => List a -> List a -> Diff a
diff []               []               = End
diff []               (y :: ys)        = Ins y $ diff [] ys
diff (x :: xs)        []               = Del x $ diff xs []
diff xsFull@(x :: xs) ysFull@(y :: ys) =
  let best2 = minDiff
                (Del x (diff xs ysFull))
                (Ins y (diff xsFull ys))
      -- best3 = minDiff (Cpy x (diff xs ys)) best2
  in
  if x == y
  then Cpy x (diff xs ys) -- best3
  else
    -- minDiff
      best2
      -- (Mod x y (diff xs ys))

diffStrs : String -> String -> Diff Char
diffStrs x y = diff (unpack x) (unpack y)

relaxFin : LTE k n -> Fin k -> Fin n
relaxFin LTEZero       x      = FinZElim x
relaxFin (LTESucc lte) FZ     = FZ
relaxFin (LTESucc lte) (FS x) = FS $ relaxFin lte x

buildVect : (n : Nat) -> (Fin n -> a) -> Vect n a
buildVect n f = reverse $ go n lteRefl
  where
    go : (k : Nat) -> LTE k n -> Vect k a
    go Z       _   = []
    go x@(S k) lte = f idx :: go k (lteSuccLeft lte)
      where
        idx : Fin n
        idx = relaxFin lte last

infixl 5 !!

(!!) : Vect n a -> Fin n -> a
(!!) v i = index i v

partial
diffMemo : (Eq a) => {n, m : Nat} -> Vect (S n) a -> Vect (S m) a -> Diff a
diffMemo {n = n} {m = m} xs ys = Force $ table !! last !! last
  where
    mutual
      partial
      fill : Fin (S n) -> Fin (S m) -> Lazy (Diff a)
      -- fill i j =
      --   case (finToNat i, finToNat j) of
      --     (Z, Z)    => End
      --     (Z, S j') => Ins (ys !! j) $ (table !! i) !! ?first -- weaken (pred j)
      --     (_, _)    => ?last
      fill FZ        FZ        = End
      fill i@FZ      j@(FS j') = Ins (ys !! j) $ Force $ table !! i         !! weaken j'
      fill i@(FS i') j@FZ      = Del (xs !! i) $ Force $ table !! weaken i' !! j
      fill i@(FS i') j@(FS j') =
        let x     = xs !! i
            y     = ys !! j
            best2 = minDiff
                      (Del x $ Force $ table !! weaken i' !! j)
                      (Ins y $ Force $ table !! i         !! weaken j')
            best3 = minDiff
                      best2
                      (Cpy x $ Force $ table !! weaken i' !! weaken j')
        in
        if x == y
        then best3
        else
          minDiff
            best2
            (Mod x y $ Force $ table !! weaken i' !! weaken j')

      partial
      table : Vect (S n) (Vect (S m) (Lazy (Diff a)))
      table =
        buildVect (S n) $ \i =>
          buildVect (S m) $ \j =>
            fill i j

strToVect : String -> (n ** Vect n Char)
strToVect = go . unpack
  where
    go : List Char -> (n ** Vect n Char)
    go cs = (_ ** fromList cs)

-- diffStrsMemo' : List Char -> List Char -> Maybe (Diff Char)
-- diffStrsMemo' x y with (fromList x, fromList y)
--   diffStrsMemo' []     _      | ([],        _)         = Nothing
--   diffStrsMemo' _      []     | (_,         [])        = Nothing
--   diffStrsMemo' (x :: xs) (y :: ys) | (x :: xs, y :: ys) = Just $ diffMemo (x :: xs) (y :: ys)

partial
diffStrsMemo : String -> String -> Maybe (Diff Char)
diffStrsMemo xs ys =
  case (strToVect xs, strToVect ys) of
    ((Z ** _),     _)            => Nothing
    (_,            (Z ** _))     => Nothing
    ((S _ ** xs'), (S _ ** ys')) => Just $ diffMemo xs' ys'

patch_diff_spec : (Eq a) => List a -> List a -> Type
patch_diff_spec = \xs, ys => patch (diff xs ys) ys = Just ys

-- the (Maybe String) $ pack $ patch (diffStrs "abcd" "aeecd") (unpack "abcd")
-- :x putStrLn $ display $ diffStrs "abcd" "aeecd"

-- test
-- putStrLn $ display $ diffStrs "abcabba" "cbabac"

-- testDiff : Diff Char
-- testDiff = diffStrs "abcabba" "cbabac"

-- partial
-- main : IO ()
-- main =
--   -- putStrLn $ display $ diffStrsMemo "abcabba" "cbabac"
--   putStrLn $ display $ diffStrs "abcabba" "cbabac"

data Tree : (a : Type) -> Type where
  Node : a -> List (Tree a) -> Tree a

data TreeDiff : (a : Type) -> Type where
  TreeIns : a -> Nat -> TreeDiff a -> TreeDiff a
  TreeDel : a -> Nat -> TreeDiff a -> TreeDiff a
  TreeCpy : a -> Nat -> TreeDiff a -> TreeDiff a
  TreeEnd : TreeDiff a

implementation HasCost (TreeDiff a) where
  cost (TreeIns _ _ d) = S $ cost d
  cost (TreeDel _ _ d) = S $ cost d
  cost (TreeCpy _ _ d) = cost d
  cost TreeEnd         = Z

insertTree : a -> Nat -> List (Tree a) -> Maybe (List (Tree a))
insertTree x n ts =
  let (ts', ts'') = splitAt n ts
  in
  if length ts' == n
  then Just $ Node x ts' :: ts''
  else Nothing

deleteTree : (Eq a) => a -> Nat -> List (Tree a) -> Maybe (List (Tree a))
deleteTree _ _ []                 = Nothing
deleteTree x n (Node y ts :: ts') =
  if x == y && length ts == n
  then Just $ ts ++ ts'
  else Nothing

patchTree : (Eq a) => TreeDiff a -> List (Tree a) -> Maybe (List (Tree a))
patchTree (TreeIns x n d) = insertTree x n <=< patchTree d
patchTree (TreeDel x n d) =                    patchTree d <=< deleteTree x n
patchTree (TreeCpy x n d) = insertTree x n <=< patchTree d <=< deleteTree x n
patchTree TreeEnd         = \xs =>
  case xs of
    [] => Just xs
    _  => Nothing

partial
diffTrees : (Eq a) => List (Tree a) -> List (Tree a) -> TreeDiff a
diffTrees []                        []                        = TreeEnd
diffTrees []                        (Node y ys :: ys')        = TreeIns y (length ys) $ diffTrees [] (ys ++ ys')
diffTrees (Node x xs :: xs')        []                        = TreeDel x (length xs) $ diffTrees (xs ++ xs') []
diffTrees xsFull@(Node x xs :: xs') ysFull@(Node y ys :: ys') =
  let xsLen = length xs
      ysLen = length ys
      best2 = minDiff
                (TreeIns y ysLen $ diffTrees xsFull      (ys ++ ys'))
                (TreeDel x xsLen $ diffTrees (xs ++ xs') ysFull)
      best3 = minDiff
                (TreeCpy x xsLen $ diffTrees (xs ++ xs') (ys ++ ys'))
                best2
  in
  if x == y && xsLen == ysLen
  then best3
  else best2

