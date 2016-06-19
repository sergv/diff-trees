----------------------------------------------------------------------------
-- |
-- Module      :  Diff
-- Copyright   :  (c) Sergey Vinokurov 2016
-- License     :  BSD3-style (see LICENSE)
--
-- Maintainer  :  serg.foo@gmail.com
-- Created     :  Sunday, 12 June 2016
-- Stability   :
-- Portability :
--
--
----------------------------------------------------------------------------

{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}

module DiffAlgorithms where

import Control.DeepSeq
import Control.Monad
import Control.Exception

import Data.Array (Array)
import qualified Data.Array as Array
import Data.Char
import Data.DList (DList)
import qualified Data.DList as DL
import Data.Foldable
import Data.Function
import Data.List (scanl')
import qualified Data.List as L
import Data.Maybe
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as S
import GHC.Generics

import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as TL
import Text.PrettyPrint.Leijen.Text (Pretty(..), Doc)
import qualified Text.PrettyPrint.Leijen.Text as PP

import qualified Data.Algorithm.Diff as AlgDiff
import qualified FastDiff

import Criterion.Main
import Criterion.Types
import System.Directory
import System.FilePath

-- import Options.Applicative
-- import qualified Options.Applicative as Opts

import Test.Tasty
import Test.Tasty.QuickCheck as QC
import Test.QuickCheck

import Debug.Trace

display :: (Pretty a) => a -> Text
display = PP.displayT . PP.renderPretty 0.8 100 . pretty

display' :: (Pretty a) => a -> String
display' = TL.unpack . display

-- | Diff that starts from the string end and grows to the beginning.
data Diff a where
  Ins :: a -> Diff a -> Diff a
  Del :: a -> Diff a -> Diff a
  Cpy :: a -> Diff a -> Diff a
  Mod :: a -> a -> Diff a -> Diff a
  End :: Diff a

deriving instance (Show a) => Show (Diff a)

instance (Pretty a) => Pretty (Diff a) where
  pretty (Ins x d)   = "+" <> pretty x <> pretty d
  pretty (Del x d)   = "-" <> pretty x <> pretty d
  pretty (Cpy x d)   = "=" <> pretty x <> pretty d
  pretty (Mod x y d) = "/" <> pretty x <> "/" <> pretty y <> "/" <> pretty d
  pretty End         = mempty

ppArray :: (Pretty a) => Array (Int, Int) a -> Doc
ppArray arr = PP.vcat
  [ PP.hsep $ map (PP.fill maxWidth) $ PP.punctuate ","
      [ pretty $ arr Array.! (i, j)
      | j <- [jStart..jEnd]
      ]
  | i <- [iStart..iEnd]
  ]
  where
    ((iStart, jStart), (iEnd, jEnd)) = Array.bounds arr
    maxWidth = 1 + maximum (map (length . display') $ Array.elems arr)

ppTable :: (Pretty a) => [[a]] -> Doc
ppTable xss = PP.vcat
  [ PP.hsep $ map (PP.fill maxWidth) $ PP.punctuate "," $ map pretty xs
  | xs <- xss
  ]
  where
    maxWidth = 1 + maximum (map (length . display') $ concat xss)

getLcs :: Diff a -> [a]
getLcs (Ins _ d)   = getLcs d
getLcs (Del _ d)   = getLcs d
getLcs (Cpy x d)   = x : getLcs d
getLcs (Mod _ _ d) = getLcs d
getLcs End         = []

subsequences :: [a] -> [[a]]
subsequences = toList . go
  where
    go :: [a] -> DList [a]
    go []     = DL.singleton []
    go (x:xs) = xss <> fmap (x:) xss
      where
        xss = go xs

allLcsNaive :: forall a. (Ord a) => [a] -> [a] -> Set [a]
allLcsNaive xs ys = S.filter ((maxLcsLen ==) . length) lcss
  where
    lcss :: Set [a]
    lcss = S.intersection xss yss
    maxLcsLen = S.findMax $ S.map length lcss
    xss, yss :: Set [a]
    xss = S.fromList $ subsequences xs
    yss = S.fromList $ subsequences ys

class Cost a where
  cost :: a -> Int

instance Cost (Diff a) where
  cost (Ins _ d)   = 1 + cost d
  cost (Del _ d)   = 1 + cost d
  cost (Cpy _ d)   = cost d
  cost (Mod _ _ d) = 1 + cost d
  cost End         = 0

minDiff :: (Cost a) => a -> a -> a
minDiff x y
  | cost x <= cost y = x
  | otherwise        = y

minDiff3 :: (Cost a) => a -> a -> a -> a
minDiff3 x y z
  | cost x <= cost y = x
  | otherwise        = minDiff y z

diffNaive :: (Eq a) => [a] -> [a] -> Diff a
diffNaive []         []     = End
diffNaive []         (y:ys) = Ins y $ diffNaive [] ys
diffNaive (x:xs)     []     = Del x $ diffNaive xs []
diffNaive xs'@(x:xs) ys'@(y:ys)
  | x == y    = Cpy x $ diffNaive xs ys
  | otherwise =
    minDiff3
      (Del x   $ diffNaive xs  ys')
      (Ins y   $ diffNaive xs' ys)
      (Mod x y $ diffNaive xs ys)

-- | Diff that starts from the string beginning and grows to the end.
data RevDiff a where
  RevIns :: a -> RevDiff a -> RevDiff a
  RevDel :: a -> RevDiff a -> RevDiff a
  RevCpy :: a -> RevDiff a -> RevDiff a
  RevMod :: a -> a -> RevDiff a -> RevDiff a
  RevEnd :: RevDiff a

instance Cost (RevDiff a) where
  cost (RevIns _ d)   = 1 + cost d
  cost (RevDel _ d)   = 1 + cost d
  cost (RevCpy _ d)   = cost d
  cost (RevMod _ _ d) = 1 + cost d
  cost RevEnd         = 0

deriving instance (Show a) => Show (RevDiff a)

instance (Pretty a) => Pretty (RevDiff a) where
  pretty (RevIns x d)   = pretty d <> "+" <> pretty x
  pretty (RevDel x d)   = pretty d <> "-" <> pretty x
  pretty (RevCpy x d)   = pretty d <> "=" <> pretty x
  pretty (RevMod x y d) = pretty d <> "/" <> pretty x <> "/" <> pretty y <> "/"
  pretty RevEnd         = mempty

unRevDiff :: forall a. RevDiff a -> Diff a
unRevDiff d = go d End
  where
    go :: RevDiff a -> Diff a -> Diff a
    go (RevIns x d) acc   = go d $ Ins x acc
    go (RevDel x d) acc   = go d $ Del x acc
    go (RevCpy x d) acc   = go d $ Cpy x acc
    go (RevMod x y d) acc = go d $ Mod x y acc
    go RevEnd acc         = acc

diffTabular :: forall a. (Eq a) => [a] -> [a] -> Diff a
diffTabular []     []     = End
diffTabular []     (y:ys) = Ins y $ diffTabular [] ys
diffTabular (x:xs) []     = Del x $ diffTabular xs []
diffTabular xs     ys     =
  -- trace ("table =\n" ++ display' (ppArray table)) $
  unRevDiff $
  getDiff xsLen ysLen
  where
    xsLen = length xs
    ysLen = length ys
    getDiff :: Int -> Int -> RevDiff a
    getDiff i j = table Array.! (i, j)
    table :: Array (Int, Int) (RevDiff a)
    table = Array.array ((0, 0), (xsLen, ysLen)) $
              [ ((i, j), mkDiff i x j y)
              | (x, i) <- zip xs [1..]
              , (y, j) <- zip ys [1..]
              ] ++
              [ ((i, 0), RevDel x $ getDiff (i - 1) 0)
              | (x, i) <- zip xs [1..xsLen]
              ] ++
              [ ((0, j), RevIns y $ getDiff 0 (j - 1))
              | (y, j) <- zip ys [1..ysLen]
              ] ++
              [ ((0, 0), RevEnd)
              ]
    mkDiff :: Int -> a -> Int -> a -> RevDiff a
    -- mkDiff 0 _ 0 _ = End
    --   -- | firstX == firstY = Cpy firstX End
    --   -- | otherwise        = Mod firstX firstY End
    -- mkDiff 0 _ j y = Ins y $ getDiff 0       (j - 1)
    -- mkDiff i x 0 _ = Del x $ getDiff (i - 1) 0
    mkDiff i x j y
      | x == y    = RevCpy x $ getDiff (i - 1) (j - 1)
      | otherwise =
        minDiff3
          (RevIns y   $ getDiff i       (j - 1))
          (RevDel x   $ getDiff (i - 1) j)
          (RevMod x y $ getDiff (i - 1) (j - 1))

diffLinewise :: forall a. (Eq a) => [a] -> [a] -> Diff a
diffLinewise xs ys =
  unRevDiff $ go xs firstRow
  where
    firstRow :: [RevDiff a]
    firstRow = scanl' (\acc y -> RevIns y acc) RevEnd ys
    go :: [a] -> [RevDiff a] -> RevDiff a
    go []       prevRow  = last prevRow
    go _        []       = error "diffLinewise.go: empty previous row"
    go (x : xs) (r : rs) = go xs nextRow
      where
        nextRow :: [RevDiff a]
        nextRow = firstItem : computeRow ys firstItem r rs
        firstItem = RevDel x r

        computeRow :: [a] -> RevDiff a -> RevDiff a -> [RevDiff a] -> [RevDiff a]
        computeRow _      _ _  []     = []
        computeRow []     _ _  _      = []
        computeRow (y:ys) w nw (n:rs) = item : computeRow ys item n rs
          where
            item
              | x == y    = RevCpy x nw
              | otherwise =
                minDiff3
                  (RevIns y w)
                  (RevDel x n)
                  (RevMod x y nw)

diffDiagonal :: forall a. (Eq a, Pretty a) => [a] -> [a] -> Diff a
diffDiagonal []     []     = End
diffDiagonal []     (b:bs) = Ins b $ diffDiagonal [] bs
diffDiagonal (a:as) []     = Del a $ diffDiagonal as []
diffDiagonal as     bs     =
  unRevDiff $ last $
  if | lab == 0 -> mainDiag
     | lab >  0 -> last $ take lab lowers
     | lab <  0 -> last $ take (abs lab) uppers
  where
    lab :: Int
    lab = length as - length bs

    -- Convert diagonal representation to 2d table for debugging
    -- table :: [[RevDiff a]]
    -- table =
    --   firstRow : mkRows lowers nextRows
    --   where
    --     initRows = mainDiag : uppers
    --     firstRow = map head initRows
    --     nextRows :: [[RevDiff a]]
    --     nextRows = filter (not . null) $ map tail initRows
    --     mkRows :: [[RevDiff a]] -> [[RevDiff a]] -> [[RevDiff a]]
    --     mkRows []       _    = []
    --     mkRows _        []   = []
    --     mkRows (l : ls) rows = map head rows' : mkRows ls (filter (not . null) (map tail rows'))
    --       where
    --         rows' = l : rows

    mainDiag :: [RevDiff a]
    mainDiag = mkDiag (\a _b -> RevDel a) (\_a b -> RevIns b) as bs mainDiagStart (head lowers) (head uppers)

    mainDiagStart :: RevDiff a
    mainDiagStart = RevEnd

    mkDiag
      :: (a -> a -> RevDiff a -> RevDiff a)
      -> (a -> a -> RevDiff a -> RevDiff a)
      -> [a]
      -> [a]
      -> RevDiff a
      -> [RevDiff a]
      -> [RevDiff a]
      -> [RevDiff a]
    mkDiag modA modB as bs firstElement diagBelow diagAbove = thisDiag
      where
        thisDiag :: [RevDiff a]
        thisDiag = firstElement : doDiag as bs firstElement diagBelow diagAbove

        doDiag :: [a] -> [a] -> RevDiff a -> [RevDiff a] -> [RevDiff a] -> [RevDiff a]
        doDiag []     _      _  _ _ = []
        doDiag _      []     _  _ _ = []
        doDiag (a:as) (b:bs) nw w n =
          thisElem : doDiag as bs thisElem (tail w) (tail n)
          where
            thisElem | a == b    = RevCpy a nw
                     | otherwise =
                       minDiff3
                         (modB a b (head w))
                         (modA a b (head n))
                         (RevMod a b nw)

    uppers :: [[RevDiff a]]
    uppers = buildDiags RevIns (\a _b -> RevDel a) (\_a b -> RevIns b) bs as mainDiagStart (tail mainDiag) uppers

    lowers :: [[RevDiff a]]
    lowers = buildDiags RevDel (\_a b -> RevIns b) (\a _b -> RevDel a) as bs mainDiagStart (tail mainDiag) lowers

    buildDiags
      :: (a -> RevDiff a -> RevDiff a)
      -> (a -> a -> RevDiff a -> RevDiff a)
      -> (a -> a -> RevDiff a -> RevDiff a)
      -> [a]
      -> [a]
      -> RevDiff a
      -> [RevDiff a]
      -> [[RevDiff a]]
      -> [[RevDiff a]]
    buildDiags _   _    _    []     _  _             _        _     = []
    buildDiags upd modA modB (a:as) bs prevDiagStart prevDiag diags =
      thisDiag : buildDiags upd modA modB as bs thisDiagStart (tail thisDiag) (tail diags)
      where
        thisDiagStart :: RevDiff a
        thisDiagStart = upd a prevDiagStart
        thisDiag :: [RevDiff a]
        thisDiag = mkDiag modA modB as bs thisDiagStart prevDiag nextDiag
        nextDiag :: [RevDiff a]
        nextDiag = head $ tail diags

data Input a = Input
  { _inputXs :: [a]
  , _inputYs :: [a]
  } deriving (Show, Eq, Ord, Generic)

data EnumType = A | B | C
  deriving (Show, Eq, Ord, Generic)

instance Arbitrary EnumType where
  arbitrary = elements [A, B, C]

instance Pretty EnumType where
  pretty = PP.text . TL.pack . show

instance NFData EnumType

instance (Arbitrary a) => Arbitrary (Input a) where
  arbitrary =
    -- n <- choose (0, 5)
    -- m <- choose (0, 5)
    Input <$> arbitrary <*> arbitrary
  shrink = genericShrink

isLcs :: forall a. (Ord a, Show a) => Input a -> [a] -> Property
isLcs (Input xs ys) lcsCandidate
  | lcsCandidate `S.member` allLcss = property True
  | otherwise                       = counterexample msg $ property False
  where
    allLcss :: Set [a]
    allLcss = allLcsNaive xs ys
    msg = unlines
      [ "Mismatch:"
      , "candidate lcs: " ++ show lcsCandidate
      , "naive lcss:    " ++ show (toList allLcss)
      ]

prop_diffNaive :: Input EnumType -> Property
prop_diffNaive input@(Input xs ys) = isLcs input $ getLcs $ diffNaive xs ys

prop_diffTabular :: Input EnumType -> Property
prop_diffTabular input@(Input xs ys) = isLcs input $ getLcs $ diffTabular xs ys

prop_diffLinewise :: Input EnumType -> Property
prop_diffLinewise _input@(Input xs ys) =
  -- property $ isLcs _input $ getLcs (diffLinewise xs ys)
  property $ getLcs (diffTabular xs ys) == getLcs (diffLinewise xs ys)

prop_diffDiagonal :: Input EnumType -> Property
prop_diffDiagonal input@(Input xs ys) =
  isLcs input $ getLcs $ diffDiagonal xs ys

prop_DataAlgorithmDiff :: Input EnumType -> Property
prop_DataAlgorithmDiff input@(Input xs ys) =
  isLcs input $ mapMaybe getLcs' $ AlgDiff.getDiff xs ys
  where
    getLcs' :: AlgDiff.Diff EnumType -> Maybe EnumType
    getLcs' (AlgDiff.First _)  = Nothing
    getLcs' (AlgDiff.Second _) = Nothing
    getLcs' (AlgDiff.Both x _) = Just x

tests :: TestTree
tests = testGroup "all tests"
  [ QC.testProperty "diff naive" prop_diffNaive
  , QC.testProperty "diff tabular" prop_diffTabular
  , QC.testProperty "diff linewise" prop_diffLinewise
  , QC.testProperty "diff diagonal" prop_diffDiagonal
  , QC.testProperty "Data.Algorithm.diff" prop_DataAlgorithmDiff
  ]

-- main :: IO ()
-- main = defaultMain tests

makeConfig :: FilePath -> IO Config
makeConfig reportOutFile = do
  tmpDir <- getTemporaryDirectory
  return $ defaultConfig
    { forceGC    = True
    , reportFile = Just $ tmpDir </> reportOutFile
    , resamples  = 10000
    }

-- deriving instance (Generic a) => Generic (Diff a)
-- instance (Generic a, NFData a) => NFData (Diff a)

instance (NFData a) => NFData (Diff a) where
  rnf (Ins x d)   = rnf x `seq` rnf d
  rnf (Del x d)   = rnf x `seq` rnf d
  rnf (Cpy x d)   = rnf x `seq` rnf d
  rnf (Mod x y d) = rnf x `seq` rnf y `seq` rnf d
  rnf End         = ()

deriving instance (Generic a) => Generic (RevDiff a)
instance (Generic a, NFData a) => NFData (RevDiff a)

deriving instance (Generic a) => Generic (AlgDiff.Diff a)
instance (NFData a, Generic a) => NFData (AlgDiff.Diff a)

main :: IO ()
main = do
  let str1, str2, str1x100, str2x100 :: String
      str1      = "abcabba"
      str2      = "cbabac"
      str1x100  = concat $ replicate 100 "abcabba"
      str2x100  = concat $ replicate 100 "cbabac"
      input     = (str1, str2)
      inputx100 = (str1x100, str2x100)
      inputSimilar = (replicate 1000 'a' ++ "b", replicate 1000 'a' ++ "c")
      inputDifferent = (map chr $ take 1000 [9..], map chr $ take 1000 [2000..])
  void $ evaluate $ force input
  void $ evaluate $ force inputx100
  void $ evaluate $ force inputSimilar
  void $ evaluate $ force inputDifferent
  config <- makeConfig "diff-algorithms.html"
  defaultMainWith config [
      bgroup "abcabba vs cbabac"
        [
          -- bench "tabular" $ nf (uncurry diffTabular) input
        -- , bench "linewise" $ nf (uncurry diffLinewise) input
        -- , bench "diagonal" $ nf (uncurry diffDiagonal) input
          bench "FastDiff" $ nf (uncurry FastDiff.getDiff) input
        , bench "Data.Algorithm.Diff" $ nf (uncurry AlgDiff.getDiff) input
        ]
    , bgroup "abcabba x 100 vs cbabac x 100"
        [
          -- bench "tabular" $ nf (uncurry diffTabular) inputx100
        -- , bench "linewise" $ nf (uncurry diffLinewise) inputx100
        -- , bench "diagonal" $ nf (uncurry diffDiagonal) inputx100
          bench "FastDiff" $ nf (uncurry FastDiff.getDiff) inputx100
        , bench "Data.Algorithm.Diff" $ nf (uncurry AlgDiff.getDiff) inputx100
        ]
    , bgroup "a^1000b  vs a^1000c"
        [
          -- bench "tabular" $ nf (uncurry diffTabular) inputSimilar
        -- , bench "linewise" $ nf (uncurry diffLinewise) inputSimilar
        -- , bench "diagonal" $ nf (uncurry diffDiagonal) inputSimilar
          bench "FastDiff" $ nf (uncurry FastDiff.getDiff) inputSimilar
        , bench "Data.Algorithm.Diff" $ nf (uncurry AlgDiff.getDiff) inputSimilar
        ]
    , bgroup "different inputs"
        [
          -- bench "tabular" $ nf (uncurry diffTabular) inputDifferent
        -- , bench "linewise" $ nf (uncurry diffLinewise) inputDifferent
        -- , bench "diagonal" $ nf (uncurry diffDiagonal) inputDifferent
          bench "FastDiff" $ nf (uncurry FastDiff.getDiff) inputDifferent
        , bench "Data.Algorithm.Diff" $ nf (uncurry AlgDiff.getDiff) inputDifferent
        ]
    ]
