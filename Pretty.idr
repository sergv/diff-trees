module Pretty

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State

%default total

%access public export

data Doc : Type where
  -- String des not contain '\n's here
  Str    : String -> Doc
  Line   : Doc
  Group  : Doc -> Doc
  Concat : Doc -> Doc -> Doc
  Nest   : Int -> Doc -> Doc
--  Alt    : Doc -> Doc -> Doc

implementation Semigroup Doc where
  (<+>) = Concat

implementation Monoid Doc where
  neutral = Str ""

text : String -> Doc
text x =
  case map Pretty.Str $ Prelude.Strings.split (== '\n') x of
    []      => neutral
    x :: xs => foldl (\acc, x => acc <+> Line <+> x) x xs

char : Char -> Doc
char = text . singleton

nest : Int -> Doc -> Doc
nest = Nest

||| Hard newline
line : Doc
line = Line

infixl 5 <++>, </>

(<++>) : Doc -> Doc -> Doc
(<++>) x y = x <+> text " " <+> y

(</>) : Doc -> Doc -> Doc
(</>) x y = x <+> line <+> y

prettyShow : (Show a) => a -> Doc
prettyShow = text . show

enclose : Doc -> Doc -> Doc -> Doc
enclose l r x = l <+> x <+> r

lbracket : Doc
lbracket = text "["

rbracket : Doc
rbracket = text "]"

comma : Doc
comma = text ","

interface Pretty a where
  export
  pretty : a -> Doc

implementation Pretty Int where
  pretty = prettyShow

implementation Pretty Double where
  pretty = prettyShow

implementation Pretty Char where
  pretty = prettyShow

implementation Pretty String where
  pretty = prettyShow

implementation Pretty () where
  pretty = prettyShow

implementation Pretty Integer where
  pretty = prettyShow

implementation Pretty Nat where
  pretty = prettyShow

implementation Pretty Bool where
  pretty = prettyShow

implementation (Pretty a) => Pretty (Maybe a) where
  pretty Nothing  = text "Nothing"
  pretty (Just x) = pretty x

--implementation (List a) => Pretty (List a) where
--  pretty xs = enclose lbracket rbracket
--            $

private
data Builder = B (String -> String)

private
runBuilder : Builder -> String -> String
runBuilder (B f) = f

private
implementation Semigroup Builder where
  (<+>) (B f) (B g) = B $ f . g

private
flatten : Doc -> Doc
flatten s@(Str _)    = s
flatten Line         = neutral
flatten (Group g)    = flatten g
flatten (Concat x y) = Concat (flatten x) (flatten y)
flatten (Nest k d)   = Nest k $ flatten d

private
record PPEnv where
  constructor MkPPEnv
  indent    : Int
  width     : Int

private
record PPState where
  constructor MkPPState
  lineWidth : Int

private
getIndent : (MonadReader PPEnv m) => m Int
getIndent = indent <$> ask

private
layOut : Doc -> ReaderT PPEnv (State PPState) Builder
layOut (Str s)      = do
  lift $ modify (\env => record { lineWidth = cast (length s) + lineWidth env } env)
  pure $ B (s <+>)
layOut Line         = do
  indent <- getIndent
  let indentation = pack $ replicate (cast indent) ' '
  lift $ modify (\env => record { lineWidth = indent } env)
  pure $ B (strCons '\n' . (indentation <+>))
layOut z@(Group d)    = layOut $ assert_smaller z $ flatten d
layOut (Concat x y) = [| layOut x <+> layOut y |]
layOut (Nest k d)   = do
  indent <- getIndent
  local (record { indent = indent + k }) $ layOut d

-- layOut doc = do
--   indent <- getIndent
--   let indentation = pack $ replicate (cast indent) ' '
--   case doc of
--     Str s      =>
--       pure $ B (s <+>)
--     Line       =>
--       pure $ B (strCons '\n' . (indentation <+>))
--     Group d    => layOut $ flatten d
--     Concat x y =>
--       [| layOut x <+> layOut y |]
--     Nest k d   =>
--       local (record { indent = indent + k }) $ layOut d

export
renderW : Int -> Doc -> String
renderW width doc =
  runBuilder (fst $ runIdentity $ runStateT (runReaderT (layOut doc) env) state) ""
  where
    env : PPEnv
    env = MkPPEnv 0 width
    state : PPState
    state = MkPPState 0

export
display : (Pretty a) => a -> String
display = renderW 80 . pretty
