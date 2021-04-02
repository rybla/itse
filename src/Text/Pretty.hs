module Text.Pretty where

class Pretty a where
  pretty :: a -> Forest

  prettyShow :: a -> String
  prettyShow = show . pretty

  prettyPrint :: a -> IO ()
  prettyPrint = print . pretty

  {-# MINIMAL pretty #-}

data Forest = Branch [Forest] | Leaf String

instance Show Forest where
  show (Leaf str) = str
  show (Branch _fs) = unlines . map (go 0) $ _fs
    where
      go :: Int -> Forest -> String
      go lvl = \case
        Branch fs -> unlines . map (go (succ lvl)) $ fs
        Leaf str -> indent lvl ++ str
      indent n = concat . replicate n $ "  "

instance Semigroup Forest where
  Leaf str1 <> Leaf str2 = Branch [Leaf str1, Leaf str2]
  Leaf str1 <> Branch fs2 = Branch (Leaf str1 : fs2)
  Branch fs1 <> Leaf str2 = Branch (fs1 ++ [Leaf str2])
  Branch fs1 <> Branch fs2 = Branch (fs1 ++ fs2)
