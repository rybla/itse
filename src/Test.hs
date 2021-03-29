module Test where

class Expr a

data Term = Term String

instance Expr Term

data T2 = T2 Bool

data T3 = T3 Int

-- test_patterguard ma mb
--   | Just a <- ma,
--     let x = a,
--     _ <- Just (),
--     Just b <- mb =
--     Just (x + b)
--   | otherwise = Nothing
