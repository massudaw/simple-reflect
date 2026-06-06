-- | Regression tests for Debug.SimpleReflect's simplification algorithm.
--
-- These are plain string comparisons against the rendered form of an
-- expression (or of its full reduction chain), so the suite only depends on
-- @base@ and the library itself. Run with @cabal test@.
module Main (main) where

import Debug.SimpleReflect
import Debug.SimpleReflect.Expr

import Data.List   (intercalate)
import Control.Monad (forM)
import System.Exit (exitFailure)

-- | Render every reduction step, joined by @ => @.
steps :: Expr -> String
steps = intercalate " => " . map show . reduction

-- | (description, actual rendering, expected rendering)
type Case = (String, String, String)

cases :: [Case]
cases =
  -- Identity elements ------------------------------------------------------
  [ ("a + 0 = a",            show (a + 0),  "a")
  , ("0 + a = a",            show (0 + a),  "a")
  , ("a - 0 = a",            show (a - 0),  "a")
  , ("x * 1 = x",            show (x * 1),  "x")
  , ("1 * x = x",            show (1 * x),  "x")
  , ("a / 1 = a",            show (a / 1),  "a")
  , ("a ** 1 = a",           show (a ** 1), "a")
  , ("a / (2 - 1) = a",      steps (a / (2 - 1)),         "a => a")
  , ("a ** (2 - 1) = a",     steps (a ** (2 - 1)),        "a => a")

  -- Annihilator ------------------------------------------------------------
  , ("x * 0 = 0",            show (x * 0),  "0")
  , ("0 * x = 0",            show (0 * x),  "0")
  , ("x * (-1) = -x",        show (x * (-1)),             "-x")
  , ("(-1) * x = -x",        show ((-1) * x),             "-x")
  , ("(10 - 3 - 2) * (-1)",  steps ((10 - 3 - 2) * (-1)), "-(10 - 3 - 2) => -(10 - 3 - 2) => -(7 - 2) => -5 => -5")

  -- Subtraction is NOT commutative: 0 - a must not collapse to a -----------
  , ("0 - a = -a",           show (0 - a),  "-a")
  , ("a - b unchanged",      show (a - b),  "a - b")
  , ("0 - (a - 0) = -a",     steps (0 - (a - 0)),         "-a => -a")
  , ("(5 - 0) - a = 5 - a",  show ((5 - 0) - a),          "5 - a")

  -- Numeric reduction chains still fold ------------------------------------
  , ("reduce 0 - 7",         steps (0 - 7),               "-7 => -7 => -7")
  , ("reduce 7 - 0",         show (7 - 0 :: Expr),        "7")
  , ("reduce 10 - 3 - 2",    steps (10 - 3 - 2),          "10 - 3 - 2 => 10 - 3 - 2 => 7 - 2 => 5")
  , ("reduce 1+2*(3+4)",     steps (1 + 2 * (3 + 4)),
        "1 + 2 * (3 + 4) => 1 + 2 * 7 => 1 + 14 => 15")

  -- Constant folding for * (commutative + associative) ---------------------
  , ("2 * (x * 3) = x * 6",        show (2 * (x * 3)),          "x * 6")
  , ("2 * (3 * (x * 4)) = x * 24", show (2 * (3 * (x * 4))),    "x * 24")
  , ("nested * chain folds",       show (2 * (x * (3 * (y * 4)))), "y * x * 24")

  -- Soundness: constants must NOT cross non-commutative operators ----------
  , ("2 * (x - 3) untouched", show (2 * (x - 3)),          "2 * (x - 3)")
  , ("2*(x-3)*4 = 8*(x-3)",   show (2 * (x - 3) * 4),      "8 * (x - 3)")
  , ("5 * (x / 2) normalization", show (5 * (x / 2)),      "x * 2.5")
  , ("(x * 3) / 2 = x * 1.5", show ((x * 3) / 2),          "x * 1.5")
  , ("(a - b) * 3 untouched", show ((a - b) * 3),          "(a - b) * 3")
  , ("2 * (x + 3) untouched", show (2 * (x + 3)),          "2 * (x + 3)")

  -- Additive constant folding (commutative + associative) ------------------
  , ("2 + (x + 3) = x + 5",   show (2 + (x + 3)),          "x + 5")
  , ("(x + 3) + 2 = x + 5",   show ((x + 3) + 2),          "x + 5")
  , ("2 + x + 3 = 5 + x",     show (2 + x + 3),            "5 + x")
  , ("x + 1 + 2 = x + 3",     show (x + 1 + 2),            "x + 3")
  , ("1+(2+(3+x)) = 6 + x",   show (1 + (2 + (3 + x))),    "6 + x")
  , ("x + 2 + 3 + y folds",   show (x + 2 + 3 + y),        "x + y + 5")
  , ("sum [1..5] stays flat", show (sum [1..5] :: Expr),   "1 + 2 + 3 + 4 + 5")
  -- ...but additive folding must NOT cross other operators:
  , ("2 + 3 * x untouched",   show (2 + 3 * x),            "2 + 3 * x")
  , ("2 + (x - 3) normalization", show (2 + (x - 3)),          "x - 1")
  , ("x + 2 - 3 normalization",   show (x + 2 - 3),            "x - 1")

  -- Unary minus rendering --------------------------------------------------
  , ("negate a = -a",             show (negate a),         "-a")
  , ("negate (a - b) = -(a - b)", show (negate (a - b)),   "-(a - b)")
  , ("negate (x * y) = -x * y",   show (negate (x * y)),   "-x * y")
  , ("negate a - b = -a - b",     show (negate a - b),     "-a - b")
  , ("negate (x * 3) = x * (-3)", show (negate (x * 3)),   "x * (-3)")
  , ("negate (2 * x) = (-2) * x", show (negate (2 * x)),   "(-2) * x")
  , ("abs a unchanged",           show (abs a),            "abs a")
  , ("signum a unchanged",        show (signum a),         "signum a")
  , ("negate (negate a) = a",     show (negate (negate a)), "a")
  , ("negate 0 = 0",              show (negate 0),         "0")
  , ("negate (negate 0) = 0",     show (negate (negate 0)), "0")
  , ("negate (negate (10 - 3 - 2))", steps (negate (negate (10 - 3 - 2))), "5 => 5 => 5 => 5 => 5 => 5")
  , ("abs (negate a) = abs a",    show (abs (negate a)),   "abs a")
  , ("abs (abs a) = abs a",       show (abs (abs a)),      "abs a")
  , ("signum (signum a) = signum a", show (signum (signum a)), "signum a")
  , ("abs (negate (10 - 3 - 2))",  steps (abs (negate (10 - 3 - 2))), "abs 5 => abs 5 => abs 5 => abs 5 => abs 5 => 5")
  , ("abs (abs (10 - 3 - 2))",     steps (abs (abs (10 - 3 - 2))), "abs (10 - 3 - 2) => abs (10 - 3 - 2) => abs (7 - 2) => abs 5 => abs 5 => 5")
  , ("signum (signum (10 - 3 - 2))", steps (signum (signum (10 - 3 - 2))), "signum (10 - 3 - 2) => signum (10 - 3 - 2) => signum (7 - 2) => signum 5 => signum 1 => 1")
  , ("recip 1 = 1",              show (recip 1),          "1.0")
  , ("recip (recip a) = a",       show (recip (recip a)),  "a")
  , ("recip (recip (10 - 3 - 2))", steps (recip (recip (10 - 3 - 2))), "10 - 3 - 2 => 10 - 3 - 2 => 7 - 2 => 5 => recip 0.2 => 5.0")
  , ("recip (recip (a - b))",     show (recip (recip (a - b))), "a - b")
  , ("recip 0 = Infinity",       steps (recip 0),         "recip 0 => Infinity")
  , ("recip (fromInteger 1) = 1", show (recip (fromInteger 1 :: Expr)), "1")
  , ("negate (negate (a - b))",   show (negate (negate (a - b))), "a - b")
  , ("abs (negate (a - b))",      show (abs (negate (a - b))), "abs (a - b)")
  , ("abs (abs (a - b))",         show (abs (abs (a - b))), "abs (a - b)")
  , ("signum (signum (a - b))",   show (signum (signum (a - b))), "signum (a - b)")
  , ("negate 0.0 = 0.0",          show (negate (0.0 :: Expr)), "0.0")
  , ("negate (negate 0.0) = 0.0", show (negate (negate (0.0 :: Expr))), "0.0")

  -- Specific division and multiplication-by-negative-one tests ------------
  , ("x / y = x / y",            show (x / y),            "x / y")
  , ("x / 5 = x * 0.2",          show (x / 5),            "x * 0.2")
  , ("5 / x = 5 / x",            show (5 / x),            "5 / x")
  , ("5 / 2 = 5 / 2",            show (5 / 2 :: Expr),    "5 / 2")
  , ("1 / recip x = x",          show (1 / recip x),      "x")
  , ("(a / 2) * 2 = a * 1.0",    show ((a / 2) * 2),      "a * 1.0")
  , ("(a * 2) / 2 = a * 1.0",    show ((a * 2) / 2),      "a * 1.0")
  , ("(-1) * (-x) = x",          show ((-1) * (-x)),      "x")
  , ("(-1) * (-1) = 1",          show (((-1) :: Expr) * (-1)), "1")
  , ("negate (x + 5) untouched", show (negate (x + 5)),       "-(x + 5)")
  , ("abs (x * 5) = abs x * abs 5", show (abs (x * 5)),       "abs x * abs 5")
  , ("recip (x * 5) = recip x / 5", show (recip (x * 5)),     "recip x / 5")


  -- Specific exponentiation identity tests ---------------------------------
  , ("1 ** a = 1",               show (1 ** a),           "1")
  , ("a ** 0 = 1",               show (a ** 0),           "1")
  , ("0 ** a = 0",               show (0 ** a),           "0")
  , ("0 ** 0 = 1",               show (0 ** 0 :: Expr),   "1")
  , ("1.0 ** a = 1",             show (1.0 ** a),         "1")
  , ("a ** 0.0 = 1",             show (a ** 0.0),         "1")
  , ("0.0 ** a = 0",             show (0.0 ** a),         "0")
  , ("a ** 1.0 = a",             show (a ** 1.0),         "a")
  , ("(2 - 1) ** a = 1",         steps ((2 - 1) ** a),    "1 => 1")
  , ("(2 - 2) ** a = 0",         steps ((2 - 2) ** a),    "0 => 0")
  , ("a ** (2 - 2) = 1",         steps (a ** (2 - 2)),    "1 => 1")

  -- Specific exponential & logarithmic tests -------------------------------
  , ("exp 0 = 1",                show (exp 0 :: Expr),    "1")
  , ("log 1 = 0",                show (log 1 :: Expr),    "0")
  , ("log (exp a) = a",          show (log (exp a)),      "a")
  , ("exp (log a) = a",          show (exp (log a)),      "a")
  , ("log (exp (2 - 1))",        steps (log (exp (2 - 1))), "2 - 1 => 2 - 1 => 1 => log 2.718281828459045 => 1.0")

  -- Specific square root & radical tests -----------------------------------
  , ("sqrt 0 = 0",               show (sqrt 0 :: Expr),   "0")
  , ("sqrt 1 = 1",               show (sqrt 1 :: Expr),   "1")
  , ("sqrt (recip a) = recip (sqrt a)", show (sqrt (recip a)), "recip (sqrt a)")
  , ("sqrt (recip (2 - 1))",     steps (sqrt (recip (2 - 1))), "1 => 1 => 1 => 1 => 1")

  -- Specific trigonometric & hyperbolic tests ------------------------------
  , ("sin 0 = 0",                show (sin 0 :: Expr),    "0")
  , ("cos 0 = 1",                show (cos 0 :: Expr),    "1")
  , ("sinh 0 = 0",               show (sinh 0 :: Expr),   "0")
  , ("cosh 0 = 1",               show (cosh 0 :: Expr),   "1")
  , ("asin 0 = 0",               show (asin 0 :: Expr),   "0")
  , ("atan 0 = 0",               show (atan 0 :: Expr),   "0")
  , ("sin (negate a) = -sin a",  show (sin (negate a)),   "-sin a")
  , ("cos (negate a) = cos a",   show (cos (negate a)),   "cos a")
  , ("sinh (negate a) = -sinh a", show (sinh (negate a)), "-sinh a")
  , ("cosh (negate a) = cosh a",  show (cosh (negate a)), "cosh a")

  -- Specific Enum (successor/precursor) tests ------------------------------
  , ("succ (pred a) = a",        show (succ (pred a)),    "a")
  , ("pred (succ a) = a",        show (pred (succ a)),    "a")
  , ("succ (pred (10 - 3 - 2))", steps (succ (pred (10 - 3 - 2))), "10 - 3 - 2 => 10 - 3 - 2 => 7 - 2 => 5 => succ 4 => 5")

  -- Specific Monoid/Semigroup tests ----------------------------------------
  , ("mempty <> a = a",          show (mempty <> a),      "a")
  , ("a <> mempty = a",          show (a <> mempty),      "a")
  , ("(mempty <> (2 - 1)) <> a", steps ((mempty <> (2 - 1)) <> a), "(2 - 1) <> a => (2 - 1) <> a => 1 <> a => 1 <> a")






  -- Sign normalization: a + (negation) => a - x, and vice versa -----------
  , ("a + negate b = a - b",      show (a + negate b),     "a - b")
  , ("a - negate b = a + b",      show (a - negate b),     "a + b")
  , ("negate a + b = b - a",      show (negate a + b),     "b - a")
  , ("x + (-1) = x - 1",          show (x + (-1)),         "x - 1")
  , ("(-1) + x = x - 1",          show ((-1) + x),         "x - 1")
  , ("x - (-3) = x + 3",          show (x - (-3)),         "x + 3")
  , ("x + (-1.5) = x - 1.5",      show (x + (-1.5)),       "x - 1.5")
  , ("(-1.5) + x = x - 1.5",      show ((-1.5) + x),       "x - 1.5")
  , ("x - (-1.5) = x + 1.5",      show (x - (-1.5)),       "x + 1.5")
  , ("x + 2 + (-3) = x - 1",      show (x + 2 + (-3)),     "x - 1")
  , ("x + negate (a+b)",          show (x + negate (a + b)), "x - (a + b)")

  -- Documented examples (README / module haddock) --------------------------
  , ("sum [1..5]",       show (sum [1..5] :: Expr),       "1 + 2 + 3 + 4 + 5")
  , ("foldr1 f [a,b,c]", show (foldr1 f [a,b,c]),         "f a (f b c)")
  , ("iterate f x",      show (take 5 (iterate f x)),
        "[x,f x,f (f x),f (f (f x)),f (f (f (f x)))]")
  ]

main :: IO ()
main = do
    results <- forM cases $ \(label, actual, expected) -> do
        let ok = actual == expected
        if ok
          then putStrLn $ "PASS  " ++ label
          else putStrLn $ "FAIL  " ++ label
                       ++ "\n        expected: " ++ expected
                       ++ "\n        actual:   " ++ actual
        return ok
    let passed = length (filter id results)
        total  = length results
    putStrLn $ "\n" ++ show passed ++ " / " ++ show total ++ " passed"
    if passed == total then return () else exitFailure
