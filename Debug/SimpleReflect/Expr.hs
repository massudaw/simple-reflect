{-# LANGUAGE TupleSections #-}
{-# LANGUAGE CPP #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Debug.SimpleReflect.Expr
-- Copyright   :  (c) 2008-2014 Twan van Laarhoven
-- License     :  BSD-style
--
-- Maintainer  :  twanvl@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Simple reflection of haskell expressions containing variables.
--
-----------------------------------------------------------------------------
module Debug.SimpleReflect.Expr
    ( -- * Construction
      Expr(..)
    , FromExpr(..)
    , intExpr,reduced,doubleExpr
    , var, fun, Associativity(..), op
      -- * Evaluating
    , expr, reduce, reduction
    ) where

import Debug.Trace
import Data.List
import Data.Maybe
import Data.Monoid
#if MIN_VERSION_base(4,9,0) && !(MIN_VERSION_base(4,11,0))
import Data.Semigroup
#endif
import Control.Applicative

------------------------------------------------------------------------------
-- Data type
------------------------------------------------------------------------------
data Operation = Operation
    {associativity :: Associativity
    ,precedence :: Int
    ,operatorName :: String}

-- | A reflected expression
data Expr
   = Expr
   { showExpr'   :: Int -> ShowS  -- ^ Show with the given precedence level
   , intExpr'    :: Maybe Integer -- ^ Integer value?
   , doubleExpr' :: Maybe Double  -- ^ Floating value?
   , reduced'    :: Maybe Expr    -- ^ Next reduction step
   }
   | BinExpr
   { operation :: Expr -> Expr -> Expr
   , argL :: Expr    -- ^ Next reduction step
   , argR :: Expr    -- ^ Next reduction step
   }

showExpr  r@(Expr {}) p = showExpr' r p
showExpr (BinExpr expr i j ) p | isConstant i && isConstant j && traceShow ("Both constant" ,i,j) False=  undefined
showExpr (BinExpr expr argL argR) p  =  showExpr (expr argL argR) p

intExpr (Expr _ i _ _ ) = i
intExpr _ = Nothing

doubleExpr (Expr _ _ i _ ) = i
doubleExpr _ = Nothing

reduced (Expr _ _ _ i ) = i
reduced (BinExpr e l r) =  reduced (e l r)

rewriteReducedBinOp bin@(BinExpr expr argL argR )=
  let rr = expr argL argR
  in fromMaybe bin $
     withReduce2 expr <$> reduced argL   <*> reduced argR
     <|> (\ l -> withReduce2 expr  l argR) <$> reduced argL
     <|> (\ r -> withReduce2 expr  argL r ) <$> reduced argR
     <|> fromInteger <$> intExpr    rr
     <|> fromDouble  <$> doubleExpr rr
rewriteReducedBinOp i = i




instance Show Expr where
 showsPrec = flip showExpr


-- | Default expression
emptyExpr :: Expr
emptyExpr = Expr { showExpr'   = \_ -> showString ""
                 , intExpr'    = Nothing
                 , doubleExpr' = Nothing
                 , reduced'    = Nothing
                 }

------------------------------------------------------------------------------
-- Lifting and combining expressions
------------------------------------------------------------------------------

-- | A variable with the given name
var :: String -> Expr
var s = emptyExpr { showExpr' = \_ -> showString s }

lift :: Show a => a -> Expr
lift x = emptyExpr { showExpr' = \p -> showsPrec p x }

-- | This data type specifies the associativity of operators: left, right or none.
data Associativity = InfixL | Infix | InfixR deriving Eq

-- | An infix operator with the given associativity, precedence and name
op :: Associativity -> Int -> String -> Expr -> Expr -> Expr
op fix prec opName a b = emptyExpr { showExpr' = showFun }
 where showFun p = showParen (p > prec)
                     $ showExpr a (if fix == InfixL then prec else prec + 1)
                     . showString opName
                     . showExpr b (if fix == InfixR then prec else prec + 1)

------------------------------------------------------------------------------
-- Adding numeric results
------------------------------------------------------------------------------

iOp :: (Expr -> Expr) -> (Integer -> Integer) -> Expr -> Expr
iOp2 :: (Expr -> Expr -> Expr) -> (Integer -> Integer -> Integer) -> Expr -> Expr -> Expr
dOp :: (Expr -> Expr) -> (Double -> Double) -> Expr -> Expr
dOp2 :: (Expr -> Expr -> Expr) -> (Double -> Double -> Double) -> Expr -> Expr -> Expr

iOp  r f a   = (r a  ) { intExpr'    = f <$> intExpr    a }
iOp2 r f a b = (r a b) { intExpr'    = f <$> intExpr    a <*> intExpr    b }
dOp  r f a   = (r a  ) { doubleExpr' = f <$> doubleExpr a }
dOp2 r f a b = (r a b) { doubleExpr' = f <$> doubleExpr a <*> doubleExpr b }

withReduce :: (Expr -> Expr) -> (Expr -> Expr)
withReduce r a    = let rr = r a
                        reductions = withReduce r <$> reduced a
                               <|> fromInteger <$> intExpr    rr
                               <|> fromDouble  <$> doubleExpr rr
                    in case rr of
                          Expr {} -> rr { reduced' =  reductions}
                          BinExpr op r l  ->  fromMaybe (distributeConstant op r l ) reductions
withReduce2 :: (Expr -> Expr -> Expr) -> (Expr -> Expr -> Expr)
withReduce2 r a b = let rr = r a b
                        ra = reduced a
                        rb = reduced b
                            in
                    rr { reduced' =
                              (\a' b' -> withReduce2 r a' b') <$> ra <*> rb
                               <|> (\a' -> withReduce2 r a' b) <$> ra
                               <|> (\b' -> withReduce2 r a b') <$> rb
                               <|> fromInteger <$> intExpr    rr
                               <|> fromDouble  <$> doubleExpr rr
                       }

withReduce2AnihilateAndIdentity :: Expr -> Expr -> (Expr -> Expr -> Expr) -> (Expr -> Expr -> Expr)
withReduce2AnihilateAndIdentity zero one r a b =
                    let
                      rr = identityRule one a b (anihilateRule zero a b (distributeConstant r a b))
                      ra = reduced a
                      rb = reduced b
                      reductions = (\a' b' -> identityRule one a' b' (anihilateRule zero a' b' (withReduce2AnihilateAndIdentity zero one (distributeConstant r)a' b'))) <$> ra <*> rb
                               <|> (\a' -> if  a' == one then b else (if abs a' < 1e-15 then zero else withReduce2AnihilateAndIdentity zero one  (distributeConstant r) a' b)) <$> ra
                               <|> (\b' -> if  b' == one then a else (if abs b' < 1e-15 then zero else withReduce2AnihilateAndIdentity zero one (distributeConstant r) a b')) <$> rb
                               <|> fromInteger <$> intExpr    rr
                               <|> fromDouble  <$> doubleExpr rr
                    in  case rr of
                            Expr {} -> rr {reduced' = reductions }
                            BinExpr op r l ->  fromMaybe (distributeConstant op r l) reductions

isConstant l = isJust (intExpr l) || isJust (doubleExpr l)
isBinExpr (BinExpr _ _ _ ) = True
isBinExpr _ = False

--distributeConstant op a b@(BinExpr exr l r ) | traceShow (op a b, isConstant a,(isConstant l,l),(isConstant r,r)) False = undefined
--distributeConstant op b@(BinExpr exr l r ) a | traceShow (op a b, isConstant a,(isConstant l,l),(isConstant r,r)) False = undefined
--distributeConstant op  a@(BinExpr exr1 l1 r1) b@(BinExpr exr l r )| traceShow (op a b, isConstant a,("l",isConstant l,l),("r",isConstant r,r),("r1",isConstant r1,r1),("l1",isConstant l1,l1)) False = undefined
--- If we can distribute to left side and untag BinExpr on right side
distributeConstant op (BinExpr expr1 l1 r1) (BinExpr expr l r) | isConstant l1 && isConstant l=  distributeConstant expr1 (rewriteReducedBinOp $ BinExpr op l1 l) (expr r1 r)
distributeConstant op (BinExpr expr1 l1 r1) (BinExpr expr l r) | isConstant l1 && isConstant r=  distributeConstant expr1 (rewriteReducedBinOp $ BinExpr op l1 r) (expr r1 l)
distributeConstant op (BinExpr expr1 l1 r1) (BinExpr expr l r) | isConstant r1 && isConstant r=  distributeConstant expr1 (rewriteReducedBinOp $ BinExpr op r1 r) (expr l1 l)
distributeConstant op (BinExpr expr1 l1 r1) (BinExpr expr l r) | isConstant l  && isConstant r1=  distributeConstant expr1 (rewriteReducedBinOp $ BinExpr op r1 l) (expr l1 r)
--- If only one side is a BinExpr search for constants and simplify
distributeConstant op (BinExpr expr l r ) a | isConstant l && isConstant a =  BinExpr expr (rewriteReducedBinOp $ BinExpr op l a) r
distributeConstant op (BinExpr expr l r ) a | isConstant r && isConstant a =  BinExpr expr l (rewriteReducedBinOp $ BinExpr op r a)
distributeConstant op a (BinExpr expr l r) | isConstant l && isConstant a =  BinExpr expr (rewriteReducedBinOp $ BinExpr op l a) r
distributeConstant op a (BinExpr expr l r) | isConstant r && isConstant a =  BinExpr expr l (rewriteReducedBinOp $ BinExpr op r a)
--- Move the constant to the top
distributeConstant op (BinExpr expr l r ) a | isConstant r =  BinExpr expr  (op l a)  r
distributeConstant op (BinExpr expr l r ) a | isConstant l =  BinExpr expr  l (op r a)
distributeConstant op a (BinExpr expr l r) | isConstant r =  BinExpr expr  (op l a)  r
distributeConstant op a (BinExpr expr l r) | isConstant l =  BinExpr expr  l (op r a)
-- If is constant keep tagged as BinExpr
distributeConstant op a b | isConstant a && isConstant b = op a b
distributeConstant op a b | isConstant a || isConstant b = BinExpr op a b
-- Don't tag if nothing is constant
distributeConstant op a b = op a b

distributeUnary op (BinExpr expr l r ) | isConstant l = BinExpr expr (withReduce op l ) r
distributeUnary op (BinExpr expr l r ) | isConstant r = BinExpr expr l (withReduce op r )
distributeUnary op expr = op expr


identityRule ident = (\a b r  -> if a == ident then b else  (if b == ident then a else r))
anihilateRule zero = (\a b r  -> if abs a < 1e-15 || abs b < 1e-15 then zero else  r)


withReduce2Identity :: Expr -> (Expr -> Expr -> Expr) -> (Expr -> Expr -> Expr)
withReduce2Identity ident r a b =
                    let rr = identityRule ident a b (r a b)
                        ra = reduced a
                        rb = reduced b
                        red = (\a' b' -> if    a' == ident  then b' else  (if b' == ident then a' else withReduce2Identity ident r a' b')) <$> ra <*> rb
                                     <|> (\a' -> if  a' == ident then b else withReduce2Identity ident r a' b) <$> ra
                                     <|> (\b' -> if  b' == ident then a else withReduce2Identity ident r a b') <$> rb
                                     <|> fromInteger <$> intExpr    rr
                                     <|> fromDouble  <$> doubleExpr rr
                    in
                    case rr of
                      Expr {} ->
                          rr { reduced' =  red }
                      BinExpr op r l -> fromMaybe (distributeConstant op r l) red


------------------------------------------------------------------------------
-- Function types
------------------------------------------------------------------------------

-- | Conversion from @Expr@ to other types
class FromExpr a where
    fromExpr :: Expr -> a

instance FromExpr Expr where
    fromExpr = id

instance (Show a, FromExpr b) => FromExpr (a -> b) where
    fromExpr f a = fromExpr $ op InfixL 10 " " f (lift a)

-- | A generic, overloaded, function variable
fun :: FromExpr a => String -> a
fun = fromExpr . var

------------------------------------------------------------------------------
-- Forcing conversion & evaluation
------------------------------------------------------------------------------

-- | Force something to be an expression.
expr :: Expr -> Expr
expr = id

-- | Reduce (evaluate) an expression once.
--
--   For example @reduce (1 + 2 + 3 + 4)  ==  3 + 3 + 4@
reduce :: Expr -> Expr
reduce e = maybe e id (reduced e)

-- | Show all reduction steps when evaluating an expression.
reduction :: Expr -> [Expr]
reduction e0 = e0 : unfoldr (\e -> do e' <- reduced e; return (e',e')) e0

------------------------------------------------------------------------------
-- Numeric classes
------------------------------------------------------------------------------

instance Eq Expr where
    Expr{ intExpr'    = Just a } == Expr{ intExpr'    = Just b }  =  a == b
    Expr{ doubleExpr' = Just a } == Expr{ doubleExpr' = Just b }  =  a == b
    a                           == b                            =  show a == show b

instance Ord Expr where
    compare Expr{ intExpr'    = Just a } Expr{ intExpr'    = Just b }  =  compare a b
    compare Expr{ doubleExpr' = Just a } Expr{ doubleExpr' = Just b }  =  compare a b
    compare a                           b                            =  compare (show a) (show b)
    min = fun "min" `iOp2` min `dOp2` min
    max = fun "max" `iOp2` max `dOp2` max

instance Num Expr where
    (+)    = withReduce2Identity 0 $ op InfixL 6 " + " `iOp2` (+)   `dOp2` (+)
    (-)    = withReduce2Identity 0 $ op InfixL 6 " - " `iOp2` (-)   `dOp2` (-)
    (*)    = withReduce2AnihilateAndIdentity 0 1 $ op InfixL 7 " * " `iOp2` (*)   `dOp2` (*)
    negate = withReduce  $ distributeUnary (fun "negate" `iOp` negate `dOp` negate)
    abs    = withReduce  $ fun "abs"    `iOp` abs    `dOp` abs
    signum = withReduce  $ fun "signum" `iOp` signum `dOp` signum
    fromInteger i = (lift i)
                     { intExpr'    = Just i
                     , doubleExpr' = Just $ fromInteger i }

instance Real Expr where
    toRational someExpr = case (doubleExpr someExpr, intExpr someExpr) of
          (Just d,_) -> toRational d
          (_,Just i) -> toRational i
          _          -> error $ "not a rational number: " ++ show someExpr

instance Integral Expr where
    quotRem a b = (quot a b, rem a b)
    divMod  a b = (div  a b, mod a b)
    quot = withReduce2 $ op InfixL 7 " `quot` " `iOp2` quot
    rem  = withReduce2 $ op InfixL 7 " `rem` "  `iOp2` rem
    div  = withReduce2 $ op InfixL 7 " `div` "  `iOp2` div
    mod  = withReduce2 $ op InfixL 7 " `mod` "  `iOp2` mod
    toInteger someExpr = case intExpr someExpr of
          Just i -> i
          _      -> error $ "not an integer: " ++ show someExpr

instance Fractional Expr where
    (/)   = withReduce2 $ op InfixL 7 " / " `dOp2` (/)
    recip = withReduce  $ fun "recip"  `dOp` recip
    fromRational r = fromDouble (fromRational r)

instance RealFrac Expr where
   --round = withReduce $ fun "round" `dOp` round
   --floor = withReduce $ fun "floor" `dOp` floor
   --ceiling = withReduce $ fun "ceiling" `dOp` ceiling
   --truncate = withReduce $ fun "truncate" `dOp` truncate

instance RealFloat Expr where
   atan2 = withReduce2 $ fun "atan2" `dOp2` atan2

fromDouble :: Double -> Expr
fromDouble d = (lift d) { doubleExpr' = Just d }

instance Floating Expr where
    pi    = (var "pi") { doubleExpr' = Just pi }
    exp   = withReduce  $ fun "exp"   `dOp` exp
    sqrt  = withReduce  $ fun "sqrt"  `dOp` sqrt
    log   = withReduce  $ fun "log"   `dOp` log
    (**)  = withReduce2 $ op InfixR 8 "**" `dOp2` (**)
    sin   = withReduce  $ fun "sin"   `dOp` sin
    cos   = withReduce  $ fun "cos"   `dOp` cos
    sinh  = withReduce  $ fun "sinh"  `dOp` sinh
    cosh  = withReduce  $ fun "cosh"  `dOp` cosh
    asin  = withReduce  $ fun "asin"  `dOp` asin
    acos  = withReduce  $ fun "acos"  `dOp` acos
    atan  = withReduce  $ fun "atan"  `dOp` atan
    asinh = withReduce  $ fun "asinh" `dOp` asinh
    acosh = withReduce  $ fun "acosh" `dOp` acosh
    atanh = withReduce  $ fun "atanh" `dOp` atanh

instance Enum Expr where
    succ   = withReduce  $ fun "succ" `iOp` succ `dOp` succ
    pred   = withReduce  $ fun "pred" `iOp` pred `dOp` pred
    toEnum = fun "toEnum"
    fromEnum = fromEnum . toInteger
    enumFrom       a     = map fromInteger $ enumFrom       (toInteger a)
    enumFromThen   a b   = map fromInteger $ enumFromThen   (toInteger a) (toInteger b)
    enumFromTo     a   c = map fromInteger $ enumFromTo     (toInteger a)               (toInteger c)
    enumFromThenTo a b c = map fromInteger $ enumFromThenTo (toInteger a) (toInteger b) (toInteger c)

instance Bounded Expr where
    minBound = var "minBound"
    maxBound = var "maxBound"

------------------------------------------------------------------------------
-- Other classes
------------------------------------------------------------------------------

#if MIN_VERSION_base(4,9,0)
instance Semigroup Expr where
    (<>) = withReduce2 $ op InfixR 6 " <> "
#endif

instance Monoid Expr where
    mempty = var "mempty"
#if !(MIN_VERSION_base(4,11,0))
    mappend = withReduce2 $ op InfixR 6 " <> "
#endif
    mconcat = fun "mconcat"

