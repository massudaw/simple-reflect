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
-- | A binary operator together with the algebraic laws needed to decide
--   whether constants may safely be rearranged through nested applications
--   of it. Only operators that are commutative and associative may have
--   their constants merged (and then only with other applications of the
--   /same/ operator), which keeps simplification sound for non-commutative
--   operators such as @-@ and @/@.
data BinOp = BinOp
    { applyBinOp    :: Expr -> Expr -> Expr     -- ^ Build the result expression (handles showing and numeric folding)
    , opName        :: String                  -- ^ Identifies the operator, so only matching operators are merged
    , commutative   :: Bool                     -- ^ Is  @a `op` b@  ==  @b `op` a@ ?
    , associative   :: Bool                     -- ^ Is  @(a `op` b) `op` c@  ==  @a `op` (b `op` c)@ ?
    , onLeftIdentity :: Maybe (Expr -> Expr)    -- ^ If @Just f@, then @ident `op` b@ simplifies to @f b@ (e.g. @id@ for @+@, @negate@ for @-@)
    }

-- | A reflected expression
data Expr
   = Expr
   { showExpr'   :: Int -> ShowS  -- ^ Show with the given precedence level
   , intExpr'    :: Maybe Integer -- ^ Integer value?
   , doubleExpr' :: Maybe Double  -- ^ Floating value?
   , reduced'    :: Maybe Expr    -- ^ Next reduction step
   , negated'    :: Maybe Expr    -- ^ If this is @negate e@, the operand @e@ (used for sign normalization)
   , absed'      :: Maybe Expr    -- ^ If this is @abs e@, the operand @e@
   , signumed'   :: Maybe Expr    -- ^ If this is @signum e@, the operand @e@
   , reciped'    :: Maybe Expr    -- ^ If this is @recip e@, the operand @e@
   }
   | BinExpr
   { operation :: BinOp
   , argL :: Expr    -- ^ Left operand
   , argR :: Expr    -- ^ Right operand
   }

showExpr  r@(Expr {}) p = showExpr' r p
showExpr (BinExpr expr argL argR) p  =  showExpr (applyBinOp expr argL argR) p

intExpr :: Expr -> Maybe Integer
intExpr Expr{ intExpr' = i } = i
intExpr _ = Nothing

doubleExpr :: Expr -> Maybe Double
doubleExpr Expr{ doubleExpr' = d } = d
doubleExpr _ = Nothing

reduced :: Expr -> Maybe Expr
reduced Expr{ reduced' = r } = r
reduced (BinExpr e l r) =  reduced (applyBinOp e l r)

-- | If the expression is a negation (a negative numeric constant or a
--   @negate e@), return the (positive) operand. Used for sign normalization.
asNegation :: Expr -> Maybe Expr
asNegation e
    | Just n <- intExpr    e, n < 0     = Just (fromInteger (negate n))
    | Just d <- doubleExpr e, d < 0     = Just (fromDouble  (negate d))
    | otherwise                         = negatedOf e
  where negatedOf Expr{ negated' = n } = n
        negatedOf _                    = Nothing

asAbs :: Expr -> Maybe Expr
asAbs Expr{ absed' = a } = a
asAbs _                  = Nothing

asSignum :: Expr -> Maybe Expr
asSignum Expr{ signumed' = s } = s
asSignum _                     = Nothing

asRecip :: Expr -> Maybe Expr
asRecip Expr{ reciped' = r } = r
asRecip _                    = Nothing

rewriteReducedBinOp bin@(BinExpr expr argL argR )=
  let rr = applyBinOp expr argL argR
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
                 , negated'    = Nothing
                 , absed'      = Nothing
                 , signumed'   = Nothing
                 , reciped'    = Nothing
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

-- | Prefix unary minus, rendered as @-a@ (precedence 6, like Haskell's own
--   unary minus) rather than as @negate a@. Tagged via 'negated'' so that
--   sign normalization can recognise it (e.g. @x + negate y@ => @x - y@).
negateExpr :: Expr -> Expr
negateExpr a = emptyExpr { showExpr' = \p -> showParen (p > 6) $ showString "-" . showExpr a 7
                         , negated'  = Just a }

-- | Show builder for @+@ that normalizes signs: @a + (-b)@ renders as
--   @a - b@ (and @(-a) + b@ as @b - a@, since @+@ is commutative).
addShow :: Expr -> Expr -> Expr
addShow a b
    | Just b' <- asNegation b = op InfixL 6 " - " a b'
    | Just a' <- asNegation a = op InfixL 6 " - " b a'
    | otherwise               = op InfixL 6 " + " a b

-- | Show builder for @-@ that normalizes signs: @a - (-b)@ renders as @a + b@.
subShow :: Expr -> Expr -> Expr
subShow a b
    | Just b' <- asNegation b = op InfixL 6 " + " a b'
    | otherwise               = op InfixL 6 " - " a b

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
withReduce2 :: BinOp -> (Expr -> Expr -> Expr)
withReduce2 r a b = let rr = applyBinOp r a b
                        ra = reduced a
                        rb = reduced b
                        reductions =
                              (\a' b' -> withReduce2 r a' b') <$> ra <*> rb
                               <|> (\a' -> withReduce2 r a' b) <$> ra
                               <|> (\b' -> withReduce2 r a b') <$> rb
                               <|> fromInteger <$> intExpr    rr
                               <|> fromDouble  <$> doubleExpr rr
                    in case rr of
                          Expr {}            -> rr { reduced' = reductions }
                          BinExpr op argL argR -> fromMaybe (distributeConstant op argL argR) reductions

withReduce2AnnihilateAndIdentity :: Expr -> Expr -> BinOp -> (Expr -> Expr -> Expr)
withReduce2AnnihilateAndIdentity zero one r a b =
                    let
                      negateRule p q fallback
                        | p == -1   = negate q
                        | q == -1   = negate p
                        | otherwise = fallback
                      rr = identityRule one a b (annihilateRule zero a b (negateRule a b (distributeConstant r a b)))
                      ra = reduced a
                      rb = reduced b
                      reductions = (\a' b' -> identityRule one a' b' (annihilateRule zero a' b' (negateRule a' b' (withReduce2AnnihilateAndIdentity zero one (distributeOp r) a' b')))) <$> ra <*> rb
                               <|> (\a' -> if  a' == one then b else (if abs a' < 1e-15 then zero else (if a' == -1 then negate b else withReduce2AnnihilateAndIdentity zero one  (distributeOp r) a' b))) <$> ra
                               <|> (\b' -> if  b' == one then a else (if abs b' < 1e-15 then zero else (if b' == -1 then negate a else withReduce2AnnihilateAndIdentity zero one (distributeOp r) a b'))) <$> rb
                               <|> fromInteger <$> intExpr    rr
                               <|> fromDouble  <$> doubleExpr rr
                    in  case rr of
                            Expr {} -> rr {reduced' = reductions }
                            BinExpr op l rgt ->  fromMaybe (distributeConstant op l rgt) reductions

isConstant l = isJust (intExpr l) || isJust (doubleExpr l)
isBinExpr (BinExpr _ _ _ ) = True
isBinExpr _ = False

-- | Construct a 'BinOp' from its name, algebraic properties and underlying
--   operator function.
mkBinOp :: String -> Bool -> Bool -> (Expr -> Expr -> Expr) -> BinOp
mkBinOp name comm assoc f = BinOp { applyBinOp = f, opName = name, commutative = comm, associative = assoc, onLeftIdentity = Nothing }

-- | Wrap an operator so that applying it also redistributes constants. Used
--   when descending into the reduction steps of an associative/commutative
--   operator (e.g. a product), while preserving its algebraic metadata.
distributeOp :: BinOp -> BinOp
distributeOp o = o { applyBinOp = distributeConstant o }

-- | Whether constants may be freely rearranged between an outer operator and
--   an inner 'BinExpr'. This is only sound when the outer operator is both
--   associative and commutative and both nodes are the /same/ operator, which
--   is what keeps non-commutative operators (@-@, @/@, ...) untouched.
mergeable :: BinOp -> BinOp -> Bool
mergeable outer inner = commutative outer && associative outer && opName outer == opName inner

distributeConstant :: BinOp -> Expr -> Expr -> Expr
--- If we can distribute to left side and untag BinExpr on right side
distributeConstant op (BinExpr e1 l1 r1) (BinExpr e2 l r) | mergeable op e1 && mergeable op e2 && isConstant l1 && isConstant l=  distributeConstant e1 (rewriteReducedBinOp $ BinExpr op l1 l) (applyBinOp e2 r1 r)
distributeConstant op (BinExpr e1 l1 r1) (BinExpr e2 l r) | mergeable op e1 && mergeable op e2 && isConstant l1 && isConstant r=  distributeConstant e1 (rewriteReducedBinOp $ BinExpr op l1 r) (applyBinOp e2 r1 l)
distributeConstant op (BinExpr e1 l1 r1) (BinExpr e2 l r) | mergeable op e1 && mergeable op e2 && isConstant r1 && isConstant r=  distributeConstant e1 (rewriteReducedBinOp $ BinExpr op r1 r) (applyBinOp e2 l1 l)
distributeConstant op (BinExpr e1 l1 r1) (BinExpr e2 l r) | mergeable op e1 && mergeable op e2 && isConstant l  && isConstant r1=  distributeConstant e1 (rewriteReducedBinOp $ BinExpr op r1 l) (applyBinOp e2 l1 r)
--- If only one side is a BinExpr search for constants and simplify
distributeConstant op (BinExpr e l r ) a | mergeable op e && isConstant l && isConstant a =  BinExpr e (rewriteReducedBinOp $ BinExpr op l a) r
distributeConstant op (BinExpr e l r ) a | mergeable op e && isConstant r && isConstant a =  BinExpr e l (rewriteReducedBinOp $ BinExpr op r a)
distributeConstant op a (BinExpr e l r) | mergeable op e && isConstant l && isConstant a =  BinExpr e (rewriteReducedBinOp $ BinExpr op l a) r
distributeConstant op a (BinExpr e l r) | mergeable op e && isConstant r && isConstant a =  BinExpr e l (rewriteReducedBinOp $ BinExpr op r a)
--- Move the constant to the top
distributeConstant op (BinExpr e l r ) a | mergeable op e && isConstant r =  BinExpr e  (applyBinOp op l a)  r
distributeConstant op (BinExpr e l r ) a | mergeable op e && isConstant l =  BinExpr e  l (applyBinOp op r a)
distributeConstant op a (BinExpr e l r) | mergeable op e && isConstant r =  BinExpr e  (applyBinOp op l a)  r
distributeConstant op a (BinExpr e l r) | mergeable op e && isConstant l =  BinExpr e  l (applyBinOp op r a)
-- If is constant keep tagged as BinExpr
distributeConstant op a b | isConstant a && isConstant b = applyBinOp op a b
distributeConstant op a b | isConstant a || isConstant b = BinExpr op a b
-- Don't tag if nothing is constant
distributeConstant op a b = applyBinOp op a b

distributeUnary op expr
    | expr == 0                     = expr
    | Just expr' <- asNegation expr = expr'
distributeUnary op (BinExpr expr l r ) | isConstant l = BinExpr expr (withReduce op l ) r
distributeUnary op (BinExpr expr l r ) | isConstant r = BinExpr expr l (withReduce op r )
distributeUnary op expr = op expr

absExpr :: Expr -> Expr
absExpr a = (fun "abs" a) { absed' = Just a }

distributeUnaryAbs :: (Expr -> Expr) -> Expr -> Expr
distributeUnaryAbs op expr
    | Just expr' <- asNegation expr               = abs expr'
    | Just expr' <- asAbs expr                    = expr
    | (BinExpr exprBin l r) <- expr, isConstant l = BinExpr exprBin (withReduce op l ) r
    | (BinExpr exprBin l r) <- expr, isConstant r = BinExpr exprBin l (withReduce op r )
    | otherwise                                   = op expr

signumExpr :: Expr -> Expr
signumExpr a = (fun "signum" a) { signumed' = Just a }

distributeUnarySignum :: (Expr -> Expr) -> Expr -> Expr
distributeUnarySignum op expr
    | Just expr' <- asSignum expr                 = expr
    | (BinExpr exprBin l r) <- expr, isConstant l = BinExpr exprBin (withReduce op l ) r
    | (BinExpr exprBin l r) <- expr, isConstant r = BinExpr exprBin l (withReduce op r )
    | otherwise                                   = op expr

recipExpr :: Expr -> Expr
recipExpr a = (fun "recip" a) { reciped' = Just a }

distributeUnaryRecip :: (Expr -> Expr) -> Expr -> Expr
distributeUnaryRecip op expr
    | expr == 1                     = expr
    | Just expr' <- asRecip expr    = expr'
    | (BinExpr exprBin l r) <- expr, isConstant l = BinExpr exprBin (withReduce op l ) r
    | (BinExpr exprBin l r) <- expr, isConstant r = BinExpr exprBin l (withReduce op r )
    | otherwise                     = op expr


identityRule ident = (\a b r  -> if a == ident then b else  (if b == ident then a else r))
annihilateRule zero = (\a b r  -> if abs a < 1e-15 || abs b < 1e-15 then zero else  r)


-- | Identity simplification for a binary operator. The right operand is always
--   an identity (@a `op` ident@ == @a@). The left operand is handled by
--   'onLeftIdentity': for @+@ it is @Just id@ so @0 + a@ == @a@; for @-@ it is
--   @Just negate@ so @0 - a@ simplifies to @negate a@ (rather than the wrong
--   @a@); for operators without a left identity it is @Nothing@.
withReduce2Identity :: Expr -> BinOp -> (Expr -> Expr -> Expr)
withReduce2Identity ident r a b =
                    let leftId p q fallback = case onLeftIdentity r of
                                                Just act | p == ident -> act q
                                                _                     -> fallback
                        rr = leftId a b (if b == ident then a else applyBinOp r a b)
                        ra = reduced a
                        rb = reduced b
                        red = (\a' b' -> leftId a' b' (if b' == ident then a' else withReduce2Identity ident r a' b')) <$> ra <*> rb
                                     <|> (\a' -> leftId a' b (withReduce2Identity ident r a' b)) <$> ra
                                     <|> (\b' -> if  b' == ident then a else withReduce2Identity ident r a b') <$> rb
                                     <|> fromInteger <$> intExpr    rr
                                     <|> fromDouble  <$> doubleExpr rr
                    in
                    case rr of
                      Expr {} ->
                          rr { reduced' =  red }
                      BinExpr op l rgt -> fromMaybe (distributeConstant op l rgt) red

-- | Identity simplification together with constant redistribution, for a
--   commutative+associative operator (currently only @+@). Constants in nested
--   applications are folded together, e.g. @2 + (x + 3)@ simplifies to
--   @x + 5@. The 'mergeable' guard inside 'distributeConstant' keeps this from
--   ever crossing into another operator, and pure-constant sums stay flat
--   (e.g. @1 + 2 + 3@) because two constants reduce to an 'Expr', not a tagged
--   'BinExpr', so the step-by-step 'reduction' is preserved.
withReduce2IdentityDistribute :: Expr -> BinOp -> (Expr -> Expr -> Expr)
withReduce2IdentityDistribute ident r a b =
                    let rr = identityRule ident a b (distributeConstant r a b)
                        ra = reduced a
                        rb = reduced b
                        red = (\a' b' -> identityRule ident a' b' (withReduce2IdentityDistribute ident (distributeOp r) a' b')) <$> ra <*> rb
                                     <|> (\a' -> if a' == ident then b else withReduce2IdentityDistribute ident (distributeOp r) a' b) <$> ra
                                     <|> (\b' -> if b' == ident then a else withReduce2IdentityDistribute ident (distributeOp r) a b') <$> rb
                                     <|> fromInteger <$> intExpr    rr
                                     <|> fromDouble  <$> doubleExpr rr
                    in
                    case rr of
                      Expr {} ->
                          rr { reduced' =  red }
                      BinExpr op l rgt -> fromMaybe (distributeConstant op l rgt) red


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
    (+)    = withReduce2IdentityDistribute 0 $ mkBinOp " + " True  True  $ addShow `iOp2` (+)   `dOp2` (+)
    (-)    = \a b -> a + negate b
    (*)    = withReduce2AnnihilateAndIdentity 0 1 $ mkBinOp " * " True True $ op InfixL 7 " * " `iOp2` (*)   `dOp2` (*)
    negate = withReduce  $ distributeUnary (negateExpr `iOp` negate `dOp` negate)
    abs    = withReduce  $ distributeUnaryAbs (absExpr `iOp` abs    `dOp` abs)
    signum = withReduce  $ distributeUnarySignum (signumExpr `iOp` signum `dOp` signum)
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
    quot = withReduce2 $ mkBinOp " `quot` " False False $ op InfixL 7 " `quot` " `iOp2` quot
    rem  = withReduce2 $ mkBinOp " `rem` "  False False $ op InfixL 7 " `rem` "  `iOp2` rem
    div  = withReduce2 $ mkBinOp " `div` "  False False $ op InfixL 7 " `div` "  `iOp2` div
    mod  = withReduce2 $ mkBinOp " `mod` "  False False $ op InfixL 7 " `mod` "  `iOp2` mod
    toInteger someExpr = case intExpr someExpr of
          Just i -> i
          _      -> error $ "not an integer: " ++ show someExpr

instance Fractional Expr where
    (/)   = withReduce2Identity 1 $ mkBinOp " / " False False $ op InfixL 7 " / " `dOp2` (/)
    recip = withReduce  $ distributeUnaryRecip (recipExpr `dOp` recip)
    fromRational r = fromDouble (fromRational r)

instance RealFrac Expr where
   --round = withReduce $ fun "round" `dOp` round
   --floor = withReduce $ fun "floor" `dOp` floor
   --ceiling = withReduce $ fun "ceiling" `dOp` ceiling
   --truncate = withReduce $ fun "truncate" `dOp` truncate

instance RealFloat Expr where
   atan2 = withReduce2 $ mkBinOp "atan2" False False $ fun "atan2" `dOp2` atan2

fromDouble :: Double -> Expr
fromDouble d = (lift d) { doubleExpr' = Just d }

instance Floating Expr where
    pi    = (var "pi") { doubleExpr' = Just pi }
    exp   = withReduce  $ fun "exp"   `dOp` exp
    sqrt  = withReduce  $ fun "sqrt"  `dOp` sqrt
    log   = withReduce  $ fun "log"   `dOp` log
    (**)  = withReduce2Identity 1 $ mkBinOp "**" False False $ op InfixR 8 "**" `dOp2` (**)
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
    (<>) = withReduce2 $ mkBinOp " <> " False True $ op InfixR 6 " <> "
#endif

instance Monoid Expr where
    mempty = var "mempty"
#if !(MIN_VERSION_base(4,11,0))
    mappend = withReduce2 $ mkBinOp " <> " False True $ op InfixR 6 " <> "
#endif
    mconcat = fun "mconcat"

