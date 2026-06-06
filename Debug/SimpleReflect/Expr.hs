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
-- | Identifies a binary operator for dispatch in the simplification rules.
--   This is kept separate from the operator's /display/ string (which lives in
--   'applyBinOp'), so changing how an operator prints can never change which
--   algebraic rules apply to it.
data OpKind = KAdd | KMul | KQuot | KRem | KIDiv | KMod | KPow | KAtan2 | KMappend
  deriving (Eq)

-- | A binary operator together with the algebraic laws needed to decide
--   whether constants may safely be rearranged through nested applications
--   of it. Only operators that are commutative and associative may have
--   their constants merged (and then only with other applications of the
--   /same/ operator), which keeps simplification sound for non-commutative
--   operators such as @-@ and @/@.
data BinOp = BinOp
    { applyBinOp    :: Expr -> Expr -> Expr     -- ^ Build the result expression (handles showing and numeric folding)
    , opKind        :: OpKind                   -- ^ Identifies the operator, so only matching operators are merged
    , commutative   :: Bool                     -- ^ Is  @a `op` b@  ==  @b `op` a@ ?
    , associative   :: Bool                     -- ^ Is  @(a `op` b) `op` c@  ==  @a `op` (b `op` c)@ ?
    , onLeftIdentity :: Maybe (Expr -> Expr)    -- ^ If @Just f@, then @ident `op` b@ simplifies to @f b@ (e.g. @id@ for @+@, @negate@ for @-@)
    }

-- | Identifies which unary function produced an expression, so that
--   simplification rules (idempotence, inverses, sign rules, …) can recognise
--   it. A single tagged field replaces the per-function boolean fields.
data UnaryTag
   = UNegate | UAbs | USignum | URecip | UExp | ULog | USqrt
   | USin | UCos | USinh | UCosh | UAsin | UAtan | USucc | UPred
   deriving (Eq)

-- | A reflected expression
data Expr
   = Expr
   { showExpr'   :: Int -> ShowS         -- ^ Show with the given precedence level
   , intExpr'    :: Maybe Integer        -- ^ Integer value?
   , doubleExpr' :: Maybe Double         -- ^ Floating value?
   , reduced'    :: Maybe Expr           -- ^ Next reduction step
   , unary'      :: Maybe (UnaryTag, Expr)
       -- ^ If this is @f e@ for a tracked unary @f@, the tag and operand @e@
       --   (used for sign normalization, idempotence and inverse rules)
   }
   | BinExpr
   { operation :: BinOp
   , argL :: Expr    -- ^ Left operand
   , argR :: Expr    -- ^ Right operand
   }

-- | The operand, if the expression was produced by the given unary function.
asUnary :: UnaryTag -> Expr -> Maybe Expr
asUnary t Expr{ unary' = Just (t', e) } | t == t' = Just e
asUnary _ _                                       = Nothing

-- | Tag a shown expression as the application of a unary function to @a@.
mkUnary :: UnaryTag -> Expr -> Expr -> Expr
mkUnary t shown a = shown { unary' = Just (t, a) }

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

-- | If the expression is a negation (a negative numeric constant, a
--   @negate e@, or a product with a negative constant factor), return the
--   (positive) operand. Used for sign normalization.
asNegation :: Expr -> Maybe Expr
asNegation e
    | Just n <- intExpr    e, n < 0     = Just (fromInteger (negate n))
    | Just d <- doubleExpr e, d < 0     = Just (fromDouble  (negate d))
    | Just e' <- negatedProduct e       = Just e'
    | otherwise                         = asUnary UNegate e
  where -- A product with a negative constant factor is a negation, since
        -- @(-c) * y == negate (c * y)@ for any @y@. (Only products carrying a
        -- constant factor are tagged 'BinExpr's, which is exactly the case we
        -- can detect here.) This lets @a + (-0.5)*y@ print as @a - 0.5*y@.
        negatedProduct (BinExpr o l r)
            | opKind o == KMul, isConstant l, Just l' <- asNegation l = Just (applyBinOp o l' r)
            | opKind o == KMul, isConstant r, Just r' <- asNegation r = Just (applyBinOp o l r')
        negatedProduct _ = Nothing

asAbs, asSignum, asRecip, asExp, asLog, asSqrt, asSin, asCos,
  asSinh, asCosh, asAsin, asAtan, asSucc, asPred :: Expr -> Maybe Expr
asAbs    = asUnary UAbs
asSignum = asUnary USignum
asRecip  = asUnary URecip
asExp    = asUnary UExp
asLog    = asUnary ULog
asSqrt   = asUnary USqrt
asSin    = asUnary USin
asCos    = asUnary UCos
asSinh   = asUnary USinh
asCosh   = asUnary UCosh
asAsin   = asUnary UAsin
asAtan   = asUnary UAtan
asSucc   = asUnary USucc
asPred   = asUnary UPred

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
                 , unary'      = Nothing
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
--   unary minus) rather than as @negate a@. Tagged 'UNegate' so that sign
--   normalization can recognise it (e.g. @x + negate y@ => @x - y@).
negateExpr :: Expr -> Expr
negateExpr a = mkUnary UNegate (emptyExpr { showExpr' = \p -> showParen (p > 6) $ showString "-" . showExpr a 7 }) a

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

mulShow :: Expr -> Expr -> Expr
mulShow a b
    | Just b' <- asRecip b = op InfixL 7 " / " a b'
    | Just a' <- asRecip a = op InfixL 7 " / " b a'
    | otherwise            = op InfixL 7 " * " a b

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
                          BinExpr op argL argR  ->  fromMaybe (distributeConstant op argL argR) reductions
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
                               <|> (\a' -> if  a' == one then b else (if isZeroExpr a' then zero else (if a' == -1 then negate b else withReduce2AnnihilateAndIdentity zero one  (distributeOp r) a' b))) <$> ra
                               <|> (\b' -> if  b' == one then a else (if isZeroExpr b' then zero else (if b' == -1 then negate a else withReduce2AnnihilateAndIdentity zero one (distributeOp r) a b'))) <$> rb
                               <|> fromInteger <$> intExpr    rr
                               <|> fromDouble  <$> doubleExpr rr
                    in  case rr of
                            Expr {} -> rr {reduced' = reductions }
                            BinExpr op l rgt ->  fromMaybe (distributeConstant op l rgt) reductions

isConstant l = isJust (intExpr l) || isJust (doubleExpr l)

-- | The numeric value of a constant expression as a 'Double' (for comparison).
numValue :: Expr -> Maybe Double
numValue e = doubleExpr e <|> (fromInteger <$> intExpr e)

-- | Construct a 'BinOp' from its kind, algebraic properties and underlying
--   operator function.
mkBinOp :: OpKind -> Bool -> Bool -> (Expr -> Expr -> Expr) -> BinOp
mkBinOp kind comm assoc f = BinOp { applyBinOp = f, opKind = kind, commutative = comm, associative = assoc, onLeftIdentity = Nothing }

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
mergeable outer inner = commutative outer && associative outer && opKind outer == opKind inner

-- | The identity element of an operator, for the cases where collapsing it
--   away is safe: @0@ for @+@ and @1@ for @*@. This handles identities that
--   only appear after constant folding (e.g. @x + 25 - 25@ or @x * 4 / 4@),
--   matching how a literal @x + 0@ / @x * 1@ already collapses.
identityElem :: BinOp -> Maybe Expr
identityElem o
    | opKind o == KAdd = Just 0
    | opKind o == KMul = Just 1
    | otherwise         = Nothing

-- | Like 'BinExpr', but collapses an operand that equals the operator's
--   identity element (e.g. @x + 0@ becomes @x@). Needed because constant
--   folding can produce an identity, as in @x + 25 - 25@ => @x + 0@ => @x@.
binExprId :: BinOp -> Expr -> Expr -> Expr
binExprId e l r
    | Just i <- identityElem e, isConstant r, r == i = l
    | Just i <- identityElem e, isConstant l, l == i = r
    | otherwise                                      = BinExpr e l r

distributeConstant :: BinOp -> Expr -> Expr -> Expr
--- If we can distribute to left side and untag BinExpr on right side
distributeConstant op (BinExpr e1 l1 r1) (BinExpr e2 l r) | mergeable op e1 && mergeable op e2 && isConstant l1 && isConstant l=  distributeConstant e1 (rewriteReducedBinOp $ BinExpr op l1 l) (applyBinOp e2 r1 r)
distributeConstant op (BinExpr e1 l1 r1) (BinExpr e2 l r) | mergeable op e1 && mergeable op e2 && isConstant l1 && isConstant r=  distributeConstant e1 (rewriteReducedBinOp $ BinExpr op l1 r) (applyBinOp e2 r1 l)
distributeConstant op (BinExpr e1 l1 r1) (BinExpr e2 l r) | mergeable op e1 && mergeable op e2 && isConstant r1 && isConstant r=  distributeConstant e1 (rewriteReducedBinOp $ BinExpr op r1 r) (applyBinOp e2 l1 l)
distributeConstant op (BinExpr e1 l1 r1) (BinExpr e2 l r) | mergeable op e1 && mergeable op e2 && isConstant l  && isConstant r1=  distributeConstant e1 (rewriteReducedBinOp $ BinExpr op r1 l) (applyBinOp e2 l1 r)
--- If only one side is a BinExpr search for constants and simplify
distributeConstant op (BinExpr e l r ) a | mergeable op e && isConstant l && isConstant a =  binExprId e (rewriteReducedBinOp $ BinExpr op l a) r
distributeConstant op (BinExpr e l r ) a | mergeable op e && isConstant r && isConstant a =  binExprId e l (rewriteReducedBinOp $ BinExpr op r a)
distributeConstant op a (BinExpr e l r) | mergeable op e && isConstant l && isConstant a =  binExprId e (rewriteReducedBinOp $ BinExpr op l a) r
distributeConstant op a (BinExpr e l r) | mergeable op e && isConstant r && isConstant a =  binExprId e l (rewriteReducedBinOp $ BinExpr op r a)
--- Move the constant to the top
distributeConstant op (BinExpr e l r ) a | mergeable op e && isConstant r =  binExprId e  (applyBinOp op l a)  r
distributeConstant op (BinExpr e l r ) a | mergeable op e && isConstant l =  binExprId e  l (applyBinOp op r a)
distributeConstant op a (BinExpr e l r) | mergeable op e && isConstant r =  binExprId e  (applyBinOp op l a)  r
distributeConstant op a (BinExpr e l r) | mergeable op e && isConstant l =  binExprId e  l (applyBinOp op r a)
-- If is constant keep tagged as BinExpr
distributeConstant op a b | isConstant a && isConstant b = applyBinOp op a b
distributeConstant op a b | isConstant a || isConstant b = binExprId op a b
-- Don't tag if nothing is constant
distributeConstant op a b = applyBinOp op a b

distributeUnary op expr
    | expr == 0                     = expr
    | Just expr' <- asNegation expr = expr'
distributeUnary op bin@(BinExpr expr l r)
    | opKind expr == KMul =
        if isConstant l then BinExpr expr (withReduce op l) r
        else if isConstant r then BinExpr expr l (withReduce op r)
        else op bin
    | otherwise = op bin
distributeUnary op expr = op expr

absExpr :: Expr -> Expr
absExpr a = mkUnary UAbs (fun "abs" a) a

distributeUnaryAbs :: (Expr -> Expr) -> Expr -> Expr
distributeUnaryAbs op expr
    | Just expr' <- asNegation expr               = abs expr'
    | Just expr' <- asAbs expr                    = expr
distributeUnaryAbs op bin@(BinExpr exprBin l r)
    | opKind exprBin == KMul =
        if isConstant l then BinExpr exprBin (withReduce op l) (abs r)
        else if isConstant r then BinExpr exprBin (abs l) (withReduce op r)
        else op bin
    | otherwise = op bin
distributeUnaryAbs op expr = op expr

signumExpr :: Expr -> Expr
signumExpr a = mkUnary USignum (fun "signum" a) a

distributeUnarySignum :: (Expr -> Expr) -> Expr -> Expr
distributeUnarySignum op expr
    | Just expr' <- asSignum expr                 = expr
distributeUnarySignum op bin@(BinExpr exprBin l r)
    | opKind exprBin == KMul =
        if isConstant l then BinExpr exprBin (withReduce op l) (signum r)
        else if isConstant r then BinExpr exprBin (signum l) (withReduce op r)
        else op bin
    | otherwise = op bin
distributeUnarySignum op expr = op expr

recipExpr :: Expr -> Expr
recipExpr a = mkUnary URecip (fun "recip" a) a

distributeUnaryRecip :: (Expr -> Expr) -> Expr -> Expr
distributeUnaryRecip op expr
    | expr == 1                     = expr
    | Just expr' <- asRecip expr    = expr'
distributeUnaryRecip op bin@(BinExpr exprBin l r)
    | opKind exprBin == KMul =
        if isConstant l then BinExpr exprBin (withReduce op l) (recip r)
        else if isConstant r then BinExpr exprBin (recip l) (withReduce op r)
        else op bin
    | otherwise = op bin
distributeUnaryRecip op expr = op expr

expExpr :: Expr -> Expr
expExpr a = mkUnary UExp (fun "exp" a) a

distributeUnaryExp :: (Expr -> Expr) -> Expr -> Expr
distributeUnaryExp op expr
    | expr == 0                   = 1
    | Just expr' <- asLog expr    = expr'
    | otherwise                   = op expr

logExpr :: Expr -> Expr
logExpr a = mkUnary ULog (fun "log" a) a

distributeUnaryLog :: (Expr -> Expr) -> Expr -> Expr
distributeUnaryLog op expr
    | expr == 1                   = 0
    | Just expr' <- asExp expr    = expr'
    | otherwise                   = op expr

sqrtExpr :: Expr -> Expr
sqrtExpr a = mkUnary USqrt (fun "sqrt" a) a

distributeUnarySqrt :: (Expr -> Expr) -> Expr -> Expr
distributeUnarySqrt op expr
    | expr == 0                   = 0
    | expr == 1                   = 1
    | Just expr' <- asRecip expr  = recip (sqrt expr')
    | otherwise                   = op expr

sinExpr :: Expr -> Expr
sinExpr a = mkUnary USin (fun "sin" a) a

distributeUnarySin :: (Expr -> Expr) -> Expr -> Expr
distributeUnarySin op expr
    | expr == 0                   = 0
    | Just expr' <- asNegation expr = negate (sin expr')
    | otherwise                   = op expr

cosExpr :: Expr -> Expr
cosExpr a = mkUnary UCos (fun "cos" a) a

distributeUnaryCos :: (Expr -> Expr) -> Expr -> Expr
distributeUnaryCos op expr
    | expr == 0                   = 1
    | Just expr' <- asNegation expr = cos expr'
    | otherwise                   = op expr

sinhExpr :: Expr -> Expr
sinhExpr a = mkUnary USinh (fun "sinh" a) a

distributeUnarySinh :: (Expr -> Expr) -> Expr -> Expr
distributeUnarySinh op expr
    | expr == 0                   = 0
    | Just expr' <- asNegation expr = negate (sinh expr')
    | otherwise                   = op expr

coshExpr :: Expr -> Expr
coshExpr a = mkUnary UCosh (fun "cosh" a) a

distributeUnaryCosh :: (Expr -> Expr) -> Expr -> Expr
distributeUnaryCosh op expr
    | expr == 0                   = 1
    | Just expr' <- asNegation expr = cosh expr'
    | otherwise                   = op expr

asinExpr :: Expr -> Expr
asinExpr a = mkUnary UAsin (fun "asin" a) a

distributeUnaryAsin :: (Expr -> Expr) -> Expr -> Expr
distributeUnaryAsin op expr
    | expr == 0                   = 0
    | otherwise                   = op expr

atanExpr :: Expr -> Expr
atanExpr a = mkUnary UAtan (fun "atan" a) a

distributeUnaryAtan :: (Expr -> Expr) -> Expr -> Expr
distributeUnaryAtan op expr
    | expr == 0                   = 0
    | otherwise                   = op expr

succExpr :: Expr -> Expr
succExpr a = mkUnary USucc (fun "succ" a) a

distributeUnarySucc :: (Expr -> Expr) -> Expr -> Expr
distributeUnarySucc op expr
    | Just expr' <- asPred expr   = expr'
    | otherwise                   = op expr

predExpr :: Expr -> Expr
predExpr a = mkUnary UPred (fun "pred" a) a

distributeUnaryPred :: (Expr -> Expr) -> Expr -> Expr
distributeUnaryPred op expr
    | Just expr' <- asSucc expr   = expr'
    | otherwise                   = op expr

powRule :: Expr -> Expr -> Expr -> Expr
powRule a b fallback
    | b == 0    = 1
    | a == 1    = 1
    | a == 0    = 0
    | b == 1    = a
    | otherwise = fallback

-- | Distribute a power over a product so that a constant factor in the base
--   becomes foldable: @(x * 5) ** c@  =>  @x ** c * 5 ** c@. This only fires
--   when a constant factor is present (mirroring 'distributeUnaryAbs' /
--   'distributeUnaryRecip'), which then lets the surrounding @*@ fold the
--   exposed constant (e.g. @2 * (x * 5) ** 1.85@ => @x ** 1.85 * 39.27...@).
--
--   Note: @(a*b)**c == a**c * b**c@ holds for an integer exponent or a
--   non-negative base, but is not exact for a negative base with a fractional
--   exponent (e.g. @((-2)*(-5))**0.5@ vs @(-2)**0.5 * (-5)**0.5@).
distributePow :: Expr -> Expr -> Expr -> Expr
distributePow (BinExpr e l r) expo fallback
    | opKind e == KMul && (isConstant l || isConstant r) = (l ** expo) * (r ** expo)
distributePow _ _ fallback = fallback

withReduce2Pow :: BinOp -> (Expr -> Expr -> Expr)
withReduce2Pow r a b =
                    let rr = powRule a b (distributePow a b (applyBinOp r a b))
                        ra = reduced a
                        rb = reduced b
                        red = (\a' b' -> powRule a' b' (withReduce2Pow r a' b')) <$> ra <*> rb
                                     <|> (\a' -> powRule a' b (withReduce2Pow r a' b)) <$> ra
                                     <|> (\b' -> powRule a b' (withReduce2Pow r a b')) <$> rb
                                     <|> fromInteger <$> intExpr    rr
                                     <|> fromDouble  <$> doubleExpr rr
                    in
                    case rr of
                      Expr {} ->
                          rr { reduced' =  red }
                      BinExpr op l rgt -> fromMaybe (distributeConstant op l rgt) red


isZeroExpr :: Expr -> Bool
isZeroExpr e =
  case (intExpr e, doubleExpr e) of
    (Just i, _) -> i == 0
    (_, Just d) -> abs d < 1e-15
    _           -> False

identityRule ident = (\a b r  -> if a == ident then b else  (if b == ident then a else r))
annihilateRule zero = (\a b r  -> if isZeroExpr a || isZeroExpr b then zero else  r)


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

withReduce2Monoid :: BinOp -> (Expr -> Expr -> Expr)
withReduce2Monoid r a b =
                    let isMempty x = show x == "mempty"
                        rr = if isMempty a then b else (if isMempty b then a else applyBinOp r a b)
                        ra = reduced a
                        rb = reduced b
                        red = (\a' b' -> if isMempty a' then b' else (if isMempty b' then a' else withReduce2Monoid r a' b')) <$> ra <*> rb
                                     <|> (\a' -> if isMempty a' then b else withReduce2Monoid r a' b) <$> ra
                                     <|> (\b' -> if isMempty b' then a else withReduce2Monoid r a b') <$> rb
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
    -- Two integer constants compare exactly (no Double rounding).
    Expr{ intExpr' = Just a } == Expr{ intExpr' = Just b }  =  a == b
    a == b = case (numValue a, numValue b) of
        (Just x , Just y ) -> x == y            -- both numeric: compare values
        (Nothing, Nothing) -> show a == show b  -- both symbolic: structural
        _                  -> False             -- numeric vs symbolic: never equal

instance Ord Expr where
    compare Expr{ intExpr'    = Just a } Expr{ intExpr'    = Just b }  =  compare a b
    compare Expr{ doubleExpr' = Just a } Expr{ doubleExpr' = Just b }  =  compare a b
    compare a                           b                            =  compare (show a) (show b)
    min = fun "min" `iOp2` min `dOp2` min
    max = fun "max" `iOp2` max `dOp2` max

instance Num Expr where
    (+)    = withReduce2IdentityDistribute 0 $ mkBinOp KAdd True  True  $ addShow `iOp2` (+)   `dOp2` (+)
    (-)    = \a b -> a + negate b
    (*)    = withReduce2AnnihilateAndIdentity 0 1 $ mkBinOp KMul True True $ mulShow `iOp2` (*)   `dOp2` (*)
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
    quot = withReduce2 $ mkBinOp KQuot False False $ op InfixL 7 " `quot` " `iOp2` quot
    rem  = withReduce2 $ mkBinOp KRem False False $ op InfixL 7 " `rem` "  `iOp2` rem
    div  = withReduce2 $ mkBinOp KIDiv False False $ op InfixL 7 " `div` "  `iOp2` div
    mod  = withReduce2 $ mkBinOp KMod False False $ op InfixL 7 " `mod` "  `iOp2` mod
    toInteger someExpr = case intExpr someExpr of
          Just i -> i
          _      -> error $ "not an integer: " ++ show someExpr

instance Fractional Expr where
    (/)   = \a b -> a * recip b
    recip = withReduce  $ distributeUnaryRecip (recipExpr `dOp` recip)
    fromRational r = fromDouble (fromRational r)

-- | The 'Double' value of a constant expression, or an error naming @ctx@.
--   Used by the numeric-projection methods, which are only meaningful once an
--   expression has been reduced to a constant.
constantDouble :: String -> Expr -> Double
constantDouble ctx e = case doubleExpr e of
    Just d  -> d
    Nothing -> error $ ctx ++ ": not a constant Expr: " ++ show e

instance RealFrac Expr where
   properFraction e = let (n, f) = properFraction (constantDouble "properFraction" e)
                      in (n, fromDouble f)

instance RealFloat Expr where
   atan2 = withReduce2 $ mkBinOp KAtan2 False False $ fun "atan2" `dOp2` atan2
   -- Format properties are those of the underlying 'Double'.
   floatRadix  _  = floatRadix  (undefined :: Double)
   floatDigits _  = floatDigits (undefined :: Double)
   floatRange  _  = floatRange  (undefined :: Double)
   isIEEE      _  = isIEEE      (undefined :: Double)
   -- Value projections require a constant; predicates default to 'False' when symbolic.
   decodeFloat e  = decodeFloat (constantDouble "decodeFloat" e)
   encodeFloat m n = fromDouble (encodeFloat m n)
   isNaN          = maybe False isNaN          . doubleExpr
   isInfinite     = maybe False isInfinite     . doubleExpr
   isDenormalized = maybe False isDenormalized . doubleExpr
   isNegativeZero = maybe False isNegativeZero . doubleExpr

fromDouble :: Double -> Expr
fromDouble d = (lift d) { doubleExpr' = Just d }

instance Floating Expr where
    pi    = (var "pi") { doubleExpr' = Just pi }
    exp   = withReduce  $ distributeUnaryExp (expExpr   `dOp` exp)
    sqrt  = withReduce  $ distributeUnarySqrt (sqrtExpr `dOp` sqrt)
    log   = withReduce  $ distributeUnaryLog (logExpr   `dOp` log)
    (**)  = withReduce2Pow $ mkBinOp KPow False False $ op InfixR 8 "**" `dOp2` (**)
    sin   = withReduce  $ distributeUnarySin (sinExpr `dOp` sin)
    cos   = withReduce  $ distributeUnaryCos (cosExpr `dOp` cos)
    sinh  = withReduce  $ distributeUnarySinh (sinhExpr `dOp` sinh)
    cosh  = withReduce  $ distributeUnaryCosh (coshExpr `dOp` cosh)
    asin  = withReduce  $ distributeUnaryAsin (asinExpr `dOp` asin)
    acos  = withReduce  $ fun "acos"  `dOp` acos
    atan  = withReduce  $ distributeUnaryAtan (atanExpr `dOp` atan)
    asinh = withReduce  $ fun "asinh" `dOp` asinh
    acosh = withReduce  $ fun "acosh" `dOp` acosh
    atanh = withReduce  $ fun "atanh" `dOp` atanh

instance Enum Expr where
    succ   = withReduce  $ distributeUnarySucc (succExpr `iOp` succ `dOp` succ)
    pred   = withReduce  $ distributeUnaryPred (predExpr `iOp` pred `dOp` pred)
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
    (<>) = withReduce2Monoid $ mkBinOp KMappend False True $ op InfixR 6 " <> "
#endif

instance Monoid Expr where
    mempty = var "mempty"
#if !(MIN_VERSION_base(4,11,0))
    mappend = withReduce2Monoid $ mkBinOp KMappend False True $ op InfixR 6 " <> "
#endif
    mconcat = fun "mconcat"

