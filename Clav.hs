{-

Following along with SPJ's The Implementation of Functional
Programming Languages.

-}

module Clav where


--------------------------------------------------------------
-- | 2.1: Syntax

data Var = Var Char

-- just two constants: integers, and plus
data Constant = KNum Int
              | KAdd

-- section 2.1.5 definition
data Exp = C Constant
         | V Var
         | A Exp Exp
         | L Var Exp

-- Show instances
instance Show Constant where
  show (KNum i) = show i
  show KAdd     = "+"

instance Show Var where
  show (Var c) = c:[]

instance Show Exp where
  show (C c)     = show c
  show (V v)     = show v
  show (A e1 e2) = "(" ++ show e1 ++ " " ++ show e2 ++ ")"
  show (L v e)   = "λ" ++ show v ++ "." ++ show e

testExp :: Exp
testExp = L (Var 'x') (A
                       (A
                        (C KAdd) (V (Var 'x')))
                       (C (KNum 1)))
--   => λx.+ x 1



--------------------------------------------------------------
--------------------------------------------------------------
-- | 2.2: Operational semantics


-- We need to be able to tell whether one variable name is the same as
-- another.
instance Eq Var where
  Var v1 == Var v2 = v1 == v2

-- 2.2.1:
-- does variable x occur free in expression e?
occursFree :: Var -> Exp -> Bool
occursFree x e = case e of
  C _     -> False
  V y     -> x == y
  A e1 e2 -> occursFree x e1 || occursFree x e2
  L y e'  -> y /= x && occursFree x e'

-- does variable x occur bound in expression e?
occursBound :: Var -> Exp -> Bool
occursBound x e = case e of
  C _     -> False
  V _     -> False
  A e1 e2 -> occursBound x e1 || occursBound x e2
  L y e'  -> ((y == x && occursFree x e')
              || occursBound x e')

-- return a variable that is not free in any expression in `ls`
mkVar :: [Exp] -> Var
mkVar ls = Var $ head $ filter notFree ['a'..'z']
  where
    notFree c = and $ map (\e' -> not $ occursFree (Var c) e') ls


-- 2.2.2: β-conversion
betaReduce :: Exp -> Exp
betaReduce ex@(C _)     = ex
betaReduce ex@(V _)     = ex
betaReduce ex@(L _ _)   = ex
betaReduce ex@(A e1 e2) = case e1 of
   (L v e1') -> substitute e1' e2 v
   _ -> ex

-- fig. 2.3, definition of E[M/x]
-- E[M/x]     E      M      x
substitute :: Exp -> Exp -> Var -> Exp

substitute e@(C _) _ _ = e

substitute e@(V y) m x | x == y    = m
                       | otherwise = e

substitute (A e f) m x = A (substitute e m x) (substitute f m x)

substitute (L y e) m x
  | y == x    = (L y e)
  | otherwise = if ((not (occursFree x e)) ||
                    (not (occursFree y m))) then
                  L y (substitute e m x)
                else
                  let z = mkVar [e,m]
                  in  L z (substitute (substitute e (V z) y) m x)

testExp2 :: Exp
testExp2 = A (testExp) (C (KNum 4)) -- (λx.((+) x) 1) 4
-- betaReduce testExp2 => ((+) 4) 1


-- the name capture problem 2.2.6
twice :: Exp
twice = (L (Var 'f')
           (L (Var 'x')
              (A
                 (V (Var 'f'))
                 (A (V (Var 'f'))
                    (V (Var 'x'))))))

-- twice         => λf.λx.(f (f x))
-- A twice twice => (λf.λx.(f (f x)) λf.λx.(f (f x)))
-- beta-reduce ^ => λx.(λf.λx.(f (f x)) (λf.λx.(f (f x)) x))
        --                                   ^       ^ if we change these to y's,
        --                                             can be reduced further

-- α-conversion
-- change lambda expression λx.E to
--   λy.E[y/x]
-- where y does not occur free in E or in any
-- expressions in `ls`
alphaConversion :: Exp -> [Exp] -> Exp
alphaConversion (L x e) ls = L y (substitute e (V y) x)
  where y = mkVar (e:ls)
alphaConversion e _ = e

-- not sure where to put this though...


-- η-reduction
etaReduction :: Exp -> Exp
etaReduction e@(L x (A e1@(L _ _) (V y))) | x == y    = e1
                                          | otherwise = e
etaReduction e = e

-- ghci> let r = (L (Var 'x') (A (L (Var 'y') (A (A (V (Var '+')) (V (Var 'y'))) (C (KNum 1)))) (V (Var 'x'))))
-- ghci> r
-- λx.(λy.((+ y) 1) x)
-- ghci> etaReduction r
-- λy.((+ y) 1)

-- ghci> let r2 = (L (Var 'z') (A (L (Var 'y') (A (A (V (Var '+')) (V (Var 'y'))) (C (KNum 1)))) (V (Var 'x'))))
-- ghci> r2
-- λz.(λy.((+ y) 1) x)
-- ghci> etaReduction r2
-- λz.(λy.((+ y) 1) x)
