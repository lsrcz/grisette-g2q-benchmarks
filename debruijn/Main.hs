{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import Control.Monad.Except
import Data.Either
import Data.Hashable
import GHC.Generics
import Grisette
import Utils.Timing

type Ident = (UnionM Int)

data CExpr
  = CVar Int
  | CLam CExpr
  | CApp CExpr CExpr
  deriving (Generic)
  deriving (ToCon Expr) via (Default CExpr)

capp :: [CExpr] -> CExpr
capp = foldl1 CApp

cnum :: Int -> CExpr
cnum n =
  CLam $
    CLam $
      foldr1 CApp (replicate n (CVar 2) ++ [CVar 1])

ctrueLam :: CExpr
ctrueLam = CLam $ CLam $ CVar 2

cfalseLam :: CExpr
cfalseLam = CLam $ CLam $ CVar 1

instance Show CExpr where
  showsPrec _ (CVar i) = shows i
  showsPrec p (CLam e) = showParen (p > 0) $ ("\\ " ++) . showsPrec 1 e
  showsPrec p (CApp e1 e2) = showParen (p > 1) $ showsPrec 1 e1 . (" " ++) . showsPrec 2 e2

data Expr
  = Var Ident
  | Lam (UnionM Expr)
  | App (UnionM Expr) (UnionM Expr)
  deriving (Show, Generic, Eq, Hashable)
  deriving (Mergeable, ToSym CExpr, SEq, EvaluateSym) via (Default Expr)

$(makeUnionWrapper "u" ''Expr)

instance GenSym (Int, Int) Expr where
  fresh (gendepth, absdepth)
    | gendepth <= 0 = genVar
    | otherwise = do
        v <- genVar
        l <- fresh (gendepth - 1, absdepth + 1)
        a1 <- fresh (gendepth - 1, absdepth)
        a2 <- fresh (gendepth - 1, absdepth)
        chooseUnionFresh [v, uLam l, uApp a1 a2]
    where
      genVar =
        if absdepth <= 0
          then return $ uLam $ uVar 1
          else uVar <$> simpleFresh (EnumGenBound 1 (absdepth + 1))

instance GenSym Int Expr where
  fresh gendepth = fresh (gendepth, 0 :: Int)

type SymStack = [UnionM Expr]

data Error = FuelError | AssertionError
  deriving (Show, Generic)
  deriving (Mergeable) via (Default Error)

eval :: Int -> Expr -> ExceptT Error UnionM Expr
eval maxFuel = eval' maxFuel []

eval' :: Int -> SymStack -> Expr -> ExceptT Error UnionM Expr
eval' fuel _ _ | fuel <= 0 = mrgThrowError FuelError
eval' fuel (e : stck) (Lam e') = eval' (fuel - 1) stck #~ (rep 1 #~ e #~ e')
eval' fuel stck (App e1 e2) = eval' (fuel - 1) (e2 : stck) #~ e1
eval' _ stck e = mrgLift $ app $ mrgReturn e : stck

rep :: Int -> Expr -> Expr -> UnionM Expr
rep i e v@(Var j) = do
  j1 <- j
  if i == j1 then mrgReturn e else mrgReturn v
rep i e (Lam e') = uLam $ rep (i + 1) e #~ e'
rep i e (App e1 e2) = uApp (rep i e #~ e1) (rep i e #~ e2)

app :: [UnionM Expr] -> UnionM Expr
app = foldl1 uApp

num :: Int -> Expr
num n =
  Lam $
    uLam $
      foldr1 uApp (replicate n (uVar 2) ++ [uVar 1])

trueLam :: Expr
trueLam = Lam $ uLam $ uVar 2

falseLam :: Expr
falseLam = Lam $ uLam $ uVar 1

idLam :: Expr
idLam = Lam $ uVar 1

constLam :: Expr
constLam = Lam $ uLam $ uVar 2

andLam :: Expr
andLam = Lam $ uLam $ app [uVar 2, uVar 1, uVar 2]

andLam' :: Expr
andLam' = Lam $ uLam $ app [uVar 1, uVar 2, uVar 1]

orLam :: Expr
orLam = Lam $ uApp (uVar 1) (uVar 1)

notLam :: Expr
notLam = Lam $ app [uVar 3, return falseLam, return trueLam]

notLam' :: Expr
notLam' = Lam $ app [uVar 1, uLam $ uLam $ uVar 1, app [uLam $ uVar 1, uLam $ uLam $ uVar 2]]

solveDeBruijn :: GrisetteSMTConfig n -> Int -> Int -> [([CExpr], CExpr)] -> IO (Maybe CExpr)
solveDeBruijn config depth maxFuel iopairs = do
  let sketch = genSym depth "sketch" :: UnionM Expr
  let constraints =
        mrgTraverse_
          ( \(i, o) -> do
              evaled <- eval maxFuel #~ app (sketch : toSym i)
              mrgIf (evaled ==~ (toSym o :: Expr)) (return ()) (throwError Main.AssertionError)
          )
          iopairs
  res <- solveExcept config (con . isRight) constraints
  {-
  case res of
    Left _ -> return Nothing
    Right mo -> return $ Just $ evaluateSymToCon mo sketch
  -}
  case res of
    Left _ -> return Nothing
    Right mo -> do
      let x = eval maxFuel #~ evaluateSym True mo sketch
      case x of
        ExceptT (SingleU (Right v)) -> return $ toCon v
        _ -> error "Should not happen"

idSpec :: [([CExpr], CExpr)]
idSpec = [([cnum 1], cnum 1), ([cnum 2], cnum 2)]

constSpec :: [([CExpr], CExpr)]
constSpec = [([cnum 1, cnum 2], cnum 1), ([cnum 2, cnum 3], cnum 2)]

orSpec :: [([CExpr], CExpr)]
orSpec =
  [ ([ctrueLam, ctrueLam], ctrueLam),
    ([ctrueLam, cfalseLam], ctrueLam),
    ([cfalseLam, ctrueLam], ctrueLam),
    ([cfalseLam, cfalseLam], cfalseLam)
  ]

andSpec :: [([CExpr], CExpr)]
andSpec =
  [ ([ctrueLam, ctrueLam], ctrueLam),
    ([ctrueLam, cfalseLam], cfalseLam),
    ([cfalseLam, ctrueLam], cfalseLam),
    ([cfalseLam, cfalseLam], cfalseLam)
  ]

notSpec :: [([CExpr], CExpr)]
notSpec = [([ctrueLam], cfalseLam), ([cfalseLam], ctrueLam)]

main :: IO ()
main = do
  let config = precise z3
  rid <- timeItAll "id" $ solveDeBruijn config 1 10 idSpec
  print rid
  rconst <- timeItAll "const" $ solveDeBruijn config 2 10 constSpec
  print rconst
  ror <- timeItAll "or" $ solveDeBruijn config 2 10 orSpec
  print ror
  rand <- timeItAll "and" $ solveDeBruijn config 4 10 andSpec
  print rand
  rnot <- timeItAll "not" $ solveDeBruijn config 5 10 notSpec
  print rnot
