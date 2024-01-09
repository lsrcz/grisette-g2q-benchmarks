{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad.Except
  ( ExceptT,
    MonadError (throwError),
    when,
  )
import GHC.Generics (Generic)
import Grisette
  ( Default (Default),
    EvaluateSym,
    LogicalOp (symNot, (.&&), (.||)),
    Mergeable (rootStrategy),
    MergingStrategy (SimpleStrategy),
    SEq ((.==)),
    SOrd ((.<)),
    SimpleMergeable (mrgIte),
    Solvable (con),
    SymBool,
    SymIntN,
    ToCon,
    UnionM,
    evaluateSymToCon,
    mrgFoldM,
    mrgIf,
    precise,
    solveExcept,
    z3,
  )
import Utils.Timing (timeItAll)

type Ident = String

type SymVal = SymIntN 64

-- We can definitely implement SymEnv as a type synonym rather than a newtype
-- with custom Mergeable instance. But a custom Mergeable instance can be more
-- efficient if we are going to verify a very large program.

newtype SymEnv = SymEnv {unSymEnv :: [(Ident, SymVal)]}
  deriving (Show, Generic)
  deriving (EvaluateSym) via (Default SymEnv)

newtype Env = Env {unEnv :: [(Ident, Int)]}
  deriving (Show, Generic)
  deriving (ToCon SymEnv) via (Default Env)

instance Mergeable SymEnv where
  rootStrategy = SimpleStrategy $ \cond (SymEnv l) (SymEnv r) -> SymEnv $ go cond l r
    where
      go _ [] [] = []
      go cond ((li, lv) : l) ((ri, rv) : r)
        | li == ri = (ri, mrgIte cond lv rv) : go cond l r
      go _ _ _ = error "Should not happen"

type Stmts = [Stmt]

data AExpr
  = I Int
  | Var Ident
  | Add AExpr AExpr
  | Mul AExpr AExpr
  deriving (Show, Eq)

data BExpr
  = Not BExpr
  | And BExpr BExpr
  | Or BExpr BExpr
  | Lt AExpr AExpr
  | Eq AExpr AExpr
  deriving (Show, Eq)

data Stmt
  = Assign Ident AExpr
  | Assert BExpr
  | If BExpr Stmts Stmts
  | While BExpr Stmts
  deriving (Show, Eq)

data Error
  = AssertionFailed
  | LoopUnfoldingLimitReached
  deriving (Show, Eq, Generic)
  deriving (Mergeable) via (Default Error)

evalA :: SymEnv -> AExpr -> SymVal
evalA _ (I i) = fromIntegral i
evalA (SymEnv env) (Var x) = case lookup x env of
  Just v -> v
  Nothing ->
    -- We do not track the error here as we will evaluate concrete programs
    error "Bad program: variable not in scope"
evalA env (Add e1 e2) = evalA env e1 + evalA env e2
evalA env (Mul e1 e2) = evalA env e1 * evalA env e2

evalB :: SymEnv -> BExpr -> SymBool
evalB env (Not e) = symNot (evalB env e)
evalB env (And e1 e2) = evalB env e1 .&& evalB env e2
evalB env (Or e1 e2) = evalB env e1 .|| evalB env e2
evalB env (Lt e1 e2) = evalA env e1 .< evalA env e2
evalB env (Eq e1 e2) = evalA env e1 .== evalA env e2

evalStmt :: Int -> SymEnv -> Stmt -> ExceptT Error UnionM SymEnv
evalStmt _ e (Assign ident aexpr) = return $ SymEnv $ (ident, evalA e aexpr) : (unSymEnv e)
evalStmt unfoldLimit e (If bexpr lhs rhs) =
  mrgIf
    (evalB e bexpr)
    (evalStmts unfoldLimit e lhs)
    (evalStmts unfoldLimit e rhs)
evalStmt unfoldLimit e (While bexpr body) = go unfoldLimit e
  where
    go limit e1 = do
      when (limit == 0) $ throwError LoopUnfoldingLimitReached
      mrgIf
        (evalB e1 bexpr)
        (evalStmts unfoldLimit e1 body >>= go (limit - 1))
        (return e1)
evalStmt _ e (Assert bexpr) = do
  mrgIf (evalB e bexpr) (return e) (throwError AssertionFailed)

evalStmts :: Int -> SymEnv -> Stmts -> ExceptT Error UnionM SymEnv
evalStmts unfoldLimit = mrgFoldM (evalStmt unfoldLimit)

prog1 :: Stmts
prog1 =
  [ Assign "k" (I 1),
    Assign "i" (I 0),
    Assign "n" (I 5),
    While
      (Or (Lt (Var "i") (Var "n")) (Eq (Var "i") (Var "n")))
      [Assign "i" (Add (Var "i") (I 1))],
    Assign "z" (Add (Var "k") (Add (Var "i") (Var "j"))),
    Assert (Lt (Mul (Var "n") (I 2)) (Var "z"))
  ]

mulSum :: Stmts
mulSum =
  [ If
      (Lt (I 0) (Var "x"))
      [Assert (Not (Eq (Mul (Var "x") (Var "y")) (Add (Var "x") (Var "y"))))]
      []
  ]

findCounterExample :: Int -> SymEnv -> Stmts -> IO (Maybe Env)
findCounterExample unfoldLimit env prog = do
  let evaled = evalStmts unfoldLimit env prog
  res <-
    solveExcept
      (precise z3)
      (\case Left AssertionFailed -> con True; _ -> con False)
      evaled
  case res of
    Left _ -> do
      r1 <-
        solveExcept
          (precise z3)
          (\case Left LoopUnfoldingLimitReached -> con True; _ -> con False)
          evaled
      case r1 of
        Left _ -> return Nothing
        Right _ -> do
          putStrLn "Warning, the loop unfolding limit can be reached, please consider increasing it"
          return Nothing
    Right model -> return $ Just $ evaluateSymToCon model env

main :: IO ()
main = do
  r1 <- timeItAll "badEnvSearch prog" $ findCounterExample 10 (SymEnv [("j", "j")]) prog1
  print r1
  r2 <- timeItAll "non-zero Mul x y == Add x y" $ findCounterExample 10 (SymEnv [("x", "x"), ("y", "y")]) mulSum
  print r2
  case r2 of
    Just (Env [("x", x), ("y", y)]) -> do
      print $ x * y
      print $ x + y
    _ -> undefined
