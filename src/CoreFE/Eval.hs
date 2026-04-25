module CoreFE.Eval where

import CoreFE.Syntax
import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad.IO.Class (liftIO)

-- | Look up the value at a de Bruijn index in a runtime environment, skipping type bindings.
lookupv :: Env -> Int -> Maybe Exp
lookupv [] _ = Nothing
lookupv (ExpE v : _) 0 = pure v
lookupv (RecE v : _) 0 = pure v
lookupv (ExpE _ : xs) n = lookupv xs (n - 1)
lookupv (RecE _ : xs) n = lookupv xs (n - 1)
lookupv (TypE _ : xs) n = lookupv xs n
lookupv (TypEN _ _ : xs) n = lookupv xs n

-- | Extract type bindings from a runtime environment as a 'TyEnv' for type-checking closures.
c2g :: Env -> TyEnv
c2g env = concatMap f env
  where
    f (TypE a) = [TypeEq a]
    f (TypEN name a) = [TypeDef name a]
    f _ = []

-- | Wrap a type in a 'TyBoxT' environment unless it is already boxed.
wrapEnvInTyBox :: TyEnv -> Typ -> Typ
wrapEnvInTyBox _ t@(TyBoxT _ _) = t
wrapEnvInTyBox env t = TyBoxT env t

-- | Look up a record field by label in a 'FEnv' expression value.
rlookupv :: Exp -> String -> Maybe Exp
rlookupv (FEnv (ExpE (Rec l1 v) : d)) l
  | l == l1 = pure v
  | l /= l1 = rlookupv (FEnv d) l
rlookupv (FEnv (ExpE (FEnv d1) : _)) l =
  rlookupv (FEnv d1) l
rlookupv (FEnv (_ : d)) l =
  rlookupv (FEnv d) l
rlookupv _ _ = Nothing

-- | Lift a 'Maybe' into 'MaybeT' for use in monadic evaluation chains.
hoistMaybe :: (Monad m) => Maybe a -> MaybeT m a
hoistMaybe = MaybeT . return

-- | Evaluate an expression to a value under a runtime environment.
eval :: Env -> Exp -> MaybeT IO Exp
eval env = go
  where
    go (Lit n) = pure $ Lit n
    go (Var n) = hoistMaybe $ lookupv env n
    go (Lam e) = pure $ Clos env e
    go e@(Clos _ _) = pure e
    go (App (Prim "print") e2) = do
      v <- eval env e2
      liftIO $ putStrLn (pretty v)
      pure $ Lit LitUnit
    go (App (Prim "input") _) = do
      line <- liftIO getLine
      pure $ Lit (LitStr line)
    go (App e1 e2) = do
      Clos env' e <- eval env e1
      v2 <- eval env e2
      eval (ExpE v2 : env') e
    go (TLam e) = pure $ TClos env e
    go e@(TClos _ _) = pure e
    go (TApp e a) = do
      TClos env' e1 <- eval env e
      eval (TypE (TyBoxT (c2g env) a) : env') e1
    go (Box e1 e2) = do
      FEnv v <- eval env (FEnv e1)
      eval v e2
    go e@(FEnv []) = pure e
    go (FEnv (ExpE e' : ve)) = do
      FEnv ve1 <- eval env (FEnv ve)
      ee <- eval (ve1 ++ env) e'
      pure $ FEnv (ExpE ee : ve1)
    go (FEnv (RecE e' : ve)) = do
      FEnv ve1 <- eval env (FEnv ve)
      ee <- eval (ve1 ++ env) e'
      pure $ FEnv (RecE ee : ve1)
    go (FEnv (TypE a : e1)) = do
      -- b_tdef
      FEnv ve1 <- eval env (FEnv e1)
      let b = TyBoxT (c2g (ve1 ++ env)) a
      return $ FEnv (TypE b : ve1)
    go (FEnv (TypEN name a : e1)) = do
      FEnv ve1 <- eval env (FEnv e1)
      let b = TyBoxT (c2g (ve1 ++ env)) a
      return $ FEnv (TypEN name b : ve1)
    go (Rec l e) = Rec l <$> eval env e
    go (RProj e l) = do
      v <- eval env e
      hoistMaybe $ rlookupv v l
    go (Fold t e) = do
      v <- eval env e
      pure (Fold t v)
    go (Unfold e) = do
      v <- eval env e
      case v of
        Fold _ inner -> pure inner
        _ -> hoistMaybe Nothing
    go (Anno e _) =
      eval env e
    go (Fix e) = do
      Clos env' e1 <- eval env e
      let v_fix = Clos (RecE v_fix : env') e1
      pure v_fix
    go (If cond e1 e2) = do
        Lit (LitBool b) <- eval env cond
        eval env (if b then e1 else e2)
    go (BinOp (Add e1 e2)) = do
        Lit (LitInt v1) <- eval env e1
        Lit (LitInt v2) <- eval env e2
        pure $ Lit (LitInt (v1 + v2))
    go (BinOp (Sub e1 e2)) = do
        Lit (LitInt v1) <- eval env e1
        Lit (LitInt v2) <- eval env e2
        pure $ Lit (LitInt (v1 - v2))
    go (BinOp (Mul e1 e2)) = do
        Lit (LitInt v1) <- eval env e1
        Lit (LitInt v2) <- eval env e2
        pure $ Lit (LitInt (v1 * v2))
    go (BinOp (EqEq e1 e2)) = do
        v1 <- eval env e1
        v2 <- eval env e2
        pure $ Lit (LitBool (v1 == v2))
    go (BinOp (Neq e1 e2)) = do
      v1 <- eval env e1
      v2 <- eval env e2
      pure $ Lit (LitBool (v1 /= v2))
    go (BinOp (Lt e1 e2)) = do
      Lit (LitInt v1) <- eval env e1
      Lit (LitInt v2) <- eval env e2
      pure $ Lit (LitBool (v1 < v2))
    go (BinOp (Le e1 e2)) = do
      Lit (LitInt v1) <- eval env e1
      Lit (LitInt v2) <- eval env e2
      pure $ Lit (LitBool (v1 <= v2))
    go (BinOp (Gt e1 e2)) = do
      Lit (LitInt v1) <- eval env e1
      Lit (LitInt v2) <- eval env e2
      pure $ Lit (LitBool (v1 > v2))
    go (BinOp (Ge e1 e2)) = do
      Lit (LitInt v1) <- eval env e1
      Lit (LitInt v2) <- eval env e2
      pure $ Lit (LitBool (v1 >= v2))
    go (Prim n) = pure $ Prim n
    go (DataCon ctor arg) = do
      val <- eval env arg
      pure $ DataCon ctor val
    go (Case e branches) = do
      DataCon ctor payload <- eval env e
      branchBody <- hoistMaybe $ lookupCaseBranch ctor branches
      eval (ExpE payload : env) branchBody
    go (EList es) = do
        vs <- mapM (eval env) es
        pure $ EList vs
    go (ETake n e) = do
        EList vs <- eval env e
        pure $ EList (take n vs)

-- | Run evaluation, returning 'Nothing' if evaluation gets stuck.
runEval :: Env -> Exp -> IO (Maybe Exp)
runEval env e = runMaybeT (eval env e)

-- | Find the body of the first branch matching a constructor tag, with @"_"@ as wildcard.
lookupCaseBranch :: String -> [CaseBranch] -> Maybe Exp
lookupCaseBranch _ [] = Nothing
lookupCaseBranch ctor (CaseBranch ctor' body : rest)
  | ctor == ctor' || ctor' == "_" = Just body
  | otherwise = lookupCaseBranch ctor rest