module EnvML.Desugar (desugarModule, desugarExp) where

import EnvML.Syntax

desugarModule :: Module -> Module
desugarModule m = case m of
  VarM n      -> VarM n
  Functor as b -> Functor as (desugarModule b)
  Struct ss   -> Struct (map desugarStructure ss)
  MApp m1 m2  -> MApp (desugarModule m1) (desugarModule m2)
  MAppt m1 t  -> MAppt (desugarModule m1) t
  MAnno m1 mt -> MAnno (desugarModule m1) mt

desugarStructure :: Structure -> Structure
desugarStructure s = case s of
  Let n mt e          -> Let n (fmap desugarTyp mt) (desugarExp e)
  TypDecl n t         -> TypDecl n (desugarTypWithBinder (Just n) t)
  ModTypDecl n mt     -> ModTypDecl n mt
  ModStruct n mt m    -> ModStruct n mt (desugarModule m)
  FunctStruct n as mt m -> FunctStruct n as mt (desugarModule m)

desugarExp :: Exp -> Exp
desugarExp e = case e of
  Lit l         -> Lit l
  Var n         -> Var n
  Fix n e1      -> Fix n (desugarExp e1)
  If c t f      -> If (desugarExp c) (desugarExp t) (desugarExp f)
  Lam as body   -> Lam as (desugarExp body)
  TLam as body  -> TLam as (desugarExp body)
  Clos env as body -> Clos (desugarEnv env) as (desugarExp body)
  App e1 e2     -> App (desugarExp e1) (desugarExp e2)
  TClos env as body -> TClos (desugarEnv env) as (desugarExp body)
  TApp e1 t     -> TApp (desugarExp e1) t
  Box env e1    -> Box (desugarEnv env) (desugarExp e1)
  Rec fs        -> Rec [(n, desugarExp v) | (n, v) <- fs]
  RProj e1 n    -> RProj (desugarExp e1) n
  FEnv env      -> FEnv (desugarEnv env)
  Anno e1 t     -> Anno (desugarExp e1) t
  Mod m         -> Mod (desugarModule m)
  -- Wrap constructor with fold
  DataCon ctor arg ty -> Fold ty (DataCon ctor (desugarExp arg) ty)
  -- Wrap case scrutinee with unfold
  Case scrut bs -> Case (Unfold (desugarExp scrut)) (map desugarBranch bs)
  Fold t e1     -> Fold t (desugarExp e1)
  Unfold e1     -> Unfold (desugarExp e1)
  EList es      -> EList (map desugarExp es)
  ETake i e1    -> ETake i (desugarExp e1)
  BinOp op      -> BinOp (desugarBinOp op)

desugarBranch :: CaseBranch -> CaseBranch
desugarBranch (CaseBranch ctor binder body) =
  CaseBranch ctor binder (desugarExp body)

desugarBinOp :: BinOp -> BinOp
desugarBinOp op = case op of
  Add e1 e2  -> Add (desugarExp e1) (desugarExp e2)
  Sub e1 e2  -> Sub (desugarExp e1) (desugarExp e2)
  Mul e1 e2  -> Mul (desugarExp e1) (desugarExp e2)
  EqEq e1 e2 -> EqEq (desugarExp e1) (desugarExp e2)
  Neq e1 e2  -> Neq (desugarExp e1) (desugarExp e2)
  Lt e1 e2   -> Lt (desugarExp e1) (desugarExp e2)
  Le e1 e2   -> Le (desugarExp e1) (desugarExp e2)
  Gt e1 e2   -> Gt (desugarExp e1) (desugarExp e2)
  Ge e1 e2   -> Ge (desugarExp e1) (desugarExp e2)

desugarEnv :: Env -> Env
desugarEnv = map desugarEnvE

desugarEnvE :: EnvE -> EnvE
desugarEnvE envE = case envE of
  ExpEN n e   -> ExpEN n (desugarExp e)
  ExpE e      -> ExpE (desugarExp e)
  TypEN n t   -> TypEN n (desugarTyp t)
  TypE t      -> TypE (desugarTyp t)
  ModE n m    -> ModE n (desugarModule m)
  ModTypE n t -> ModTypE n t

desugarTyp :: Typ -> Typ
desugarTyp = desugarTypWithBinder Nothing

desugarTypWithBinder :: Maybe Name -> Typ -> Typ
desugarTypWithBinder mb ty = case ty of
  TyLit l      -> TyLit l
  TyVar n      -> TyVar n
  TyArr a b    -> TyArr (desugarTypWithBinder mb a) (desugarTypWithBinder mb b)
  TyAll n t    -> TyAll n (desugarTypWithBinder mb t)
  TyBoxT ctx t -> TyBoxT ctx (desugarTypWithBinder mb t)
  TyRcd fs     -> TyRcd [(n, desugarTypWithBinder mb t) | (n, t) <- fs]
  TySum ctors  ->
    let ctors' = [(n, desugarTypWithBinder mb t) | (n, t) <- ctors]
    in case mb of
      Just binder -> TyMu binder (TySum ctors')
      Nothing     -> TySum ctors'
  TyMu n t     -> TyMu n (desugarTypWithBinder (Just n) t)
  TyCtx ctx    -> TyCtx ctx
  TyModule mt  -> TyModule mt
  TyList t     -> TyList (desugarTypWithBinder mb t)

desugarCtors :: [(Name, Typ)] -> [(Name, Typ)]
desugarCtors = map (\(n, t) -> (n, desugarTyp t))
