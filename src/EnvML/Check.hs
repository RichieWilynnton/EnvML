module EnvML.Check where

import EnvML.Syntax
import qualified CoreFE.Syntax as CoreFE
import Control.Monad (guard)

typeSubstName :: Name -> Typ -> Typ -> Typ
typeSubstName _ _ (TyLit l) = TyLit l
typeSubstName name s (TyVar n)
  | n == name = s
  | otherwise = TyVar n
typeSubstName name s (TyArr a b) = TyArr (typeSubstName name s a) (typeSubstName name s b)
typeSubstName name s (TyAll n body)
  | n == name = TyAll n body
  | otherwise = TyAll n (typeSubstName name s body)
typeSubstName name s (TyBoxT ctx t) = TyBoxT (tyCtxSubstName name s ctx) (typeSubstName name s t)
typeSubstName name s (TyRcd fs) = TyRcd [(l, typeSubstName name s t) | (l, t) <- fs]
typeSubstName name s (TySum cs) = TySum [(l, typeSubstName name s t) | (l, t) <- cs]
typeSubstName name s (TyMu n body)
  | n == name = TyMu n body
  | otherwise = TyMu n (typeSubstName name s body)
typeSubstName name s (TyList t) = TyList (typeSubstName name s t)
typeSubstName name s (TyCtx ctx) = TyCtx (tyCtxSubstName name s ctx)
typeSubstName _ _ t@(TyModule _) = t

tyCtxSubstName :: Name -> Typ -> TyCtx -> TyCtx
tyCtxSubstName _ _ [] = []
tyCtxSubstName name s (TypeN n t : rest)
  | n == name = TypeN n t : rest
  | otherwise = TypeN n (typeSubstName name s t) : tyCtxSubstName name s rest
tyCtxSubstName name s (KindN n : rest)
  | n == name = KindN n : rest
  | otherwise = KindN n : tyCtxSubstName name s rest
tyCtxSubstName name s (TypeEqN n t : rest)
  | n == name = TypeEqN n (typeSubstName name s t) : rest
  | otherwise = TypeEqN n (typeSubstName name s t) : tyCtxSubstName name s rest
tyCtxSubstName name s (e : rest) = e : tyCtxSubstName name s rest

lookupTypeEq :: TyCtx -> Name -> Maybe Typ
lookupTypeEq [] _ = Nothing
lookupTypeEq (TypeEqN n t : _) x | n == x = Just t
lookupTypeEq (_ : g) x = lookupTypeEq g x

teq :: TyCtx -> Typ -> Typ -> TyCtx -> Bool
teq _ (TyLit a) (TyLit b) _ = a == b
teq g1 (TyVar x) b g2 =
  case lookupTypeEq g1 x of
    Just a  -> teq g1 a b g2
    Nothing -> case b of
      TyVar y -> case lookupTypeEq g2 y of
        Just b' -> teq g1 (TyVar x) b' g2
        Nothing -> x == y
      _ -> False
teq g1 a (TyVar y) g2 =
  case lookupTypeEq g2 y of
    Just b  -> teq g1 a b g2
    Nothing -> False
teq g1 (TyArr a b) (TyArr c d) g2 =
  teq g1 a c g2 && teq g1 b d g2
teq g1 (TyAll n1 a) (TyAll n2 b) g2 =
  teq (KindN n1 : g1) a (typeSubstName n2 (TyVar n1) b) (KindN n1 : g2)
teq g1 (TyBoxT ctx1 a) (TyBoxT ctx2 b) g2 =
  teqCtx g1 ctx1 ctx2 g2 && teq (ctx1 ++ g1) a b (ctx2 ++ g2)
teq g1 (TyRcd fs1) (TyRcd fs2) g2 =
  length fs1 == length fs2
    && all (\((l1, t1), (l2, t2)) -> l1 == l2 && teq g1 t1 t2 g2) (zip fs1 fs2)
teq g1 (TySum cs1) (TySum cs2) g2 =
  length cs1 == length cs2
    && all (\((l1, t1), (l2, t2)) -> l1 == l2 && teq g1 t1 t2 g2) (zip cs1 cs2)
teq g1 (TyMu n1 a) (TyMu n2 b) g2 =
  teq (KindN n1 : g1) a (typeSubstName n2 (TyVar n1) b) (KindN n1 : g2)
teq g1 (TyList a) (TyList b) g2 =
  teq g1 a b g2
teq g1 (TyCtx ctx1) (TyCtx ctx2) g2 =
  teqCtx g1 ctx1 ctx2 g2
teq _ _ _ _ = False

teqCtx :: TyCtx -> TyCtx -> TyCtx -> TyCtx -> Bool
teqCtx _ [] [] _ = True
teqCtx g1 (KindN _ : e1) (KindN _ : e2) g2 =
  teqCtx g1 e1 e2 g2
teqCtx g1 (TypeN _ a : e1) (TypeN _ b : e2) g2 =
  teqCtx g1 e1 e2 g2 && teq (e1 ++ g1) a b (e2 ++ g2)
teqCtx g1 (TypeEqN _ a : e1) (TypeEqN _ b : e2) g2 =
  teqCtx g1 e1 e2 g2 && teq (e1 ++ g1) a b (e2 ++ g2)
teqCtx _ _ _ _ = False

getVar :: TyCtx -> Name -> Maybe Typ
getVar [] _ = Nothing
getVar (TypeN n a : _) x | n == x = Just a
getVar (_ : g) x = getVar g x

lookupModTypeEq :: TyCtx -> Name -> Maybe ModuleTyp
lookupModTypeEq [] _ = Nothing
lookupModTypeEq (TypeEqM n mty : _) x | n == x = Just mty
lookupModTypeEq (_ : g) x = lookupModTypeEq g x


infer :: TyCtx -> Exp -> Maybe Typ
infer _ (Lit lit) = pure $ TyLit $ inferLit lit
  where
    inferLit (CoreFE.LitInt _) = CoreFE.TyInt
    inferLit (CoreFE.LitBool _) = CoreFE.TyBool
    inferLit (CoreFE.LitStr _) = CoreFE.TyStr
    inferLit CoreFE.LitUnit = CoreFE.TyUnit
infer g (Var x) = getVar g x
infer g (App e1 e2) = do
  TyArr a b <- infer g e1
  guard (check g e2 a)
  return b
infer _ (TLam _ _ ) = error "Typed lambdas don't exist at source separately."
infer g (TApp e t) = do
  TyAll name b <- infer g e
  return (typeSubstName name t b)
infer g (Box d e) = do
  TyCtx g1 <- infer g (FEnv d)
  TyBoxT g1 <$> infer g1 e
infer _ (FEnv []) = pure (TyCtx [])
infer _ (FEnv (ExpE _ : _)) = error "Unnamed exp elements in FEnvs at source not supported currently."
infer g (FEnv (ExpEN name e : d)) = do
    TyCtx g1 <- infer g (FEnv d)
    a <- infer (g1 ++ g) e
    return (TyCtx (TypeN name a : g1))
infer _ (FEnv (TypE _ : _)) = error "Unnamed type elements in FEnvs at source not supported currently."
infer g (FEnv (TypEN name t : d)) = do
    TyCtx g1 <- infer g (FEnv d)
    return (TyCtx (TypeN name t : g1))
infer g (FEnv (ModE name m : d)) = do
    TyCtx g1 <- infer g (FEnv d)
    mty <- inferMod g m
    return (TyCtx (TyMod name mty : g1))
infer g (FEnv (ModTypE name mty : d)) = do
    TyCtx g1 <- infer g (FEnv d)
    return (TyCtx (TypeEqM name mty : g1))
infer _ (Rec []) = pure $ TyRcd []
infer g (Rec ((name, e) : rest)) = do
  a <- infer g e
  TyRcd ts <- infer g (Rec rest)
  return $ TyRcd ((name, a) : ts)
infer g (RProj e l) = do
  TyRcd fields <- infer g e
  lookup l fields
infer g (Anno e t) =
    if check g e t then Just t else Nothing
infer g (Mod m) = TyModule <$> inferMod g m
infer g (BinOp (Add e1 e2)) = do
  guard (check g e1 (TyLit CoreFE.TyInt))
  guard (check g e2 (TyLit CoreFE.TyInt))
  return (TyLit CoreFE.TyInt)
infer g (BinOp (Sub e1 e2)) = do
  guard (check g e1 (TyLit CoreFE.TyInt))
  guard (check g e2 (TyLit CoreFE.TyInt))
  return (TyLit CoreFE.TyInt)
infer g (BinOp (Mul e1 e2)) = do
  guard (check g e1 (TyLit CoreFE.TyInt))
  guard (check g e2 (TyLit CoreFE.TyInt))
  return (TyLit CoreFE.TyInt)
infer g (If e1 e2 e3) = do
  guard (check g e1 (TyLit CoreFE.TyBool))
  t2 <- infer g e2
  t3 <- infer g e3
  guard (teq g t2 t3 g)
  return t2
infer g (BinOp (EqEq e1 e2)) = do
  t1 <- infer g e1
  guard (check g e2 t1)
  return (TyLit CoreFE.TyBool)
infer g (BinOp (Neq e1 e2)) = do
  t1 <- infer g e1
  guard (check g e2 t1)
  return (TyLit CoreFE.TyBool)
infer g (BinOp (Lt e1 e2)) = do
  guard (check g e1 (TyLit CoreFE.TyInt))
  guard (check g e2 (TyLit CoreFE.TyInt))
  return (TyLit CoreFE.TyBool)
infer g (BinOp (Le e1 e2)) = do
  guard (check g e1 (TyLit CoreFE.TyInt))
  guard (check g e2 (TyLit CoreFE.TyInt))
  return (TyLit CoreFE.TyBool)
infer g (BinOp (Gt e1 e2)) = do
  guard (check g e1 (TyLit CoreFE.TyInt))
  guard (check g e2 (TyLit CoreFE.TyInt))
  return (TyLit CoreFE.TyBool)
infer g (BinOp (Ge e1 e2)) = do
  guard (check g e1 (TyLit CoreFE.TyInt))
  guard (check g e2 (TyLit CoreFE.TyInt))
  return (TyLit CoreFE.TyBool)
infer g (Fold ty e) =
  case resolveToMu g ty of
    Just (n, body) ->
      let unfolded = typeSubstName n ty body
      in if check g e unfolded then Just ty else Nothing
    Nothing -> if check g e ty then Just ty else Nothing
infer g (Unfold e) = do
  t <- infer g e
  unfoldMu g t
infer g (Case e branches) = do
  t <- infer g e
  ctors <- resolveTySum g t
  inferCaseBranches g ctors branches
infer _ (EList []) = Nothing -- Cannot infer empty list type
infer g (EList (e : es)) = do
  t <- infer g e
  guard (all (\ei -> check g ei t) es)
  return (TyList t)
infer g (ETake _ e) = do
  TyList t <- infer g e
  return (TyList t)
infer _ _ = Nothing


inferMod :: TyCtx -> Module -> Maybe ModuleTyp
inferMod g (VarM name) = getMod g name
inferMod g (Struct structs) = TySig <$> inferStructs g structs
inferMod g (Functor [] m) = inferMod g m
inferMod g (Functor ((name, TyArg) : rest) m) = do
  mty <- inferMod (KindN name : g) (Functor rest m)
  return $ ForallM name mty
inferMod g (Functor ((name, TmArgType ty) : rest) m) = do
  mty <- inferMod (TypeN name ty : g) (Functor rest m)
  return $ TyArrowM ty mty
inferMod _ (Functor ((_, TmArg) : _) _) = Nothing
inferMod g (MApp m1 m2) = do
  TyArrowM a mty <- inferMod g m1
  guard (check g (Mod m2) a)
  return mty
inferMod g (MAppt m1 _ty) = do
  ForallM _name mty <- inferMod g m1
  return mty -- TODO: substitute ty for name in mty
inferMod g (MAnno m mty) = do
  guard (checkMod g m mty)
  return mty

getMod :: TyCtx -> Name -> Maybe ModuleTyp
getMod [] _ = Nothing
getMod (TyMod n mty : _) x | n == x = Just mty
getMod (_ : g) x = getMod g x

inferStructs :: TyCtx -> Structures -> Maybe Intf
inferStructs _ [] = Just []
inferStructs g (s : rest) = do
  (entry, g') <- inferStructure g s
  entries <- inferStructs g' rest
  return (entry : entries)

inferStructure :: TyCtx -> Structure -> Maybe (IntfE, TyCtx)
inferStructure g (Let name Nothing e) = do
  t <- infer g e
  return (ValDecl name t, TypeN name t : g)
inferStructure g (Let name (Just ty) e) = do
  guard (check g e ty)
  return (ValDecl name ty, TypeN name ty : g)
inferStructure g (TypDecl name ty) =
  Just (TyDef name ty, TypeEqN name ty : g)
inferStructure g (ModTypDecl name mty) = case mty of
  TySig intf -> Just (SigDecl name intf, TypeEqM name mty : g)
  _          -> Just (SigDecl name [], TypeEqM name mty : g)
inferStructure g (ModStruct name Nothing m) = do
  mty <- inferMod g m
  return (ModDecl name (TyModule mty), TyMod name mty : g)
inferStructure g (ModStruct name (Just mty) m) = do
  guard (checkMod g m mty)
  return (ModDecl name (TyModule mty), TyMod name mty : g)
inferStructure g (FunctStruct name args Nothing m) = do
  mty <- inferMod g (Functor args m)
  return (FunctorDecl name args (TyModule mty), TyMod name mty : g)
inferStructure g (FunctStruct name args (Just mty) m) = do
  guard (checkMod g (Functor args m) mty)
  return (FunctorDecl name args (TyModule mty), TyMod name mty : g)

checkMod :: TyCtx -> Module -> ModuleTyp -> Bool
checkMod g m (TyVarM name) =
  case lookupModTypeEq g name of
    Just mty -> checkMod g m mty
    Nothing -> False
checkMod g (Functor ((name, TmArgType ty) : rest) m) (TyArrowM a mty) =
  teq g ty a g && checkMod (TypeN name a : g) (Functor rest m) mty
checkMod g (Functor ((name, TmArg) : rest) m) (TyArrowM a mty) =
  checkMod (TypeN name a : g) (Functor rest m) mty
checkMod g (Functor ((name, TyArg) : rest) m) (ForallM n mty) =
  checkMod (KindN name : g) (Functor rest m) (substModTypName n (TyVar name) mty)
checkMod g (Functor [] m) mty = checkMod g m mty
checkMod g (Struct structs) (TySig intf) =
  case inferStructs g structs of
    Just inferred -> intfEq g inferred intf
    Nothing -> False
checkMod g m mty =
  case inferMod g m of
    Just mty' -> mtyEq g mty' mty
    Nothing -> False

check :: TyCtx -> Exp -> Typ -> Bool
check g (Lam ((name, TmArgType tyA) : rest) e) (TyArr a b) =
  teq g tyA a g && check (TypeN name a : g) (Lam rest e) b
check g (Lam ((name, TmArg) : rest) e) (TyArr a b) =
  check (TypeN name a : g) (Lam rest e) b
check g (Lam ((name, TyArg) : rest) e) (TyAll n b) =
  check (KindN name : g) (Lam rest e) (typeSubstName n (TyVar name) b)
check g (Lam [] e) t = check g e t
check g (Fix f e) (TyArr a b) =
  check (TypeN f (TyArr a b) : g) e (TyArr a b)
check g (Clos d args e) (TyBoxT ctx (TyArr a b)) =
  case infer g (FEnv d) of
    Just (TyCtx ctx') -> teqCtx g ctx' ctx g && check ctx (Lam args e) (TyArr a b)
    _ -> False
check g (Clos d args e) (TyBoxT ctx (TyAll n b)) =
  case infer g (FEnv d) of
    Just (TyCtx ctx') -> teqCtx g ctx' ctx g && check ctx (Lam args e) (TyAll n b)
    _ -> False
check _ (TClos {}) (TyBoxT _ (TyAll _ _)) =
  error "Typed closures not supported at source currently."
check g (DataCon ctor payload ty) t =
  teq g ty t g && case resolveTySum g ty of
    Just ctors -> case lookup ctor ctors of
      Just payloadTy -> check g payload payloadTy
      Nothing -> False
    Nothing -> False
check _ (EList []) (TyList _) = True
check g (EList es) (TyList t) = all (\e -> check g e t) es
check g e t =
  case infer g e of
    Just t' -> teq g t' t g
    _ -> False

resolveTySum :: TyCtx -> Typ -> Maybe [(Name, Typ)]
resolveTySum _ (TySum ctors) = Just ctors
resolveTySum g (TyVar x) =
  lookupTypeEq g x >>= resolveTySum g
resolveTySum _ _ = Nothing

unfoldMu :: TyCtx -> Typ -> Maybe Typ
unfoldMu _ (TyMu n body) = Just (typeSubstName n (TyMu n body) body)
unfoldMu g (TyVar x) = lookupTypeEq g x >>= unfoldMu g
unfoldMu _ _ = Nothing

resolveToMu :: TyCtx -> Typ -> Maybe (Name, Typ)
resolveToMu _ (TyMu n body) = Just (n, body)
resolveToMu g (TyVar x) = lookupTypeEq g x >>= resolveToMu g
resolveToMu _ _ = Nothing

inferCaseBranches :: TyCtx -> [(Name, Typ)] -> [CaseBranch] -> Maybe Typ
inferCaseBranches _ _ [] = Nothing
inferCaseBranches g ctors (b : bs) = do
  t <- inferCaseBranch g ctors b
  mapM_ (\br -> do
    t' <- inferCaseBranch g ctors br
    guard (teq g t t' g)) bs
  return t

inferCaseBranch :: TyCtx -> [(Name, Typ)] -> CaseBranch -> Maybe Typ
inferCaseBranch g _     (CaseBranch "_" _ body) = infer g body
inferCaseBranch g ctors (CaseBranch ctor binder body) = do
  payloadTy <- lookup ctor ctors
  infer (TypeN binder payloadTy : g) body

mtyEq :: TyCtx -> ModuleTyp -> ModuleTyp -> Bool
mtyEq g (TyVarM n) m2 =
  case lookupModTypeEq g n of
    Just mty -> mtyEq g mty m2
    Nothing -> case m2 of
      TyVarM m -> n == m
      _ -> False
mtyEq g m1 (TyVarM n) =
  case lookupModTypeEq g n of
    Just mty -> mtyEq g m1 mty
    Nothing -> False
mtyEq g (TyArrowM a1 m1) (TyArrowM a2 m2) =
  teq g a1 a2 g && mtyEq g m1 m2
mtyEq g (ForallM n1 m1) (ForallM n2 m2) =
  mtyEq (KindN n1 : g) m1 (substModTypName n2 (TyVar n1) m2)
mtyEq g (TySig i1) (TySig i2) = intfEq g i1 i2
mtyEq _ (TyVarM n1) (TyVarM n2) = n1 == n2
mtyEq _ _ _ = False

intfEq :: TyCtx -> Intf -> Intf -> Bool
intfEq _ [] [] = True
intfEq g (TyDef n1 t1 : r1) (TyDef n2 t2 : r2) =
  n1 == n2 && teq g t1 t2 g && intfEq (TypeEqN n1 t1 : g) r1 r2
intfEq g (ValDecl n1 t1 : r1) (ValDecl n2 t2 : r2) =
  n1 == n2 && teq g t1 t2 g && intfEq (TypeN n1 t1 : g) r1 r2
intfEq g (ModDecl n1 t1 : r1) (ModDecl n2 t2 : r2) =
  n1 == n2 && teq g t1 t2 g && intfEq g r1 r2
intfEq g (FunctorDecl n1 _ t1 : r1) (FunctorDecl n2 _ t2 : r2) =
  n1 == n2 && teq g t1 t2 g && intfEq g r1 r2
intfEq g (SigDecl n1 i1 : r1) (SigDecl n2 i2 : r2) =
  n1 == n2 && intfEq g i1 i2 && intfEq g r1 r2
intfEq _ _ _ = False

substModTypName :: Name -> Typ -> ModuleTyp -> ModuleTyp
substModTypName name s (TyArrowM ty mty) =
  TyArrowM (typeSubstName name s ty) (substModTypName name s mty)
substModTypName name s (ForallM n mty)
  | n == name = ForallM n mty
  | otherwise = ForallM n (substModTypName name s mty)
substModTypName name s (TySig intf) = TySig (substIntfName name s intf)
substModTypName _ _ (TyVarM n) = TyVarM n

substIntfName :: Name -> Typ -> Intf -> Intf
substIntfName _ _ [] = []
substIntfName name s (TyDef n ty : rest) =
  TyDef n (typeSubstName name s ty) : substIntfName name s rest
substIntfName name s (ValDecl n ty : rest) =
  ValDecl n (typeSubstName name s ty) : substIntfName name s rest
substIntfName name s (ModDecl n ty : rest) =
  ModDecl n (typeSubstName name s ty) : substIntfName name s rest
substIntfName name s (FunctorDecl n args ty : rest) =
  FunctorDecl n args (typeSubstName name s ty) : substIntfName name s rest
substIntfName name s (SigDecl n intf : rest) =
  SigDecl n (substIntfName name s intf) : substIntfName name s rest