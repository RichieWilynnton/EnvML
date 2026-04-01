{-# LANGUAGE ScopedTypeVariables #-}
module EnvML.CheckSpec (spec) where

import EnvML.Syntax as Src
import EnvML.Parser.Lexer (lexer)
import EnvML.Parser.Parser (parseExp, parseModule, parseModuleTyp, parseTyp)
import EnvML.Check
import EnvML.Desugar (desugarExp, desugarModule)
import qualified CoreFE.Syntax as CoreFE
import Data.Maybe (isJust)
import Test.Hspec
import Debug.Trace (trace)

pde :: String -> Src.Exp
pde input = desugarExp (parseExp (lexer input))

pe :: String -> Src.Exp
pe input = parseExp (lexer input)

pt :: String -> Src.Typ
pt input = parseTyp (lexer input)

-- Helper: parse and desugar a module, infer its structures
inferMod' :: String -> Maybe Src.Intf
inferMod' input =
  let m = desugarModule (parseModule (lexer input))
  in case m of
    Src.Struct structs -> inferStructs [] structs
    _ -> Nothing

spec :: Spec
spec = do
  describe "infer literals" $ do
    it "infers int literal" $
      infer [] (pe "42") `shouldBe` Just (TyLit CoreFE.TyInt)

    it "infers bool literal true" $
      infer [] (pe "true") `shouldBe` Just (TyLit CoreFE.TyBool)

    it "infers bool literal false" $
      infer [] (pe "false") `shouldBe` Just (TyLit CoreFE.TyBool)

    it "infers string literal" $
      infer [] (pe "\"hello\"") `shouldBe` Just (TyLit CoreFE.TyStr)

    it "infers unit literal" $
      infer [] (pe "()") `shouldBe` Just (TyLit CoreFE.TyUnit)

  describe "infer variables" $ do
    it "infers variable from context" $
      infer [TypeN "x" (TyLit CoreFE.TyInt)] (pe "x")
        `shouldBe` Just (TyLit CoreFE.TyInt)

    it "fails for unbound variable" $
      infer [] (pe "x") `shouldBe` Nothing

  describe "infer applications" $ do
    it "infers simple function application" $
      let ctx = [TypeN "f" (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyBool)),
                 TypeN "x" (TyLit CoreFE.TyInt)]
      in infer ctx (pe "f(x)") `shouldBe` Just (TyLit CoreFE.TyBool)

    it "fails application with wrong argument type" $
      let ctx = [TypeN "f" (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyBool)),
                 TypeN "x" (TyLit CoreFE.TyBool)]
      in infer ctx (pe "f(x)") `shouldBe` Nothing

  describe "infer type application" $ do
    it "infers type application" $
      let ctx = [TypeN "id" (TyAll "a" (TyArr (TyVar "a") (TyVar "a")))]
      in infer ctx (pe "id @ int") `shouldBe`
           Just (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyInt))

  describe "infer if expressions" $ do
    it "infers if expression" $
      infer [] (pe "if true then 1 else 0")
        `shouldBe` Just (TyLit CoreFE.TyInt)

    it "fails if with non-bool condition" $
      let ctx = [TypeN "x" (TyLit CoreFE.TyInt)]
      in infer ctx (pe "if x then 1 else 0") `shouldBe` Nothing

    it "fails if with mismatched branches" $
      infer [] (pe "if true then 1 else false") `shouldBe` Nothing

  describe "infer binary ops" $ do
    it "infers addition" $
      infer [] (pe "1 + 2") `shouldBe` Just (TyLit CoreFE.TyInt)

    it "infers subtraction" $
      infer [] (pe "1 - 2") `shouldBe` Just (TyLit CoreFE.TyInt)

    it "infers multiplication" $
      infer [] (pe "2 * 3") `shouldBe` Just (TyLit CoreFE.TyInt)

    it "infers equality comparison" $
      infer [] (pe "1 == 2") `shouldBe` Just (TyLit CoreFE.TyBool)

    it "infers inequality comparison" $
      infer [] (pe "1 != 2") `shouldBe` Just (TyLit CoreFE.TyBool)

    it "infers less than" $
      infer [] (pe "1 < 2") `shouldBe` Just (TyLit CoreFE.TyBool)

    it "infers less equal" $
      infer [] (pe "1 <= 2") `shouldBe` Just (TyLit CoreFE.TyBool)

    it "infers greater than" $
      infer [] (pe "1 > 2") `shouldBe` Just (TyLit CoreFE.TyBool)

    it "infers greater equal" $
      infer [] (pe "1 >= 2") `shouldBe` Just (TyLit CoreFE.TyBool)

    it "fails addition with bool" $
      let ctx = [TypeN "x" (TyLit CoreFE.TyBool)]
      in infer ctx (pe "x + 1") `shouldBe` Nothing

  describe "infer records" $ do
    it "infers empty record" $
      infer [] (pe "{}") `shouldBe` Just (TyRcd [])

    it "infers record with fields" $
      infer [] (pe "{x = 1, y = true}")
        `shouldBe` Just (TyRcd [("x", TyLit CoreFE.TyInt), ("y", TyLit CoreFE.TyBool)])

    it "infers record projection" $
      let ctx = [TypeN "r" (TyRcd [("x", TyLit CoreFE.TyInt), ("y", TyLit CoreFE.TyBool)])]
      in infer ctx (pe "r.x") `shouldBe` Just (TyLit CoreFE.TyInt)

  describe "infer fenv" $ do
    it "infers empty fenv" $
      infer [] (FEnv []) `shouldBe` Just (TyCtx [])

    it "infers fenv with named expression" $
      infer [] (FEnv [ExpEN "x" (Lit (CoreFE.LitInt 1))])
        `shouldBe` Just (TyCtx [TypeN "x" (TyLit CoreFE.TyInt)])

    it "infers fenv with multiple named expressions" $
      infer [] (FEnv [ExpEN "x" (Lit (CoreFE.LitInt 1)),
                       ExpEN "y" (Lit (CoreFE.LitBool True))])
        `shouldBe` Just (TyCtx [TypeN "x" (TyLit CoreFE.TyInt),
                                 TypeN "y" (TyLit CoreFE.TyBool)])

    it "infers fenv with named type" $
      infer [] (FEnv [TypEN "t" (TyLit CoreFE.TyInt)])
        `shouldBe` Just (TyCtx [TypeN "t" (TyLit CoreFE.TyInt)])

    it "infers fenv where later entry references earlier" $
      infer [] (FEnv [ExpEN "y" (Var "x"),
                       ExpEN "x" (Lit (CoreFE.LitInt 42))])
        `shouldBe` Just (TyCtx [TypeN "y" (TyLit CoreFE.TyInt),
                                 TypeN "x" (TyLit CoreFE.TyInt)])

    it "fails fenv with unbound variable" $
      infer [] (FEnv [ExpEN "x" (Var "z")])
        `shouldBe` Nothing

  describe "infer annotations" $ do
    it "infers annotated expression" $
      infer [] (pe "(1 :: int)") `shouldBe` Just (TyLit CoreFE.TyInt)

    it "fails annotation with wrong type" $
      infer [] (pe "(1 :: bool)") `shouldBe` Nothing

  describe "infer lists" $ do
    it "infers non-empty list" $
      infer [] (pe "List[1, 2, 3]") `shouldBe` Just (TyList (TyLit CoreFE.TyInt))

    it "fails empty list (no type info)" $
      infer [] (pe "List[]") `shouldBe` Nothing

    it "fails list with mixed types" $
      infer [] (pe "List[1, true]") `shouldBe` Nothing

  describe "check lambda" $ do
    it "checks simple lambda" $
      check [] (pe "fun (x : int) -> x") (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyInt))
        `shouldBe` True

    it "checks lambda with unannotated arg" $
      check [] (pe "fun (x) -> x") (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyInt))
        `shouldBe` True

    it "checks type lambda" $
      check [] (pe "fun (type a) -> 2") (TyAll "a" (TyLit CoreFE.TyInt))
        `shouldBe` True

    it "rejects lambda with wrong return type" $
      check [] (pe "fun (x : int) -> true") (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyInt))
        `shouldBe` False

  describe "check fix" $ do
    it "checks fixpoint" $
      check [] (pe "fix f. fun (x : int) -> f(x)")
        (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyInt))
        `shouldBe` True

  describe "check lists" $ do
    it "checks non-empty list" $
      check [] (pe "List[1, 2]") (TyList (TyLit CoreFE.TyInt)) `shouldBe` True

    it "rejects list with wrong element type" $
      check [] (pe "List[true]") (TyList (TyLit CoreFE.TyInt)) `shouldBe` False

  describe "teq type equality" $ do
    it "teq for identical base types" $
      teq [] (TyLit CoreFE.TyInt) (TyLit CoreFE.TyInt) [] `shouldBe` True

    it "teq for different base types" $
      teq [] (TyLit CoreFE.TyInt) (TyLit CoreFE.TyBool) [] `shouldBe` False

    it "teq for arrow types" $
      teq [] (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyBool))
             (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyBool)) []
        `shouldBe` True

    it "teq resolves type aliases" $
      teq [TypeEqN "t" (TyLit CoreFE.TyInt)] (TyVar "t") (TyLit CoreFE.TyInt) []
        `shouldBe` True

    it "teq for forall types" $
      teq [] (TyAll "a" (TyVar "a")) (TyAll "b" (TyVar "b")) []
        `shouldBe` True

    it "teq for mu types" $
      teq [] (TyMu "a" (TyVar "a")) (TyMu "b" (TyVar "b")) []
        `shouldBe` True

  describe "infer fold/unfold (desugared)" $ do
    it "infers fold with TyMu type" $
      let ty = TyMu "X" (TySum [("Nil", TyLit CoreFE.TyUnit), ("Cons", TyLit CoreFE.TyInt)])
          ctx = []
      in infer ctx (Fold ty (DataCon "Nil" (Lit CoreFE.LitUnit) (typeSubstName "X" ty (TySum [("Nil", TyLit CoreFE.TyUnit), ("Cons", TyLit CoreFE.TyInt)]))))
        `shouldBe` Just ty

    it "infers unfold returns unfolded type" $
      let ty = TyMu "X" (TySum [("Nil", TyLit CoreFE.TyUnit), ("Cons", TyLit CoreFE.TyInt)])
          ctx = [TypeN "x" ty]
      in infer ctx (Unfold (Var "x"))
        `shouldBe` Just (typeSubstName "X" ty (TySum [("Nil", TyLit CoreFE.TyUnit), ("Cons", TyLit CoreFE.TyInt)]))

  describe "infer case (desugared)" $ do
    it "infers case expression on sum type" $
      let sumTy = TySum [("Nil", TyLit CoreFE.TyUnit), ("Cons", TyLit CoreFE.TyInt)]
          ctx = [TypeN "x" sumTy]
      in infer ctx (Case (Var "x") [CaseBranch "Nil" "u" (Lit (CoreFE.LitInt 0)),
                                     CaseBranch "Cons" "n" (Var "n")])
        `shouldBe` Just (TyLit CoreFE.TyInt)

  describe "infer DataCon (check mode)" $ do
    it "checks DataCon against sum type" $
      let sumTy = TySum [("Nil", TyLit CoreFE.TyUnit), ("Cons", TyLit CoreFE.TyInt)]
      in check [] (DataCon "Nil" (Lit CoreFE.LitUnit) sumTy) sumTy
        `shouldBe` True

    it "rejects DataCon with wrong payload" $
      let sumTy = TySum [("Nil", TyLit CoreFE.TyUnit), ("Cons", TyLit CoreFE.TyInt)]
      in check [] (DataCon "Nil" (Lit (CoreFE.LitInt 1)) sumTy) sumTy
        `shouldBe` False

  describe "infer modules" $ do
    it "infers simple struct module" $
        inferMod' "type t = int; let x : t = 1;"
            `shouldBe` Just
            [ TyDef "t" (TyLit CoreFE.TyInt)
            , ValDecl "x" (TyVar "t")
            ]

    it "infers struct with multiple lets" $
      inferMod' "let x : int = 1; let y : bool = true;"
        `shouldBe` Just [ValDecl "x" (TyLit CoreFE.TyInt),
                         ValDecl "y" (TyLit CoreFE.TyBool)]

    it "infers let with type alias usage" $
      inferMod' "type t = int; let x : t = 1;"
        `shouldBe` Just [TyDef "t" (TyLit CoreFE.TyInt),
                         ValDecl "x" (TyVar "t")]

  describe "checkMod" $ do
    it "checks struct against sig" $
      let ctx = []
          m = Struct [TypDecl "t" (TyLit CoreFE.TyInt),
                      Let "x" (Just (TyVar "t")) (Lit (CoreFE.LitInt 1))]
          mty = TySig [TyDef "t" (TyLit CoreFE.TyInt),
                        ValDecl "x" (TyVar "t")]
      in checkMod ctx m mty `shouldBe` True

    it "checks functor against arrow module type" $
      let ctx = []
          m = Functor [("x", TmArgType (TyLit CoreFE.TyInt))]
                       (Struct [Let "y" (Just (TyLit CoreFE.TyInt)) (Var "x")])
          mty = TyArrowM (TyLit CoreFE.TyInt)
                          (TySig [ValDecl "y" (TyLit CoreFE.TyInt)])
      in checkMod ctx m mty `shouldBe` True

    it "checks functor with type arg against ForallM" $
      let ctx = []
          m = Functor [("a", TyArg)]
                       (Struct [Let "id" (Just (TyArr (TyVar "a") (TyVar "a")))
                                 (Lam [("x", TmArgType (TyVar "a"))] (Var "x"))])
          mty = ForallM "a" (TySig [ValDecl "id" (TyArr (TyVar "a") (TyVar "a"))])
      in checkMod ctx m mty `shouldBe` True

  describe "full module type checking (parsed)" $ do
    it "infers simple module" $ do
      let input = "let x : int = 42;"
      let m = desugarModule (parseModule (lexer input))
      case m of
        Struct structs -> inferStructs [] structs
          `shouldBe` Just [ValDecl "x" (TyLit CoreFE.TyInt)]
        _ -> expectationFailure "Expected Struct"

    it "infers module with type decl" $ do
      let input = "type t = int; let x : t = 42;"
      let m = desugarModule (parseModule (lexer input))
      case m of
        Struct structs -> inferStructs [] structs
          `shouldBe` Just [TyDef "t" (TyLit CoreFE.TyInt),
                           ValDecl "x" (TyVar "t")]
        _ -> expectationFailure "Expected Struct"

    it "infers module with function" $ do
      let input = "let f : int -> int = fun (x : int) -> x;"
      let m = desugarModule (parseModule (lexer input))
      case m of
        Struct structs -> inferStructs [] structs
          `shouldBe` Just [ValDecl "f" (TyArr (TyLit CoreFE.TyInt) (TyLit CoreFE.TyInt))]
        _ -> expectationFailure "Expected Struct"

    it "infers annotated module" $ do
      let input = "module m : sig type t = int; val y : t; end = struct type t = int; let y : t = 10; end;"
      let m = desugarModule (parseModule (lexer input))
      case m of
        Struct structs -> inferStructs [] structs `shouldSatisfy` isJust
        _ -> expectationFailure "Expected Struct"

    it "infers polymorphic identity functor" $ do
      let input = unlines
            [ "module type POLICY = forall t. sig val trans : t -> t; end;"
            , "module policy1 : POLICY = functor (type t) -> struct let trans : t -> t = fun (x) -> x; end;"
            ]
      let m = desugarModule (parseModule (lexer input))
      case m of
        Struct structs -> inferStructs [] structs `shouldSatisfy` isJust
        _ -> expectationFailure "Expected Struct"

