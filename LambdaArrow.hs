module Main where

import Control.Monad (unless)
import Control.Monad.Error.Class (throwError)


{-  Abstract syntax
    ===============

    τ := α          Base type
       | τ -> τ'    Function type

    e := e :: τ     Annotated term
       | x          Variable
       | e e'       Application
       | λx -> e    Lambda abstraction

    v := n          Neutral term
       | λx -> e    Lambda abstraction

    n := x          Variable
       | n v        Application
-}

data TermI    -- Inferable term
  = Ann TermC Type
  | Bound Int
  | Free Name
  | TermI :@: TermC
  deriving (Show, Eq)

data TermC    -- Checkable term
  = Inf TermI
  | Lam TermC
  deriving (Show, Eq)

data Name
  = Global String
  | Local Int
  | Quote Int
  deriving (Show, Eq)

data Type
  = TFree Name
  | Fun Type Type
  deriving (Show, Eq)

data Value
  = VLam (Value -> Value)
  | VNeutral Neutral

data Neutral
  = NFree Name
  | NApp Neutral Value

vfree :: Name -> Value
vfree n = VNeutral (NFree n)


{-  Quotation
    =========
-}

quote0 :: Value -> TermC
quote0 = quote 0

quote :: Int -> Value -> TermC
quote i (VLam f)     = Lam (quote (i + 1) (f (vfree (Quote i))))
quote i (VNeutral n) = Inf (neutralQuote i n)

neutralQuote :: Int -> Neutral -> TermI
neutralQuote i (NFree x)  = boundfree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v

boundfree :: Int -> Name -> TermI
boundfree i (Quote k) = Bound (i - k - 1)
boundfree i x         = Free x


{-  Evaluation
    ==========

      e => v
    -----------
    e :: τ => v


    ------
    x => x

    e => λx -> v    v[x / e'] -> v'
    -------------------------------
              e e' => v'

    e => n    e' => v'
    ------------------
       e e' => n v'

          e => v
    ------------------
    λx -> e => λx -> v
-}

type Env = [Value]

evalI :: TermI -> Env -> Value
evalI (Ann e _)  d = evalC e d
evalI (Free x)   d = vfree x
evalI (Bound i)  d = d !! i
evalI (e :@: e') d = vapp (evalI e d) (evalC e' d)

vapp :: Value -> Value -> Value
vapp (VLam f)     v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

evalC :: TermC -> Env -> Value
evalC (Inf i) d = evalI i d
evalC (Lam e) d = VLam (\x -> evalC e (x : d))


{-  Contexts
    ========

    Γ := ε            Empty context
       | Γ, α :: *    Adding a type identifier
       | Γ, x :: τ    Adding a term identifier


    --------
    valid(ε)

       valid(Γ)
    ----------------
    valid(Γ, α :: *)

    valid(Γ)    Γ |- τ :: *
    -----------------------
        valid(Γ, x :: τ)

     Γ(α) = *
    -----------  (TVAR)
    Γ |- α :: *

    Γ |- τ :: *    Γ |- τ' :: *
    ---------------------------  (FUN)
         Γ |- τ -> τ' :: *
-}

data Kind
  = Star
  deriving (Show)

data Info
  = HasKind Kind
  | HasType Type
  deriving (Show)

type Context = [(Name, Info)]


{-  Type checking
    =============

    Γ |- τ :: *    Γ |- e ::C τ
    ---------------------------  (ANN)
        Γ |- (e :: τ) ::I τ

      Γ(x) = τ
    ------------  (VAR)
    Γ |- x ::I τ

    Γ |- e ::I τ -> τ'    Γ |- e' ::C τ
    -----------------------------------  (APP)
              Γ |- e e' ::I τ'

    Γ |- e ::I τ
    ------------  (CHK)
    Γ |- e ::C τ

     Γ, x :: τ |- e ::C τ'
    ------------------------  (LAM)
    Γ |- λx -> e ::C τ -> τ'
-}

type Result a = Either String a

kindC :: Context -> Type -> Kind -> Result ()
kindC c (TFree x) Star
   = case lookup x c of
       Just (HasKind Star) -> return ()
       Nothing             -> throwError "unknown identifier"
kindC c (Fun k k') Star
  = do kindC c k Star
       kindC c k' Star

typeI0 :: Context -> TermI -> Result Type
typeI0 = typeI 0

typeI :: Int -> Context -> TermI -> Result Type
typeI i c (Ann e t)
  = do kindC c t Star
       typeC i c e t
       return t
typeI i c (Free x)
  = case lookup x c of
      Just (HasType t) -> return t
      Nothing          -> throwError "unknown identifier"
typeI i c (e :@: e')
  = do s <- typeI i c e
       case s of
         Fun t t' -> do typeC i c e' t
                        return t'
         _        -> throwError "illegal application"

typeC :: Int -> Context -> TermC -> Type -> Result ()
typeC i c (Inf e) t
  = do t' <- typeI i c e
       unless (t == t') (throwError "type mismatch")
typeC i c (Lam e) (Fun t t')
  = typeC (i + 1) ((Local i, HasType t) : c)
          (substC 0 (Free (Local i)) e) t'
typeC i c _ _
  = throwError "type mismatch"

substI :: Int -> TermI -> TermI -> TermI
substI i r (Ann e t)  = Ann (substC i r e) t
substI i r (Bound j)  = if i == j then r else Bound j
substI i r (Free y)   = Free y
substI i r (e :@: e') = substI i r e :@: substC i r e'

substC :: Int -> TermI -> TermC -> TermC
substC i r (Inf e) = Inf (substI i r e)
substC i r (Lam e) = Lam (substC (i + 1) r e)


{-  Examples
    ========

    >> assume (α :: *) (y :: α)
    >> ((λx -> x) :: α -> α) y
    y :: α

    >> assume (β :: *)
    >> ((λx y -> x) :: (β -> β) -> α -> β -> β) (λx -> x) y
    λx -> x :: β -> β
-}

id', const' :: TermC
id'    = Lam (Inf (Bound 0))
const' = Lam (Lam (Inf (Bound 1)))

tfree :: String -> Type
tfree a = TFree (Global a)

free :: String -> TermC
free x = Inf (Free (Global x))

env1, env2 :: Context
env1 = [(Global "y", HasType (tfree "a")),
        (Global "a", HasKind Star)]
env2 = [(Global "b", HasKind Star)] ++ env1

term1, term2 :: TermI
term1 = Ann id' (Fun (tfree "a") (tfree "a")) :@: free "y"
term2 = Ann const' (Fun (Fun (tfree "b") (tfree "b"))
                        (Fun (tfree "a")
                             (Fun (tfree "b") (tfree "b"))))
        :@: id' :@: free "y"


-- >> quote0 (evalI term1 [])
-- Inf (Free (Global "y"))

-- >> quote0 (evalI term2 [])
-- Lam (Inf (Bound 0))

-- >> let Right t = typeI0 env1 term1 in t
-- TFree (Global "a")

-- >> let Right t = typeI0 env2 term2 in t
-- Fun (TFree (Global "b")) (TFree (Global "b"))
