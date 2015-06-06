module Main where

import Control.Monad (unless)
import Control.Monad.Error.Class (throwError)


{-  Abstract syntax
    ===============

    e, ρ, κ := e :: ρ         Annotated term
             | *              Type of types
             | ∀x :: ρ.ρ'     Dependent function space
             | x              Variable
             | e e'           Application
             | λx -> e        Lambda abstraction

    v, τ := n                 Neutral term
          | *                 Type of types
          | ∀x :: τ.τ'        Dependent function space
          | λx -> e           Lambda abstraction

    n := x                    Variable
       | n v                  Application
-}

data TermI    -- Inferable term
  = Ann TermC TermC
  | Star
  | Pi TermC TermC
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

data Value
  = VLam (Value -> Value)
  | VStar
  | VPi Value (Value -> Value)
  | VNeutral Neutral

data Neutral
  = NFree Name
  | NApp Neutral Value

vfree :: Name -> Value
vfree n = VNeutral (NFree n)


{-  Evaluation
    ==========

      e => v
    -----------
    e :: ρ => v


    ------
    * => *

       ρ => τ    ρ' => τ'
    ------------------------
    ∀x :: ρ.ρ' => ∀x :: τ.τ'

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
evalI Star       d = VStar
evalI (Pi t t')  d = VPi (evalC t d) (\x -> evalC t' (x : d))
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
       | Γ, x :: τ    Adding a variable


    --------
    valid(ε)

    valid(Γ)    Γ |- τ ::C *
    ------------------------
        valid(Γ, x :: τ)
-}

type Type    = Value
type Context = [(Name, Type)]


{-  Type checking
    =============

    Γ |- ρ ::C *    ρ => τ    Γ |- e ::C τ
    --------------------------------------  (ANN)
              Γ |- (e :: ρ) ::I τ


    ------------  (STAR)
    Γ |- * ::I *

    Γ |- ρ ::C *    ρ => τ    Γ, x :: τ |- ρ' ::C *
    -----------------------------------------------  (PI)
                 Γ |- ∀x :: ρ.ρ' ::I *

      Γ(x) = τ
    ------------  (VAR)
    Γ |- x ::I τ

    Γ |- e ::I ∀x τ.τ'    Γ |- e' ::C τ    τ'[x / e'] => τ''
    --------------------------------------------------------  (APP)
                         Γ |- e e' ::I τ''

    Γ |- e ::I τ
    ------------  (CHK)
    Γ |- e ::C τ

       Γ, x :: τ |- e ::C τ'
    ---------------------------  (LAM)
    Γ |- λx -> e ::C ∀x :: τ.τ'
-}

type Result a = Either String a

evalC0 :: TermC -> Value    -- NOTE: Assumes no unbound variables in e
evalC0 e = evalC e []

typeI0 :: Context -> TermI -> Result Type
typeI0 = typeI 0

typeI :: Int -> Context -> TermI -> Result Type
typeI i c (Ann e r)
  = do typeC i c r VStar
       let t = evalC0 r
       typeC i c e t
       return t
typeI i c Star
  = return VStar
typeI i c (Pi r r')
  = do typeC i c r VStar
       let t = evalC0 r
       typeC (i + 1) ((Local i, t) : c)
             (substC 0 (Free (Local i)) r') VStar
       return VStar
typeI i c (Free x)
  = case lookup x c of
      Just t  -> return t
      Nothing -> throwError "unknown identifier"
typeI i c (e :@: e')
  = do s <- typeI i c e
       case s of
         VPi t t' -> do typeC i c e' t
                        return (t' (evalC0 e'))
         _        -> throwError "illegal application"

typeC :: Int -> Context -> TermC -> Type -> Result ()
typeC i c (Inf e) v
  = do v' <- typeI i c e
       unless (quote0 v == quote0 v') (throwError "type mismatch")
typeC i c (Lam e) (VPi t t')
  = typeC (i + 1) ((Local i, t) : c)
          (substC 0 (Free (Local i)) e) (t' (vfree (Local i)))
typeC i c _ _
  = throwError "type mismatch"

substI :: Int -> TermI -> TermI -> TermI
substI i r (Ann e t)  = Ann (substC i r e) t
substI i r Star       = Star
substI i r (Pi t t')  = Pi (substC i r t) (substC (i + 1) r t')
substI i r (Bound j)  = if i == j then r else Bound j
substI i r (Free y)   = Free y
substI i r (e :@: e') = substI i r e :@: substC i r e'

substC :: Int -> TermI -> TermC -> TermC
substC i r (Inf e) = Inf (substI i r e)
substC i r (Lam e) = Lam (substC (i + 1) r e)


{-  Quotation
    =========
-}

quote0 :: Value -> TermC
quote0 = quote 0

quote :: Int -> Value -> TermC
quote i (VLam f)     = Lam (quote (i + 1) (f (vfree (Quote i))))
quote i VStar        = Inf Star
quote i (VPi v f)    = Inf (Pi (quote i v) (quote (i + 1) (f (vfree (Quote i)))))
quote i (VNeutral n) = Inf (neutralQuote i n)

neutralQuote :: Int -> Neutral -> TermI
neutralQuote i (NFree x)  = boundfree i x
neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v

boundfree :: Int -> Name -> TermI
boundfree i (Quote k) = Bound (i - k - 1)
boundfree i x         = Free x


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

free :: String -> TermC
free x = Inf (Free (Global x))

env1, env2 :: Context
env1 = [(Global "y", vfree (Global "a")),
        (Global "a", VStar)]
env2 = [(Global "b", VStar)] ++ env1

term1, term2 :: TermI
term1 = Ann id' (Inf (Pi (free "a") (free "a"))) :@: free "y"
term2 = Ann const' (Inf (Pi (Inf (Pi (free "b") (free "b")))
                            (Inf (Pi (free "a")
                                     (Inf (Pi (free "b") (free "b")))))))
        :@: id' :@: free "y"


-- >> quote0 (evalI term1 [])
-- Inf (Free (Global "y"))

-- >> quote0 (evalI term2 [])
-- Lam (Inf (Bound 0))

-- >> let Right t = typeI0 env1 term1 in quote0 t
-- Inf (Free (Global "a"))

-- >> let Right t = typeI0 env2 term2 in quote0 t
-- Inf (Pi (Inf (Free (Global "b"))) (Inf (Free (Global "b"))))
