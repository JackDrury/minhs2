{-

z5199922

COMP9164

Assignment 2 - Type Inference for MinHS

-}

module MinHS.TyInfer where

import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Subst
import MinHS.TCMonad

import Data.Monoid (Monoid (..), (<>))
import Data.Foldable (foldMap)
import Data.List (nub, union, (\\))

primOpType :: Op -> QType
primOpType Gt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ge   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Lt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Le   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Eq   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ne   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Neg  = Ty $ Base Int `Arrow` Base Int
primOpType Fst  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "a"
primOpType Snd  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "b"
primOpType _    = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Int)

constType :: Id -> Maybe QType
constType "True"  = Just $ Ty $ Base Bool
constType "False" = Just $ Ty $ Base Bool
constType "()"    = Just $ Ty $ Base Unit
constType "Pair"  = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "b" `Arrow` (TypeVar "a" `Prod` TypeVar "b"))
constType "Inl"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType "Inr"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "b" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType _       = Nothing

type Gamma = E.Env QType

initialGamma :: Gamma
initialGamma = E.empty

tv :: Type -> [Id]
tv = tv'
 where
   tv' (TypeVar x) = [x]
   tv' (Prod  a b) = tv a `union` tv b
   tv' (Sum   a b) = tv a `union` tv b
   tv' (Arrow a b) = tv a `union` tv b
   tv' (Base c   ) = []

tvQ :: QType -> [Id]
tvQ (Forall x t) = filter (/= x) $ tvQ t
tvQ (Ty t) = tv t

tvGamma :: Gamma -> [Id]
tvGamma = nub . foldMap tvQ

infer :: Program -> Either TypeError Program
infer program = do (p',tau, s) <- runTC $ inferProgram initialGamma program
                   return p'

unquantify :: QType -> TC Type
{-
Normally this implementation would be possible:

unquantify (Ty t) = return t
unquantify (Forall x t) = do x' <- fresh
                             unquantify (substQType (x =:x') t)

However as our "fresh" names are not checked for collisions with names bound in the type
we avoid capture entirely by first replacing each bound
variable with a guaranteed non-colliding variable with a numeric name,
and then substituting those numeric names for our normal fresh variables
-}

unquantify = unquantify' 0 emptySubst
unquantify' :: Int -> Subst -> QType -> TC Type
unquantify' i s (Ty t) = return $ substitute s t
unquantify' i s (Forall x t) = do x' <- fresh
                                  unquantify' (i + 1)
                                              ((show i =: x') <> s)
                                              (substQType (x =:TypeVar (show i)) t)





-- so to unify we address all of the cases from the lecture
-- beginning with two type variables that are either equal or not
unify :: Type -> Type -> TC Subst

unify (TypeVar var1) (TypeVar var2)   = if var1 == var2
                                           then return emptySubst
                                           else return (var1 =: (TypeVar var2))


-- Then we have two base types that are either equal or not
unify (Base c1) (Base c2)             = if c1   == c2
                                           then return emptySubst
                                           else typeError (TypeMismatch (Base c1) (Base c2))

-- Then the case of sum types which requires a multi-stage
-- unification process (separately unifying both parts of the sum)
unify (Sum t11 t12) (Sum t21 t22)   = do s1 <- (unify           t11             t21)
                                         s2 <- (unify (substitute s1 t12) (substitute s1 t22))
                                         return (s1 <> s2)

-- We then repeat the same thing for product types:
unify (Prod t11 t12) (Prod t21 t22)   = do s1 <- (unify           t11             t21)
                                           s2 <- (unify (substitute s1 t12) (substitute s1 t22))
                                           return (s1 <> s2)

-- And again for function types:
unify (Arrow t11 t12) (Arrow t21 t22)   = do s1 <- (unify           t11             t21)
                                         s2 <- (unify (substitute s1 t12) (substitute s1 t22))
                                         return (s1 <> s2)

-- Now we have the case that only one of the arguments is a type variable and
-- the other is any type term. We need to fail if the variable occurs in the term
-- Because then we would get stuck in an infinitely expanding unification:
unify (Type t) (TypeVar var)    = if var `elem` (tv t)
                                     then typeError (OccursCheckFailed var t)
                                     else return (var =: t)

-- Then repeat for the position of typevar and type swapped:
unify (TypeVar var) (Type t)    = if var `elem` (tv t)
                                     then typeError (OccursCheckFailed var t)
                                     else return (var =: t)

--If none of these cases work then we cannot unify the two types:
unify t1 t2 = typeError (TypeMismatch t1 t2)








-- From the spec, generalise is:
-- Generalise(Γ,τ)  =∀(TV(τ)\TV(Γ)). τ
-- This can be implemented as ===================================================================
generalise :: Gamma -> Type -> QType
generalise g t = error "implement me"






-- ==============================================================================================
inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram env bs = error "implement me! don't forget to run the result substitution on the"
                            "entire expression using allTypes from Syntax.hs"





inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)


-- So we now get to adding all of the inference rules listed in the assignment.
-- We begin with the simplest, a constant:
inferExp g (Num n) = return (Num n, Base Int, emptySubst)

-- Next we handle variables, where (just like in assignment 1) we must look up
-- the variable in our environment
inferExp g (Var x) = if (E.lookup g x) == Just t
                        then do unQt <- unqunatify t
                                return (Var x, unQt, emptySubst)
                        else typeError (NoSuchVariable x)


-- Then we have to handle primitive operators which is simply
-- using fresh variables for the quantified types:
inferExp g (Prim o) = do unQt <- unquantify (PrimOpType o)
                         return (Prim o, unQt, emptySubst)

                      



-- FROM THE LECTURE:

inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)
inferExp g (App e1 e2) = do
  (e1', tau1, tee)  <- inferExp g e1
  (es', tau2, tee') <- inferExp (substGamma tee g) e2
  alpha             <- fresh
  let lhs = substitute tee' tau1
      rhs = Arrow tau2 alpha
      u   = unify lhs rhs
  in return (App e1' e2', substitute u alpha, u <> tee' <> tee)

-- Will need to be altered


inferExp g _ = error "Implement me!"
-- -- Note: this is the only case you need to handle for case expressions
-- inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2])
-- inferExp g (Case e _) = typeError MalformedAlternatives
