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
unify t (TypeVar var)    = if var `elem` (tv t)
                              then typeError (OccursCheckFailed var t)
                              else return (var =: t)

-- Then repeat for the position of typevar and type swapped:
unify (TypeVar var) t    = if var `elem` (tv t)
                              then typeError (OccursCheckFailed var t)
                              else return (var =: t)

--If none of these cases work then we cannot unify the two types:
unify t1 t2 = typeError (TypeMismatch t1 t2)








-- From the spec, generalise is:
-- Generalise(Γ,τ)  =∀(TV(τ)\TV(Γ)). τ
-- This can be implemented as:
generalise :: Gamma -> Type -> QType
generalise g tau = foldl (\tau' x -> Forall x tau') (Ty tau) iter
                         where iter = reverse (filter (\y -> not (y `elem` (tvGamma g))) (tv tau))

generalise g t = error "implement me"






-- We now implement infer program
inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)
inferProgram g [Bind str _ [] e] = do
  (e', tau, tee) <- inferExp g e
  let retExp      = allTypes (substQType tee) e'
      retTy       = Just (generalise g tau)
  return ([Bind str retTy [] retExp], tau, tee)
inferProgram _ _ = error "Somehow you couldn't pattern match inferProgram"




inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)


-- So we now get to adding all of the inference rules listed in the assignment.
-- We begin with the simplest, a constant:
inferExp g (Num n) = return (Num n, Base Int, emptySubst)

-- Next we handle variables, where (just like in assignment 1) we must look up
-- the variable in our environment
inferExp g (Var x) = case (E.lookup g x) of Just t  -> do unQt <- unquantify t
                                                          return (Var x, unQt, emptySubst)
                                            _       -> typeError (NoSuchVariable x)

-- Then we have to handle primitive operators which is simply
-- using fresh variables for the quantified types:
inferExp g (Prim o) = do unQt <- unquantify (PrimOpType o)
                         return (Prim o, unQt, emptySubst)


-- Then handle the constructors which is very similar to the primops
-- except we need to include an error condition
inferExp g (Con c) = case (constType c) of Just t -> do unQt <- unquantify t
                                                        return (Con c, unQt, emptySubst)
                                           _      -> typeError (NosSuchConstructor c)

-- Next we handle application. We only need to slightly
-- modify the example from the lectures by
-- unpacking the unification from TC:
inferExp g (App e1 e2) = do
  (e1', tau1, tee)  <- inferExp g e1
  (e2', tau2, tee') <- inferExp (substGamma tee g) e2
  alpha             <- fresh
  let lhs            = substitute tee' tau1
      rhs            = Arrow tau2 alpha
  u                 <- unify lhs rhs
  return (App e1' e2', substitute u alpha, u <> tee' <> tee)  


-- Next we handle If-Then-Else statements, which will have
-- a similar structure to the application:
inferExp g (If e e1 e2) = do
  (e', tau, tee)    <- inferExp g e
  u                 <- unify tau (Base Bool)
  (e1', tau1, tee1) <- inferExp (substGamma (u <> tee) g) e1
  (e2', tau2, tee2) <- inferExp (substGamma (tee1 <> u <> tee) g) e2
  let lhs            = substitute tee2 tau1
  u'                <- unify lhs tau2
  return (If e' e1' e2', substitute u' tau2, u' <> tee2 <> tee1 <> u <> tee)


-- Then we handle the only non-error-raising case statement:
inferExp g (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2]) = do
  (e', tau, tee)    <- inferExp g e
  alphaL            <- fresh
  (e1', tauL, tee1) <- inferExp (substGamma tee (E.add g (x, Ty alphaL))) e1
  alphaR            <- fresh
  (e2', tauR, tee2) <- inferExp (substGamma (tee <> tee1) (E.add g (y, Ty alphaR))) e2
  let lhs            = substitute (tee2 <> tee1 <> tee) (Sum alphaL alphaR)
      rhs            = substitute (tee2 <> tee1) tau
  u                 <- unify lhs rhs
  let lhs'           = substitute (u <> tee2) tauL
      rhs'           = substitute u tauR
  u'                <- unify lhs' rhs'
  let retTy          = substitute (u' <> u) tauR
      retSub         = u' <> u <> tee2 <> tee1 <> tee
  return (Case e' [Alt "Inl" [x] e1', Alt "Inr" [y] e2'], retTy, retSub)

inferExp g (Case e _) = typeError MalformedAlternatives  

-- Next up we need to handle the recfun statements:
-- I am not sure that I have made the substitutions correctly ============================
-- ============================= do we assume only a single argument x????????????????????
-- ============================== Should we also consider no argument?
-- How about different starting types?
inferExp g (Recfun (Bind f _ [x] e)) = do
  alpha1         <- fresh
  alpha2         <- fresh
  let g'          = E.addAll g [(x, Ty alpha1), (f, Ty alpha2)]
  (e', tau, tee) <- inferExp g' e
  let lhs         = substitute tee alpha2
      rhs         = Arrow (substitute tee alpha1) tau
  u              <- unify lhs rhs
  let retTy       = substitute u (Arrow (substitute tee alpha1) tau)
      retSub      = u <> tee
  return (Recfun (Bind f (Just (return (generalise g' retTy))) [x] e'),retTy, retSub)


-- Finally we handle let expressions:
inferExp g (Let [Bind x _ [] e1] e2) = do
  (e1', tau, tee)  <- inferExp g e1
  let g'            = E.add (substGamma tee g) (x, generalise (substGamma tee g) tau)
  (e2', tau',tee') <- inferExp g' e2
  return (Let [Bind x (Just (return (generalise g' tau))) [] e1'] e2', tau', tee' <> tee)


inferExp g _ = error "Implement me! (You missed some cases, duh!)"



