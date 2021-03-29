module Language.Itse.Typechecking_Old where

-- import Control.Monad.Except
-- import Control.Monad.Trans
-- import Language.Itse.Grammar
-- import Text.Printf

-- {-
-- ## Control Flow
-- -}

-- type M = Except E

-- type E = String

-- {-
-- ## Contexts
-- -}

-- data Context
--   = Context_Empty
--   | Context_Typing Context (Name Term) Type
--   | Context_Kinding Context (Name Type) Kind
--   | Context_Closure Context Closure

-- {-
-- ## Closures
-- -}

-- -- laws:
-- -- - no (mutually) recursive mappings
-- -- - terms are bound to closed terms
-- -- - types are bound to types closed in domain(closure)
-- data Closure = Closure
--   { termBindings :: [(Name Term, Type, Term)],
--     typeBindings :: [(Name Type, Kind, Type)]
--   }

-- {-
-- ## Free Names
-- -}

-- freeNameTms :: Expr a -> [Name Term]
-- freeNameTms (Term _a) = case _a of
--   Term_Ref x -> [x]
--   Term_AbsTm x t a -> (freeNameTms (Type t) ++ freeNameTms (Term a)) `withoutName` x
--   Term_AppTm a b -> freeNameTms (Term a) ++ freeNameTms (Term b)
-- freeNameTms (Type _t) = case _t of
--   Type_Ref _ -> []
--   Type_AllTy _ k t -> freeNameTms (Kind k) ++ freeNameTms (Type t)
--   Type_PiTm x s t -> (freeNameTms (Type s) ++ freeNameTms (Type t)) `withoutName` x
--   Type_AllTm x s t -> (freeNameTms (Type s) ++ freeNameTms (Type t)) `withoutName` x
--   Type_Iota x t -> freeNameTms (Type t) `withoutName` x
--   Type_AppTm t a -> freeNameTms (Type t) ++ freeNameTms (Term a)
--   Type_AbsTy _ k t -> freeNameTms (Kind k) ++ freeNameTms (Type t)
--   Type_AbsTm x s t -> (freeNameTms (Type s) ++ freeNameTms (Type t)) `withoutName` x
--   Type_AppTy s t -> freeNameTms (Type s) ++ freeNameTms (Type t)
-- freeNameTms (Kind _k) = case _k of
--   Kind_Unit -> []
--   Kind_AbsTm x t k -> (freeNameTms (Type t) ++ freeNameTms (Kind k)) `withoutName` x
--   Kind_AbsTy _ k l -> freeNameTms (Kind k) ++ freeNameTms (Kind l)

-- freeNameTys :: Expr a -> [Name Type]
-- freeNameTys (Term _a) = case _a of
--   Term_Ref _ -> []
--   Term_AbsTm _ t a -> freeNameTys (Type t) ++ freeNameTys (Term a)
--   Term_AppTm a b -> freeNameTys (Term a) ++ freeNameTys (Term b)
-- freeNameTys (Type _t) = case _t of
--   Type_Ref x -> [x]
--   Type_AllTy x k t -> (freeNameTys (Kind k) ++ freeNameTys (Type t)) `withoutName` x
--   Type_PiTm _ s t -> freeNameTys (Type s) ++ freeNameTys (Type t)
--   Type_AllTm _ s t -> freeNameTys (Type s) ++ freeNameTys (Type t)
--   Type_Iota _ t -> freeNameTys (Type t)
--   Type_AppTm t a -> freeNameTys (Type t) ++ freeNameTys (Term a)
--   Type_AbsTy x k t -> (freeNameTys (Kind k) ++ freeNameTys (Type t)) `withoutName` x
--   Type_AbsTm _ s t -> freeNameTys (Type s) ++ freeNameTys (Type t)
--   Type_AppTy s t -> freeNameTys (Type s) ++ freeNameTys (Type t)
-- freeNameTys (Kind _k) = case _k of
--   Kind_Unit -> []
--   Kind_AbsTm _ t k -> freeNameTys (Type t) ++ freeNameTys (Kind k)
--   Kind_AbsTy x k l -> (freeNameTys (Kind k) ++ freeNameTys (Kind l)) `withoutName` x

-- withoutName :: [Name a] -> Name a -> [Name a]
-- withoutName xs x = filter (x /=) xs

-- {-
-- ## Well-formedness
-- -}

-- checkWellFormedContext :: Context -> M ()
-- checkWellFormedContext _ctx = case _ctx of
--   Context_Empty ->
--     return ()
--   Context_Typing ctx x t -> do
--     checkWellFormedContext ctx
--     checkKind ctx t Kind_Unit
--   Context_Kinding ctx x k -> do
--     checkWellFormedContext ctx
--     checkWellFormedKind ctx k
--   Context_Closure ctx clo ->
--     checkWellFormedClosure ctx clo

-- checkWellFormedClosure :: Context -> Closure -> M ()
-- checkWellFormedClosure ctx clo = do
--   mapM_
--     (\(_, t, a) -> checkType (Context_Closure ctx clo) a t)
--     $ termBindings clo
--   mapM_
--     (\(_, k, t) -> checkKind (Context_Closure ctx clo) t k)
--     $ typeBindings clo

-- checkWellFormedKind :: Context -> Kind -> M ()
-- checkWellFormedKind ctx _k = case _k of
--   Kind_Unit ->
--     return ()
--   Kind_AbsTy x k l -> do
--     checkWellFormedKind (Context_Kinding ctx x k) l
--     checkWellFormedKind ctx k
--   Kind_AbsTm x t k -> do
--     checkWellFormedKind (Context_Typing ctx x t) k
--     checkKind ctx t Kind_Unit

-- {-
-- ## Kinding
-- -}

-- checkKind :: Context -> Type -> Kind -> M ()
-- checkKind ctx t k = do
--   checkWellFormedKind ctx k
--   k' <- synthesizeKind ctx t
--   unify (Kind k) (Kind k')

-- synthesizeKind :: Context -> Type -> M Kind
-- synthesizeKind ctx _t = case _t of
--   -- x
--   Type_Ref x ->
--     -- ctx |- x : k in ctx
--     synthesizeKind_NameTy ctx x
--   -- forall x : k . t
--   Type_AllTy x k t -> do
--     -- ctx |- k WF
--     checkWellFormedKind ctx k
--     -- ctx, x :: k |- t :: *
--     checkKind (Context_Kinding ctx x k) t Kind_Unit
--     -- ctx |- forall x : k . t :: *
--     return Kind_Unit
--   -- Π x : s . t
--   Type_PiTm x s t -> do
--     -- ctx |- t : *
--     checkKind ctx t Kind_Unit
--     -- ctx, x :: s |- t :: *
--     checkKind (Context_Typing ctx x s) t Kind_Unit
--     -- ctx |- Π x : s . t :: *
--     return Kind_Unit
--   -- forall x : s . t
--   Type_AllTm x s t -> do
--     -- ctx, x :: s |- t :: *
--     checkKind (Context_Typing ctx x s) t Kind_Unit
--     -- ctx |- s :: *
--     checkKind ctx s Kind_Unit
--     -- ctx |- forall x : s . t :: *
--     return Kind_Unit
--   -- ι x . t
--   Type_Iota x t -> do
--     -- ctx, x :: ι x . t |- t :: *
--     checkKind (Context_Typing ctx x (Type_Iota x t)) t Kind_Unit
--     -- ctx |- ι x . t :: *
--     return Kind_Unit
--   -- s a
--   Type_AppTm s a -> do
--     -- ctx |- s :: Π x : t . k
--     (x, t, k) <-
--       synthesizeKind ctx s >>= \case
--         Kind_AbsTm x t k -> return (x, t, k)
--         k -> throwError $ printf "invalid dependent type application applicant: %s :: %s" (show s) (show k)
--     -- ctx |- a :: s
--     checkType ctx a s
--     -- ctx |- s a :: [x => a] k
--     return . fromExpr $ substitute x (Term a) (Kind k)
--   -- λ x : k . t
--   Type_AbsTy x k t -> do
--     -- ctx, x :: k |- t :: k'
--     k' <- synthesizeKind (Context_Kinding ctx x k) t
--     -- ctx |- k WF
--     checkWellFormedKind ctx k
--     -- ctx |- forall x : k . t :: Π x : k . k'
--     return $ Kind_AbsTy x k k'
--   -- λ x : s . t
--   Type_AbsTm x s t -> do
--     -- ctx, x :: s |- t :: k
--     k <- synthesizeKind (Context_Typing ctx x s) t
--     -- ctx |- t :: *
--     checkKind ctx t Kind_Unit
--     -- ctx |- λ x : s . t :: Π x : s . k
--     return $ Kind_AbsTm x s k
--   -- s t
--   Type_AppTy s t -> do
--     -- ctx |- s :: Π x : k . l
--     (x, k, l) <-
--       synthesizeKind ctx s >>= \case
--         Kind_AbsTy x k l -> return (x, k, l)
--         k -> throwError $ printf "invalid type application applicant: %s :: %s" (show s) (show k)
--     -- ctx |- t :: k
--     checkKind ctx t k
--     -- ctx |- s t :: [x => t] l
--     return . fromExpr $ substitute x (Type t) (Kind l)

-- {-
-- ## Typing
-- -}

-- -- TODO: somehow need to use `choice` in order to "match" on certain type syntheses
-- -- TODO: I think there is a reliance on type inference for arguments of term abstractions,
-- --       so perhaps it'd be good to explicitly add those as terms e.g.
-- --       Term_AbsTy (Name Type) Kind Term
-- --       Term_AppTy Term Type
-- -- i.e. explicit polymorphism

{-
checkType :: Context -> Term -> Type -> M ()
checkType ctx a _t = case _t of
  -- SelfGen
  Type_Iota x t -> do
    -- ctx |- a :: [x => a] t
    checkType ctx a (fromExpr $ substitute x (Term a) (Type t))
    -- ctx |- ι x . t :: *
    checkKind ctx (Type_Iota x t) Kind_Unit
  -- Poly
  Type_AllTy x k t -> do
    -- ctx, x :: k |- a : t
    checkType (Context_Kinding ctx x k) a t
    -- ctx |- k WF
    checkWellFormedKind ctx k
    return ()
  t ->
    -- SelfInst
    synthesizeType ctx a >>= \case
      -- ctx |- a :: ι x . s
      Type_Iota x s ->
        unify (Type s) (substitute x (Term a) (Type t))
      -- Indx
      _ -> undefined
      -- Inst
      _ -> undefined
      _ -> undefined
-}

-- try :: M a -> M (Either String a)
-- try ma = catchError (Right <$> ma) (return . Left)

-- -- match on pairs of patterns and continuations
-- -- if a pattern fails, then continuation is not run
-- -- if a pattern succeeds, then continuation is run (and may except)
-- -- if all patterns fail, then inexhaustive match
-- match :: [(M a, a -> M b)] -> M b
-- match [] = throwError "inexhaustive match"
-- match ((p, k) : clauses) =
--   try p >>= \case
--     Left _ -> match clauses
--     Right a -> k a

-- synthesizeType :: Context -> Term -> M Type
-- synthesizeType ctx _a = case _a of
--   -- Var
--   Term_Ref x ->
--     synthesizeType_NameTm ctx x
--   -- Func
--   -- λ x : s . a
--   Term_AbsTm x s a -> do
--     -- ctx |- s :: *
--     checkKind ctx s Kind_Unit
--     -- ctx, x :: s |- a :: t
--     t <- synthesizeType (Context_Typing ctx x s) a
--     -- ctx |- λ x : s . a :: Π x : s . t
--     return $ Type_PiTm x s t
--   -- App
--   -- a b
--   Term_AppTm a b -> do
--     -- ctx |- a :: Π x : s . t
--     (x, s, t) <-
--       synthesizeType ctx a >>= \case
--         Type_PiTm x s t -> return (x, s, t)
--         t -> throwError $ printf "invalid term application applicant: %s :: %s" (show a) (show t)
--     -- ctx |- b :: s
--     checkType ctx b s
--     -- ctx |- a b :: [x => b] t
--     return . fromExpr $ substitute x (Term b) (Type t)
--   -- λ x : k . a
--   Term_AbsTy x k a -> do
--     -- ctx |- k WF
--     checkWellFormedKind ctx k
--     -- ctx, x :: k |- a :: t
--     t <- synthesizeType (Context_Kinding ctx x k) a
--   -- ctx |- λ x : k . a :: forall
--   -- a t
--   Term_AppTy a t -> do
--     _
-- -}

-- {-
-- ## Names
-- -}

-- synthesizeType_NameTm :: Context -> Name Term -> M Type
-- synthesizeType_NameTm Context_Empty x =
--   throwError $ printf "could not synthesize the type of term name: `%s`" (show x)
-- synthesizeType_NameTm (Context_Typing ctx y t) x =
--   if x == y
--     then return t
--     else synthesizeType_NameTm ctx x
-- synthesizeType_NameTm (Context_Kinding ctx _ _) x =
--   synthesizeType_NameTm ctx x
-- synthesizeType_NameTm (Context_Closure ctx clo) x =
--   undefined

-- synthesizeKind_NameTy :: Context -> Name Type -> M Kind
-- synthesizeKind_NameTy Context_Empty x =
--   throwError $ printf "could not synthesize the kind of type name: `%s`" (show x)
-- synthesizeKind_NameTy (Context_Typing ctx _ _) x =
--   synthesizeKind_NameTy ctx x
-- synthesizeKind_NameTy (Context_Kinding ctx y k) x =
--   if x == y
--     then return k
--     else synthesizeKind_NameTy ctx x
-- synthesizeKind_NameTy (Context_Closure ctx clo) x =
--   undefined -- TODO

-- {-
-- ## Unification
-- -}

-- -- congruence closure of beta-reduction
-- unify :: Expr a -> Expr a -> M ()
-- unify e1 e2 =
--   runExceptT (go e1 e2) >>= \case
--     Left (s1, s2) -> throwError $ printf "cannot unify subexpression `%s` with `%s`, in order to unify expression `%s` with `%s`" (show s1) (show s2) (show e1) (show e2)
--     Right () -> return ()
--   where
--     go :: Expr a -> Expr a -> ExceptT (String, String) M ()
--     -- term
--     go (Term _a1) (Term _a2) = case (_a1, _a2) of
--       (Term_Ref x1, Term_Ref x2) ->
--         if x1 /= x2
--           then throwError (show _a1, show _a2)
--           else return ()
--       (Term_AbsTm x1 t1 a1, Term_AbsTm x2 t2 a2) -> do
--         go (Type t1) $ substitute x2 (Term $ Term_Ref x1) (Type t1)
--         go (Term a1) $ substitute x2 (Term $ Term_Ref x1) (Term a1)
--       (Term_AppTm a1 b1, Term_AppTm a2 b2) -> do
--         go (Term a1) (Term a2)
--         go (Term b1) (Term b2)
--       _ -> throwError $ (show _a1, show _a2)
--     -- type
--     go (Type _t1) (Type _t2) = case (_t1, _t2) of
--       (Type_Ref x1, Type_Ref x2) ->
--         if x1 /= x2
--           then throwError $ (show _t1, show _t2)
--           else return ()
--       (Type_AllTy x1 k1 t1, Type_AllTy x2 k2 t2) -> do
--         go (Kind k1) $ substitute x2 (Type $ Type_Ref x1) (Kind k2)
--         go (Type t1) $ substitute x2 (Type $ Type_Ref x1) (Type t2)
--       (Type_PiTm x1 s1 t1, Type_PiTm x2 s2 t2) -> do
--         go (Type s1) $ substitute x2 (Term $ Term_Ref x1) (Type s2)
--         go (Type t1) $ substitute x2 (Term $ Term_Ref x1) (Type t2)
--       (Type_AllTm x1 s1 t1, Type_AllTm x2 s2 t2) -> do
--         go (Type s1) $ substitute x2 (Term $ Term_Ref x1) (Type s2)
--         go (Type t1) $ substitute x2 (Term $ Term_Ref x1) (Type t2)
--       (Type_Iota x1 t1, Type_Iota x2 t2) ->
--         go (Type t1) $ substitute x2 (Term $ Term_Ref x1) (Type t2)
--       (Type_AppTm s1 a1, Type_AppTm s2 a2) -> do
--         go (Type s1) (Type s2)
--         go (Term a1) (Term a2)
--       (Type_AbsTy x1 k1 t1, Type_AbsTy x2 k2 t2) -> do
--         go (Kind k1) $ substitute x2 (Type $ Type_Ref x1) (Kind k2)
--         go (Type t1) $ substitute x2 (Type $ Type_Ref x1) (Type t2)
--       (Type_AbsTm x1 s1 t1, Type_AbsTm x2 s2 t2) -> do
--         go (Type s1) $ substitute x2 (Term $ Term_Ref x1) (Type s2)
--         go (Type t1) $ substitute x2 (Term $ Term_Ref x1) (Type t2)
--       (Type_AppTy s1 t1, Type_AppTy s2 t2) -> do
--         go (Type s1) (Type s2)
--         go (Type t1) (Type t2)
--       _ ->
--         throwError (show _t1, show _t2)
--     -- kind
--     go (Kind _k1) (Kind _k2) = case (_k1, _k2) of
--       (Kind_Unit, Kind_Unit) ->
--         return ()
--       (Kind_AbsTm x1 t1 k1, Kind_AbsTm x2 t2 k2) -> do
--         go (Type t1) $ substitute x2 (Term $ Term_Ref x1) (Type t2)
--         go (Kind k1) $ substitute x2 (Term $ Term_Ref x1) (Kind k2)
--       (Kind_AbsTy x1 k1 l1, Kind_AbsTy x2 k2 l2) -> do
--         go (Kind k1) $ substitute x2 (Type $ Type_Ref x1) (Kind k2)
--         go (Kind l1) $ substitute x2 (Type $ Type_Ref x1) (Kind l2)
--       _ ->
--         throwError $ (show _k1, show _k2)

-- {-
-- ## Reduction
-- -}

-- evaluate :: Expr a -> M (Expr a)
-- evaluate e =
--   reduce e >>= \case
--     Just e' -> evaluate e'
--     Nothing -> return e

-- reduce :: Expr a -> M (Maybe (Expr a))
-- reduce = undefined

-- {-
-- ## Substitution
-- -}

-- -- [x => a] b
-- substitute :: Name a -> Expr a -> Expr b -> Expr b
-- substitute = undefined -- TODO
