module Language.Itse.Checking where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer
import Language.Itse.Grammar
import Text.Printf (printf)
import Prelude hiding (log, lookup)
import qualified Prelude

{-
## Control Flow
-}

type M = StateT Context (ExceptT Exception (Writer [Log]))

type Exception = String

type Log = String

toIO :: M a -> IO a
toIO m = case runWriter . runExceptT $ evalStateT m Context_Empty of
  (Left expt, logs) -> do
    printf "%s\nlogs: (%i)\n%s\n" expt (length logs) (unlines . map (" - " ++) $ logs)
    fail "Language.Itse.Checking.toIO"
  (Right a, _) ->
    return a

log :: String -> M ()
log msg = tell [msg]

logBlock :: String -> M a -> M a
logBlock msg m = do log ("begin " ++ msg); a <- m; log ("end   " ++ msg); return a

{-
## Contexts
-}

data Context
  = Context_Empty
  | Context_Typing (Name Term) Type Context
  | Context_Kinding (Name Type) Kind Context
  | Context_Closure Closure Context
  deriving (Show)

{-
## Closures
-}

-- laws:
-- - no (mutually) recursive mappings
-- - terms are bound to closed terms
-- - types are bound to types closed in domain(closure)
data Closure = Closure
  { bindingsTm :: [(Name Term, (Term, Type))],
    bindingsTy :: [(Name Type, (Type, Kind))],
    bindingsKd :: [(Name Kind, Kind)]
  }
  deriving (Show)

type family LookupResult a where
  LookupResult Term = (Term, Type)
  LookupResult Type = (Type, Kind)
  LookupResult Kind = Kind

lookupClosure :: Name a -> Closure -> Maybe (LookupResult a)
lookupClosure = \case
  x@(NameTm _) -> \Closure {bindingsTm} -> Prelude.lookup x bindingsTm
  x@(NameTy _) -> \Closure {bindingsTy} -> Prelude.lookup x bindingsTy
  x@(NameKd _) -> \Closure {bindingsKd} -> Prelude.lookup x bindingsKd

lookupContext :: Name a -> Context -> Maybe (LookupResult a)
lookupContext x = \case
  Context_Empty -> Nothing
  Context_Typing _ _ ctx -> lookupContext x ctx
  Context_Kinding _ _ ctx -> lookupContext x ctx
  Context_Closure clo ctx -> lookupClosure x clo <|> lookupContext x ctx

lookup :: Name a -> M (Maybe (LookupResult a))
lookup x = lookupContext x <$> get

{-
## Processing
-}

processPrgm :: Prgm -> M ()
processPrgm (Prgm stmts) = mapM_ processStmt stmts

processStmt :: Stmt -> M ()
processStmt = \case
  Stmt_DefnTm x t a -> do
    declareNameTy x t
    t' <- synthesizeType a
    unify t t'
  Stmt_DefnTy x k t -> do
    declareNameKd x k
    k' <- synthesizeKind t
    unify k k'

declareNameTy :: Name Term -> Type -> M ()
declareNameTy x t = modify $ Context_Typing x t

declareNameKd :: Name Type -> Kind -> M ()
declareNameKd x k = modify $ Context_Kinding x k

bindClosure :: Closure -> M ()
bindClosure clo = modify $ Context_Closure clo

locallyDeclareNameTy :: Name Term -> Type -> M a -> M a
locallyDeclareNameTy x t m = locally do declareNameTy x t; m

locallyDeclareNameKd :: Name Type -> Kind -> M a -> M a
locallyDeclareNameKd x k m = locally do declareNameKd x k; m

locallyBindClosure :: Closure -> M a -> M a
locallyBindClosure clo m = locally do bindClosure clo; m

locally :: M a -> M a
locally m = lift . evalStateT m =<< get

inContext :: Context -> M a -> M a
inContext ctx m = locally do put ctx; m

{-
## Free Names
-}

freeNameTms :: ToExpr a => a -> [Name Term]
freeNameTms _e = case toExpr _e of
  Term _ -> case _e of
    Term_Ref x -> [x]
    Term_AbsTm x t a -> (freeNameTms t ++ freeNameTms a) `withoutName` x
    Term_AppTm a b -> freeNameTms a ++ freeNameTms b
    Term_AbsTy _ k a -> freeNameTms k ++ freeNameTms a
    Term_AppTy a t -> freeNameTms a ++ freeNameTms t
  Type _ -> case _e of
    Type_Ref _ -> []
    Type_AppTm t a -> freeNameTms t ++ freeNameTms a
    Type_AbsTy _ k t -> freeNameTms k ++ freeNameTms t
    Type_AbsTm x s t -> (freeNameTms s ++ freeNameTms t) `withoutName` x
    Type_AppTy s t -> freeNameTms s ++ freeNameTms t
    Type_Iota x t -> freeNameTms t `withoutName` x
  Kind _ -> case _e of
    Kind_Unit -> []
    Kind_AbsTm x t k -> (freeNameTms t ++ freeNameTms k) `withoutName` x
    Kind_AbsTy _ k l -> freeNameTms k ++ freeNameTms l

freeNameTys :: ToExpr a => a -> [Name Type]
freeNameTys _e = case toExpr _e of
  Term _ -> case _e of
    Term_Ref _ -> []
    Term_AbsTm _ t a -> freeNameTys t ++ freeNameTys a
    Term_AppTm a b -> freeNameTys a ++ freeNameTys b
    Term_AbsTy x k a -> (freeNameTys k ++ freeNameTys a) `withoutName` x
    Term_AppTy a t -> freeNameTys a ++ freeNameTys t
  Type _ -> case _e of
    Type_Ref x -> [x]
    Type_Iota _ t -> freeNameTys t
    Type_AppTm t a -> freeNameTys t ++ freeNameTys a
    Type_AbsTy x k t -> (freeNameTys k ++ freeNameTys t) `withoutName` x
    Type_AbsTm _ s t -> freeNameTys s ++ freeNameTys t
    Type_AppTy s t -> freeNameTys s ++ freeNameTys t
  Kind _ -> case _e of
    Kind_Unit -> []
    Kind_AbsTm _ t k -> freeNameTys t ++ freeNameTys k
    Kind_AbsTy x k l -> (freeNameTys k ++ freeNameTys l) `withoutName` x

withoutName :: [Name a] -> Name a -> [Name a]
withoutName xs x = filter (x /=) xs

{-
## Wellformed-ness
-}

wellformedContext :: Context -> M ()
wellformedContext _ctx = (logBlock $ printf "wellFormedContext: %s" (show _ctx))
  case _ctx of
    Context_Empty ->
      return ()
    Context_Typing _ t ctx -> do
      wellformedContext ctx
      locally do put ctx; checkKind t Kind_Unit
    Context_Kinding _ k ctx -> do
      wellformedContext ctx
      locally do put ctx; wellformedKind k
    Context_Closure clo ctx ->
      locally do put ctx; wellformedClosure clo

wellformedClosure :: Closure -> M ()
wellformedClosure clo = (logBlock $ printf "wellformedClosure: %s" (show clo)) do
  {-
    TODO:
    should `locallyBindClosure clo`? Or should this not happen since closures
    cannot have (mutually) recursive definitions...?
  -}
  mapM_ (locallyBindClosure clo . uncurry checkType . snd) $ bindingsTm clo
  mapM_ (locallyBindClosure clo . uncurry checkKind . snd) $ bindingsTy clo
  mapM_ (wellformedKind . snd) $ bindingsKd clo

wellformedKind :: Kind -> M ()
wellformedKind _k = (logBlock $ printf "wellformedKind: %s" (show _k))
  case _k of
    Kind_Unit ->
      return ()
    Kind_AbsTy x k l -> do
      locallyDeclareNameKd x k $ wellformedKind l
      wellformedKind k
    Kind_AbsTm x t k -> do
      locallyDeclareNameTy x t $ wellformedKind k
      checkKind t Kind_Unit

{-
## Kinding
-}

checkKind :: Type -> Kind -> M ()
checkKind t k = (logBlock $ printf "checkKind: %s :: %s" (show t) (show k)) do
  wellformedKind k
  k' <- synthesizeKind t
  unify k k'

synthesizeKind :: Type -> M Kind
synthesizeKind _t = (logBlock $ printf "synthesizeKind: %s" (show _t))
  case _t of
    -- x
    Type_Ref x ->
      -- ctx, x : k |- x : k
      synthesizeKind_NameTy x
    -- s a
    Type_AppTm s a -> do
      -- ctx |- s :: Π x : t . k
      (x, _, k) <-
        synthesizeKind s >>= \case
          Kind_AbsTm x t k -> return (x, t, k)
          k -> throwError $ printf "invalid type-term applicant: `%s :: %s`" (show s) (show k)
      -- ctx |- a :: s
      checkType a s
      -- ctx |- s a :: [x => a] k
      return $ substitute x a k
    -- λ x : k . t
    Type_AbsTy x k t -> do
      -- ctx, x :: k |- t :: l
      l <- locallyDeclareNameKd x k $ synthesizeKind t
      -- ctx |- k WF
      wellformedKind k
      if x `elem` freeNameTys l
        then -- ctx |- forall x : k . t :: Π x : k . l
          return $ Kind_AbsTy x k l
        else -- ctx |- forall _ : k . t :: l
          return l
    -- λ x : s . t
    Type_AbsTm x s t -> do
      -- ctx, x :: s |- t :: k
      k <- locallyDeclareNameTy x s $ synthesizeKind t
      -- ctx |- t :: *
      checkKind t Kind_Unit
      if x `elem` freeNameTms t
        then -- ctx |- λ x : s . t :: Π x : s . k
          return $ Kind_AbsTm x s k
        else -- ctx |- λ _ : s . t :: k
          return k
    -- s t
    Type_AppTy s t -> do
      -- ctx |- s :: Π x : k . l
      (x, k, l) <-
        synthesizeKind s >>= \case
          Kind_AbsTy x k l -> return (x, k, l)
          k -> throwError $ printf "invalid type-type applicant: `%s :: %s`" (show s) (show k)
      -- ctx |- t :: k
      checkKind t k
      -- ctx |- s t :: [x => t] l
      return $ substitute x t l
    -- ι x . t
    Type_Iota x t -> do
      -- ctx, x :: ι x . t |- t :: *
      locallyDeclareNameTy x (Type_Iota x t) $ checkKind t Kind_Unit
      -- ctx |- ι x . t :: *
      return Kind_Unit

{-
## Typing
-}

checkType :: Term -> Type -> M ()
checkType a _t = (logBlock $ printf "checkType: %s :: %s" (show a) (show _t))
  case _t of
    -- SelfGen
    -- ι x . t
    Type_Iota x t -> do
      -- ctx |- a :: [x => a] t
      checkType a (substitute x a t)
      -- ctx |- ι x . t :: *
      checkKind (Type_Iota x t) Kind_Unit
    t ->
      synthesizeType a >>= \case
        -- SelfInst
        -- TODO: potential problem -- what if doesn't want to SelfInst yet?
        -- ctx |- a :: ι x . t'
        Type_Iota x t' ->
          -- ctx |- [x => a] t ~ t'
          unify (substitute x a t) t'
        t' ->
          unify t t'

synthesizeType :: Term -> M Type
synthesizeType _a = (logBlock $ printf "synthesizeType: %s" (show _a))
  case _a of
    -- x
    Term_Ref x ->
      synthesizeType_NameTm x
    -- λ x : s . a
    Term_AbsTm x s a -> do
      -- ctx |- s :: *
      checkKind s Kind_Unit
      -- ctx, x :: a |- a :: t
      t <- locallyDeclareNameTy x s $ synthesizeType a
      -- ctx |- λ x : s . a :: λ x : s . t
      return $ Type_AbsTm x s t
    -- a b
    Term_AppTm a b -> do
      -- ctx |- a :: λ x : s . t
      (x, s, t) <-
        synthesizeType a >>= \case
          Type_AbsTm x s t -> return (x, s, t)
          t -> throwError $ printf "invalid term-term applicant: `%s :: %s`" (show a) (show t)
      -- ctx |- b :: s
      checkType b s
      -- ctx |- a b ::
      return $ substitute x b t
    -- λ x : k . a
    Term_AbsTy x k a -> do
      -- ctx |- k WF
      wellformedKind k
      -- ctx, x :: k |- a :: t
      t <- locallyDeclareNameKd x k $ synthesizeType a
      -- ctx |- λ x : k . a :: λ x : k . t
      return $ Type_AbsTy x k t
    -- a s
    Term_AppTy a s -> do
      -- ctx |- a :: λ x : k . t
      (x, k, t) <-
        synthesizeType a >>= \case
          Type_AbsTy x k t -> return (x, k, t)
          t -> throwError $ printf "invalid term-type applicant: `%s :: %s`" (show a) (show t)
      -- ctx |- s :: k
      checkKind s k
      -- ctx |- a t :: [x => s] t
      return $ substitute x s t

{-
## Names
-}

synthesizeType_NameTm :: Name Term -> M Type
synthesizeType_NameTm x = (logBlock $ printf "synthesizeType_NameTm: %s" (show x)) do
  go =<< get
  where
    go = \case
      Context_Empty ->
        throwError $ printf "undeclared term name: `%s`" (show x)
      Context_Typing y t ctx ->
        if x == y
          then return t
          else go ctx
      Context_Kinding _ _ ctx ->
        go ctx
      Context_Closure clo ctx ->
        case lookupClosure x clo of
          Just (_, t) -> return t
          Nothing -> go ctx

synthesizeKind_NameTy :: Name Type -> M Kind
synthesizeKind_NameTy x = go =<< get
  where
    go = \case
      Context_Empty ->
        throwError $ printf "undeclared type name: `%s`" (show x)
      Context_Typing _ _ ctx ->
        go ctx
      Context_Kinding y k ctx ->
        if x == y
          then return k
          else go ctx
      Context_Closure clo ctx ->
        case lookupClosure x clo of
          Just (_, k) -> return k
          Nothing -> go ctx

{-
## Unification
-}

-- congruence closure of beta-reduction
unify :: ToExpr a => a -> a -> M ()
unify e1 e2 =
  (logBlock $ printf "unify: %s ~ %s" (show . toExpr $ e1) (show . toExpr $ e2))
    (runExceptT (go e1 e2))
    >>= \case
      Left (s1, s2, var) ->
        throwError $
          (printf "cannot unify sub%s\n\n  %s\n\nwith\n\n  %s\n\nin order to unify %s\n\n  %s\n\nwith\n\n  %s\n")
            var
            s1
            s2
            (exprVariant . toExpr $ e1)
            (show . toExpr $ e1)
            (show . toExpr $ e2)
      Right () -> return ()
  where
    go :: ToExpr a => a -> a -> ExceptT (String, String, String) M ()
    -- term
    go _e1 _e2 = case toExpr _e1 of
      Term _ -> case (_e1, _e2) of
        (Term_Ref x1, Term_Ref x2) ->
          if x1 /= x2
            then cannotUnify _e1 _e2
            else return ()
        (Term_AbsTm x1 t1 a1, Term_AbsTm x2 t2 a2) -> do
          go t1 $ substitute x2 (Term_Ref x1) t2
          go a1 $ substitute x2 (Term_Ref x1) a2
        (Term_AppTm a1 b1, Term_AppTm a2 b2) -> do
          go a1 a2
          go b1 b2
        _ -> cannotUnify _e1 _e2
      -- type
      Type _ -> case (_e1, _e2) of
        (Type_Ref x1, Type_Ref x2) ->
          if x1 /= x2
            then cannotUnify _e1 _e2
            else return ()
        (Type_AppTm s1 a1, Type_AppTm s2 a2) -> do
          go s1 s2
          go a1 a2
        (Type_AbsTy x1 k1 t1, Type_AbsTy x2 k2 t2) -> do
          go k1 $ substitute x2 (Type_Ref x1) k2
          go t1 $ substitute x2 (Type_Ref x1) t2
        (Type_AbsTm x1 s1 t1, Type_AbsTm x2 s2 t2) -> do
          go s1 $ substitute x2 (Term_Ref x1) s2
          go t1 $ substitute x2 (Term_Ref x1) t2
        (Type_AppTy s1 t1, Type_AppTy s2 t2) -> do
          go s1 s2
          go t1 t2
        (Type_Iota x1 t1, Type_Iota x2 t2) ->
          go t1 $ substitute x2 (Term_Ref x1) t2
        _ ->
          cannotUnify _e1 _e2
      -- kind
      Kind _ -> case (_e1, _e2) of
        (Kind_Unit, Kind_Unit) ->
          return ()
        (Kind_AbsTm x1 t1 k1, Kind_AbsTm x2 t2 k2) -> do
          go t1 $ substitute x2 (Term_Ref x1) t2
          go k1 $ substitute x2 (Term_Ref x1) k2
        (Kind_AbsTy x1 k1 l1, Kind_AbsTy x2 k2 l2) -> do
          go k1 $ substitute x2 (Type_Ref x1) k2
          go l1 $ substitute x2 (Type_Ref x1) l2
        _ ->
          cannotUnify _e1 _e2

    cannotUnify :: ToExpr a => a -> a -> ExceptT (String, String, String) M ()
    cannotUnify se1 se2 =
      throwError
        ( show . toExpr $ se1,
          show . toExpr $ se2,
          exprVariant . toExpr $ se1
        )

{-
## Reduction
-}

evaluate :: ToExpr a => a -> M a
evaluate e = (logBlock $ printf "evaluate: %s" (show . toExpr $ e)) do
  reduce e >>= \case
    Just e' -> evaluate e'
    Nothing -> return e

reduce :: ToExpr a => a -> M (Maybe a)
reduce e = do
  log $ printf "reduce: %s" (show . toExpr $ e)
  case toExpr e of
    --
    Term _ -> case e of
      --
      Term_Ref x ->
        (fmap . fmap) fst (lookup x)
      --
      Term_AbsTm _ _ _ ->
        return Nothing
      --
      Term_AppTm _a b -> do
        (x, a) <-
          evaluate _a >>= \case
            Term_AbsTm x _ a -> return (x, a)
            a -> throwError $ printf "invalid term-term applicant: `%s`" (show a)
        return . Just $ substitute x b a
      --
      Term_AbsTy _ _ _ ->
        return Nothing
      --
      Term_AppTy _a t -> do
        (x, a) <-
          evaluate _a >>= \case
            Term_AbsTy x _ a -> return (x, a)
            a -> throwError $ printf "invalid term-type applicant: `%s`" (show a)
        return . Just $ substitute x t a
    --
    Type _ -> case e of
      --
      Type_Ref x ->
        (fmap . fmap) fst (lookup x)
      --
      Type_AbsTm _ _ _ ->
        return Nothing
      --
      Type_AppTm _t a -> do
        (x, t) <-
          evaluate _t >>= \case
            Type_AbsTm x _ t -> return (x, t)
            t -> throwError $ printf "invalid type-term applicant: `%s`" (show t)
        return . Just $ substitute x a t
      --
      Type_AbsTy _ _ _ ->
        return Nothing
      --
      Type_AppTy _s t -> do
        (x, s) <-
          evaluate _s >>= \case
            Type_AbsTy x _ s -> return (x, s)
            s -> throwError $ printf "invalid type-type applicant: `%s`" (show s)
        return . Just $ substitute x t s
      --
      Type_Iota _ _ -> do
        return Nothing
    -- substitutes kind
    Kind _ ->
      return Nothing

{-
## Substitution
-}

-- [x => e2] e1
substitute :: (ToExpr a, ToExpr b) => Name a -> a -> b -> b
--
substitute x e _e = case toExpr _e of
  Term _ -> case _e of
    --
    Term_Ref y -> case x of
      NameTm _ ->
        if x == y
          then e
          else Term_Ref y
      _ -> Term_Ref y
    --
    Term_AbsTm y t a -> case x of
      NameTm _ ->
        if x == y
          then Term_AbsTm y t a
          else Term_AbsTm y (substitute x e t) (substitute x e a)
      _ ->
        Term_AbsTm y (substitute x e t) (substitute x e a)
    --
    Term_AbsTy y k a -> case x of
      NameTy _ ->
        if x == y
          then Term_AbsTy y k a
          else Term_AbsTy y (substitute x e k) (substitute x e a)
      _ ->
        Term_AbsTy y (substitute x e k) (substitute x e a)
    --
    Term_AppTm a b ->
      Term_AppTm (substitute x e a) (substitute x e b)
    --
    Term_AppTy a t ->
      Term_AppTy (substitute x e a) (substitute x e t)
  Type _ -> case _e of
    Type_Ref y -> case x of
      NameTy _ ->
        if x == y
          then e
          else Type_Ref y
      _ -> Type_Ref y
    Type_AbsTm y s t -> case x of
      NameTm _ ->
        if x == y
          then Type_AbsTm y s t
          else Type_AbsTm y (substitute x e s) (substitute x e t)
      _ ->
        Type_AbsTm y (substitute x e s) (substitute x e t)
    Type_AbsTy y k t -> case x of
      NameTy _ ->
        if x == y
          then Type_AbsTy y k t
          else Type_AbsTy y (substitute x e k) (substitute x e t)
      _ ->
        Type_AbsTy y (substitute x e k) (substitute x e t)
    Type_AppTm t a ->
      Type_AppTm (substitute x e t) (substitute x e a)
    Type_AppTy s t ->
      Type_AppTy (substitute x e s) (substitute x e t)
    Type_Iota y t -> case x of
      NameTm _ ->
        if x == y
          then Type_Iota y t
          else Type_Iota y (substitute x e t)
      _ -> Type_Iota y (substitute x e t)
  --
  Kind _ -> case _e of
    Kind_Unit ->
      Kind_Unit
    Kind_AbsTm y t k -> case x of
      NameTm _ ->
        if x == y
          then Kind_AbsTm y t k
          else Kind_AbsTm y (substitute x e t) (substitute x e k)
      _ ->
        Kind_AbsTm y (substitute x e t) (substitute x e k)
    Kind_AbsTy y k l -> case x of
      NameTy _ ->
        if x == y
          then Kind_AbsTy y k l
          else Kind_AbsTy y (substitute x e k) (substitute x e l)
      _ ->
        Kind_AbsTy y (substitute x e k) (substitute x e l)
