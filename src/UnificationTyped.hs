
module UnificationTyped (unifyTy, solve, unifySp, UnifCxt, elab2UnifCxt) where

import qualified Data.Array.FM as AFM
import qualified Data.Ref.F as RF
import IO
import GHC.Exts

import qualified Cxt as ElabCxt
import qualified MetaCxt as MC
import qualified LvlSet as LS
import qualified Map as M
import Common
import CoreTypes
import Evaluation
import Exceptions

type TypeCxt = M.Map Lvl GTy

type TopTypeCxt = M.Map Lvl GTy

data UnifCxt = UnifCxt
  { tcxt :: TypeCxt
  , ttcxt :: TopTypeCxt
  , mcxt :: MetaCxt
  , lvl :: Lvl
  , frz :: MetaVar
  , cs :: ConvState
  , mask :: LS.LvlSet
  , env :: Env
  , names :: Names
  }

elab2UnifCxt :: ElabCxt.Cxt -> UnifCxt
elab2UnifCxt (ElabCxt.Cxt lvl env mask tbl typ topTyp mcxt names frz) = UnifCxt typ topTyp mcxt lvl frz Rigid mask env names

unifCxtNewLocal :: GTy -> UnifCxt -> (UnifCxt, Val)
unifCxtNewLocal t (UnifCxt tcxt ttcxt mcxt lvl frz cs mask env names) =
  let v = VLocalVar lvl SId
  in (UnifCxt (M.insert lvl t tcxt) ttcxt mcxt (lvl + 1) frz cs (LS.insert lvl mask) (EDef env v) names, v)

unifCxtWithConvState :: ConvState -> UnifCxt -> UnifCxt
unifCxtWithConvState cs (UnifCxt tcxt ttcxt mcxt lvl frz _ mask env names) = UnifCxt tcxt ttcxt mcxt lvl frz cs mask env names

--------------------------------------------------------------------------------

-- | Forcing depending on conversion state.
forceCS :: UnifCxt -> Val -> IO Val
forceCS cxt v = case cs cxt of
  Full -> forceAll (mcxt cxt) v
  _    -> force    (mcxt cxt) v
{-# inline forceCS #-}


-- PARTIAL RENAMINGS
--------------------------------------------------------------------------------

data PartialRenaming = PRen {
    occ :: MetaVar          -- ^ Occurring meta to be checked.
  , dom :: Lvl              -- ^ Domain context size (context of output term)
  , cod :: Lvl              -- ^ Codomain context size (context of input value)
  , ren :: AFM.Array Lvl    -- ^ Partial mapping from cod vars to dom vars,
                            --   (-1) denotes an undefined value. Indices above the
                            --   array length are considered to be mapped to themselves.
  }

instance Show PartialRenaming where
  show (PRen occ dom cod ren) = runIO do
    ren <- AFM.unsafeFreeze ren
    pure $! show (occ, dom, cod, ren)

-- | Lift a renaming over a bound variable. The new var is mapped to itself.
lift :: PartialRenaming -> PartialRenaming
lift (PRen m dom cod ren) = PRen m (dom + 1) (cod + 1) ren
{-# inline lift #-}


-- SOLUTION QUOTATION
--------------------------------------------------------------------------------

approxOccursInSolution :: MetaCxt -> MetaVar -> MetaVar -> MetaVar -> IO UBool
approxOccursInSolution ms frz occ x
  | x < frz   = pure UTrue
  | otherwise = MC.read ms x >>= \case
      Unsolved _ _ | occ == x  -> pure UFalse
                 | otherwise -> pure UTrue
      Solved cache _ t _ _ -> do
        cached <- RF.read cache
        if cached == occ then
          pure UTrue
        else do
          res <- approxOccurs ms frz occ t
          when (res == UTrue) (RF.write cache occ)
          pure res

approxOccurs :: MetaCxt -> MetaVar -> MetaVar -> Tm -> IO UBool
approxOccurs ms frz occ t = let
  go = approxOccurs ms frz occ; {-# inline go #-}
  in case t of
    LocalVar x     -> pure UTrue
    TopVar x _     -> pure UTrue
    Let x a t u    -> (\x y z -> x &&# y &&# z) <$> go a <*> go t <*> go u
    App t u i      -> (&&#) <$> go t <*> go u
    Lam _ t        -> go t
    InsertedMeta x -> approxOccursInSolution ms frz occ x
    Meta x         -> approxOccursInSolution ms frz occ x
    Pi _ a b       -> (&&#) <$> go a <*> go b
    Irrelevant     -> pure UTrue
    U              -> pure UTrue

rigidQuoteSp :: MetaCxt -> MetaVar -> PartialRenaming -> Tm -> Spine -> IO Tm
rigidQuoteSp ms frz pren hd = \case
  SId         -> pure hd
  SApp sp t i -> App <$> rigidQuoteSp ms frz pren hd sp
                     <*> rigidQuote ms frz pren t
                     <*> pure i

rigidQuote :: MetaCxt -> MetaVar -> PartialRenaming -> Val -> IO Tm
rigidQuote ms frz pren t = let
  go       = rigidQuote ms frz pren; {-# inline go #-}
  goSp     = rigidQuoteSp ms frz pren; {-# inline goSp #-}
  goSpFlex = flexQuoteSp ms frz pren; {-# inline goSpFlex #-}
  goBind t = rigidQuote ms frz (lift pren) (appCl' ms t (VLocalVar (cod pren) SId))
  {-# inline goBind #-}

  in force ms t >>= \case
    VLocalVar x sp
      | x < coerce (AFM.size (ren pren)) ->
        (AFM.read (ren pren) (coerce x)) >>= \case
          (-1) -> throw $ UnifyEx Conversion -- scope check
          y    -> goSp (LocalVar (lvlToIx (dom pren) y)) sp
      | otherwise ->
        -- TODO: simplify arith expr here (LocalVar (cod pren - x - 1))
        goSp (LocalVar (lvlToIx (dom pren) (x - (cod pren - dom pren)))) sp

    VFlex x sp
      | occ pren == x -> throw $ UnifyEx Conversion -- occurs check
      | otherwise     -> goSp (Meta x) sp

    topt@(VUnfold h sp t) -> do
      (t, tValid) <- case h of    -- WARNING: Core was fine here, but should be checked on ghc change
        UHTopVar x v -> do
          goSpFlex (TopVar x (coerce v) // UTrue) sp
        UHSolved x -> do
          xValid <- approxOccursInSolution ms frz (occ pren) x
          goSpFlex (Meta x // xValid) sp

      when (tValid == UFalse) $
        fullCheckRhs ms frz pren topt

      pure t

    VLam xi t   -> Lam xi <$> goBind t
    VPi xi a b  -> Pi xi <$> go a <*> goBind b
    VU          -> pure U
    VIrrelevant -> pure Irrelevant

flexQuoteSp :: MetaCxt -> MetaVar -> PartialRenaming -> (Tm, UBool) -> Spine -> IO (Tm, UBool)
flexQuoteSp ms frz pren hd@(t, !tValid) = \case
  SId         -> pure hd
  SApp sp t i -> do
    (sp, spValid) <- flexQuoteSp ms frz pren hd sp
    (t, tValid)   <- flexQuote   ms frz pren t
    pure $! (App sp t i // spValid &&# tValid)

flexQuote :: MetaCxt -> MetaVar -> PartialRenaming -> Val -> IO (Tm, UBool)
flexQuote ms frz pren t = let
  go       = flexQuote ms frz pren; {-# inline go #-}
  goSp     = flexQuoteSp ms frz pren; {-# inline goSp #-}
  goBind t = flexQuote ms frz (lift pren) (appCl' ms t (VLocalVar (cod pren) SId))
  {-# inline goBind #-}

  in force ms t >>= \case
    VLocalVar x sp
      | x < coerce (AFM.size (ren pren)) ->
        (AFM.read (ren pren) (coerce x)) >>= \case
          (-1) -> pure (Irrelevant, UFalse)
          y    -> goSp (LocalVar (lvlToIx (dom pren) y) // UTrue) sp
      | otherwise ->
        -- TODO: simplify arith expr here (LocalVar (cod pren - x - 1))
        goSp (LocalVar (lvlToIx (dom pren) (x - (cod pren - dom pren))) // UTrue) sp

    VFlex x sp
      | occ pren == x -> pure (Irrelevant, UFalse)
      | otherwise     -> goSp (Meta x // UTrue) sp

    topt@(VUnfold h sp t) -> do
      (t, tf) <- case h of    -- WARNING: Core was fine here, but should be checked on ghc change
        UHTopVar x v -> do
          goSp (TopVar x (coerce v) // UTrue) sp
        UHSolved x -> do
          xf <- approxOccursInSolution ms frz (occ pren) x
          goSp (Meta x // xf) sp

      when (tf == UFalse) $
        fullCheckRhs ms frz pren topt

      pure $! (t // UTrue)

    VLam xi t -> do
      (!t, !tValid) <- goBind t
      pure $! (Lam xi t // tValid)

    VPi xi a b -> do
      (a, aValid) <- go a
      (b, bValid) <- goBind b
      pure $! (Pi xi a b // aValid &&# bValid)

    VU          -> pure (U // UTrue)
    VIrrelevant -> pure (Irrelevant // UTrue)

fullCheckSp :: MetaCxt -> MetaVar -> PartialRenaming -> Spine -> IO ()
fullCheckSp ms frz pren = \case
  SId         -> pure ()
  SApp sp t i -> fullCheckSp ms frz pren sp >> fullCheckRhs ms frz pren t

fullCheckRhs :: Dbg => MetaCxt -> MetaVar -> PartialRenaming -> Val -> IO ()
fullCheckRhs ms frz pren v = do
  let go       = fullCheckRhs ms frz pren;  {-# inline go #-}
      goSp     = fullCheckSp ms frz pren;   {-# inline goSp #-}
      goBind t = fullCheckRhs ms frz (lift pren)
                    (appCl' ms t (VLocalVar (cod pren) SId))
      {-# inline goBind #-}

  forceAll ms v >>= \case

    VFlex m' sp | occ pren == m' -> throw $ UnifyEx Conversion -- occurs check
                | otherwise      -> goSp sp

    VLocalVar x sp
      | x < coerce (AFM.size (ren pren)) ->
        (AFM.read (ren pren) (coerce x)) >>= \case
          (-1) -> throw $ UnifyEx Conversion -- scope check
          y    -> goSp sp
      | otherwise ->
        goSp sp

    VLam _ t    -> goBind t
    VPi _ a b   -> go a >> goBind b
    VUnfold{}   -> error "unfold in Full conversion state"
    VU          -> pure ()
    VIrrelevant -> pure ()


-- UNIFICATION
--------------------------------------------------------------------------------

-- | Invert a spine, producing a partial renaming. The "trim" argument is the
--   set of vars that we already dropped by eta-contracting the two sides.
invertSp :: UnifCxt -> MetaVar -> Spine -> LS.LvlSet -> IO PartialRenaming
invertSp cxt m sp trim = do
  ren <- AFM.new @Lvl (coerce (lvl cxt))
  AFM.set ren (-1)

  let go :: MetaCxt -> AFM.Array Lvl -> LS.LvlSet -> Spine -> IO Lvl
      go ms ren trim = \case
        SId         -> pure 0
        SApp sp t _ -> do
          dom <- go ms ren trim sp
          forceAll ms t >>= \case
            VLocalVar x SId -> do

              -- non-linear: variable was previously trimmed by eta-contraction
              when (LS.member x trim) (throw $ UnifyEx Conversion)

              y <- AFM.read ren (coerce x)
              case y of
                (-1) -> do
                  AFM.write ren (coerce x) dom
                  pure $! (dom + 1)

                -- non-linear: variable already mapped
                y -> throw $ UnifyEx Conversion
            _ ->
              throw $ UnifyEx Conversion -- non-var in spine

  dom <- go (mcxt cxt) ren trim sp
  pure (PRen m dom (lvl cxt) ren)

lams :: Spine -> Tm -> Tm
lams SId           acc = acc
lams (SApp sp t i) acc = lams sp (Lam (NI NX i) acc)

data SSLS = SSLS Spine Spine LS.LvlSet

-- | Try to eta contract both sides, bind trimmed lhs, rhs, and the set of
--   variables that were trimmed.
etaContract :: Spine -> Val -> (Spine -> Val -> LS.LvlSet -> IO a) -> IO a
etaContract sp rhs cont = let

  go :: Spine -> Spine -> LS.LvlSet -> IO SSLS
  go sp sp' trim = case (sp, sp') of
    (left@(SApp sp (VLocalVar x SId) i), right@(SApp sp' (VLocalVar x' SId) i')) -> do
      when (LS.member x trim) (throw $ UnifyEx Conversion) -- non-linear spine
      if x == x' then go sp sp' (LS.insert x trim)
                 else pure (SSLS left right trim)
    (sp, sp') -> pure (SSLS sp sp' trim)

  in case rhs of
    VFlex x sp'     -> go sp sp' mempty >>= \case
                         SSLS sp sp' trim -> cont sp (VFlex x sp') trim
    VLocalVar x sp' -> go sp sp' mempty >>= \case
                         SSLS sp sp' trim -> cont sp (VLocalVar x sp') trim
    VUnfold h sp' v -> go sp sp' mempty >>= \case
                         SSLS sp sp' trim -> cont sp (VUnfold h sp' v) trim
    _               -> cont sp rhs mempty
{-# inline etaContract #-}

solve :: UnifCxt -> MetaVar -> Spine -> Val -> IO ()
solve cxt x ~sp ~rhs = do
  -- debug ["attempt solve", show (VFlex x sp), show rhs]
  when (x < frz cxt) $ throw $ UnifyEx $ FrozenSolution x

  -- TURN OFF eta-contraction here

  etaContract sp rhs \sp rhs trim -> do

  -- do
  --   let trim = mempty

    pren <- invertSp cxt x sp trim
    rhs <- lams sp <$> rigidQuote (mcxt cxt) (frz cxt) pren rhs
    debug ["renamed", show rhs]
    debug ["solve", show x, show pren, show rhs]
    MC.solve (mcxt cxt) x rhs (eval (mcxt cxt) ENil rhs)

-- | Try to solve a meta, but fully eta-expand sides.
solveLong :: UnifCxt -> MetaVar -> Spine -> Val -> VTy -> IO ()
solveLong cxt x sp rhs ty = do
  rhs' <- forceAll (mcxt cxt) rhs
  case (rhs', ty) of
    ((VLam (NI _ i) t), (VPi _ d c)) ->
      let (cxt', v) = unifCxtNewLocal (gjoin d) cxt
      in solveLong cxt' x (SApp sp v i) (appCl' (mcxt cxt) t v) (appCl (mcxt cxt) c v)
    ((VFlex x' sp'), _)
      | x == x' -> do
        xTy <- metaType cxt x
        unifySp cxt xTy sp sp'
        return ()
      | otherwise -> flexFlex cxt (VFlex x sp) x sp rhs x' sp'
    (_, _) -> solve cxt x sp rhs

flexFlex :: UnifCxt -> Val -> MetaVar -> Spine -> Val -> MetaVar -> Spine -> IO ()
flexFlex cxt t x ~sp t' x' ~sp' =
  solve cxt x sp t' `catch` \_ ->
  solve cxt x' sp' t

calcMetaType :: UnifCxt -> VTy -> IO VTy
calcMetaType cxt codom =
  let goSp :: Lvl -> Lvl -> LS.LvlSet -> (Tm -> Tm) -> IO (Tm -> Tm)
      goSp x l mask ty
        | x == l    = return ty
        | otherwise =
          let ty'
                | LS.member x mask =
                  let (G _ xTy) = M.lookup x (tcxt cxt)
                  in (\c -> Pi (NI NX Expl) (quote (mcxt cxt) x UnfoldNone xTy) (ty c))
                | otherwise        = ty
          in goSp (x + 1) l mask ty'
  in do
    f <- goSp 0 (lvl cxt) (mask cxt) (\c -> c)
    return (eval (mcxt cxt) (env cxt) (f (quote (mcxt cxt) (lvl cxt) UnfoldNone codom)))

-- | Create fresh meta as a value.
freshMeta :: UnifCxt -> VTy -> IO Val
freshMeta cxt ty = do
  let goSp :: Lvl -> Lvl -> LS.LvlSet -> Spine -> IO Spine
      goSp x l mask sp
        | x == l    = return sp
        | otherwise =
          let sp'
                | LS.member x mask = SApp sp (VLocalVar x SId) Expl
                | otherwise        = sp
          in goSp (x + 1) l mask sp'
  sp <- (goSp 0 (lvl cxt) (mask cxt) SId)
  ty' <- calcMetaType cxt ty
  mvar <- MC.fresh (mcxt cxt) (gjoin ty') (mask cxt)
  pure $! VFlex (coerce mvar) sp

-- | Create fresh meta as a term, under an extra binder.
freshMetaUnderBinder :: UnifCxt -> Icit -> VTy -> IO Closure
freshMetaUnderBinder cxt i ty = do
  ty' <- calcMetaType cxt ty
  mvar <- MC.fresh (mcxt cxt) (gjoin ty') (LS.insert (lvl cxt) (mask cxt))
  pure $! Closure (env cxt) (InsertedMeta (coerce mvar))

assertPiType :: UnifCxt -> Icit -> VTy -> IO (VTy, Closure)
assertPiType _ _ (VPi _ d c) = return (d, c)
assertPiType cxt icit t = do
  debug ["assertPiType", show t]
  d <- freshMeta cxt VU
  c <- freshMetaUnderBinder cxt icit VU
  -- TODO: Is it ok that we just set name to empty?
  unifyTy cxt (gjoin t) (gjoin (VPi (NI NX icit) d c))
  return (d, c)

unifySp :: UnifCxt -> GTy -> Spine -> Spine -> IO GTy
unifySp cxt idTy sp sp' = do
  debug ["unifySp", show idTy, show sp, show sp']
  case (sp, sp') of
    (SId,         SId          ) -> pure idTy
    (SApp sp t i, SApp sp' t' _) -> do
      (G _ ftyp) <- unifySp cxt idTy sp sp'
      typ' <- forceCS cxt ftyp
      (d, c) <- assertPiType cxt i typ'
      unifyChk cxt (gjoin t) (gjoin t') d
      return (gjoin (appCl' (mcxt cxt) c t))
    _ -> throw $ UnifyEx Conversion

unifyTy :: UnifCxt -> G -> G -> IO ()
-- Because forall A. A type = A : U
unifyTy cxt a b = unifyChk cxt a b VU

unifyChkClo :: UnifCxt -> GTy -> Closure -> Closure -> Val -> IO ()
unifyChkClo cxt d c c' t = do
  let (cxt', v) = unifCxtNewLocal d cxt
  debug ["unifyChkClo", show v, show t, show c, show c']
  unifyChk cxt' (gjoin $! appCl' (mcxt cxt) c v) (gjoin $! appCl (mcxt cxt) c' v) t

-- withLocal :: Lvl -> GTy -> SymTable -> (Lvl -> Val -> IO a) -> IO a
-- withLocal l ty tbl a = do
--   h <- ST.hash tbl 

unfoldHeadType :: UnifCxt -> UnfoldHead -> IO GTy
unfoldHeadType cxt (UHTopVar x _) = do
  return (M.lookup x (ttcxt cxt))
unfoldHeadType cxt (UHSolved x) = metaType cxt x

metaType :: UnifCxt -> MetaVar -> IO GTy
metaType cxt x = do
  ty <- MC.read (mcxt cxt) x
  case ty of
    Unsolved _ t -> return t
    Solved _ _ _ _ t -> return t

unifyChk :: Dbg => UnifCxt -> G -> G -> Val -> IO ()
unifyChk cxt (G topt ftopt) (G topt' ftopt') ty = let
  err      = throw (UnifyEx Conversion); {-# inline err #-}

  guardCS cs = when (cs == Flex) $ throw $ UnifyEx FlexSolution
  {-# inline guardCS #-}

  in do
    -- turn off speculative conversion here:

    -- t  <- forceAll ms ftopt
    -- t' <- forceAll ms ftopt'
    t  <- forceCS cxt ftopt
    t' <- forceCS cxt ftopt'
    ty' <- forceCS (unifCxtWithConvState Full cxt) ty
    debug ["unifyChk", show t, show t', show ty']
    case (t, t', ty') of
      -- function eta
      (_, _, VPi _ d c) -> do
        let (cxt', xv) = unifCxtNewLocal (gjoin d) cxt
        debug ["Pi eta", show xv, show d]
        unifyChk cxt' (gjoin (doApp cxt t xv)) (gjoin (doApp cxt t' xv)) (appCl' (mcxt cxt) c xv)
      -- (VLam i c, t', ty) -> do
      --   unifyTy ms tcxt ttcxt l frz cs ty _
      (VPi (NI _ i) d c, VPi (NI _ i') d' c', VU) | i == i' -> do
        let gd = gjoin d
        unifyChk cxt gd (gjoin d') VU
        unifyChkClo cxt gd c c' VU
      (VU, VU, VU) -> pure ()
      (VIrrelevant, _, _) -> pure ()
      (_, VIrrelevant, _) -> pure ()
      (VLocalVar x sp, VLocalVar x' sp', _) | x == x' -> do
        debug ["M.lookup", show x]
        unifySp cxt (M.lookup x (tcxt cxt)) sp sp' >> return ()
      (VUnfold h sp t, VUnfold h' sp' t', _) -> do
        hTy <- unfoldHeadType cxt h
        debug ["unfold head type", show hTy]
        case cs cxt of
          Rigid | eqUH h h' -> do
            (unifySp (unifCxtWithConvState Flex cxt) hTy sp sp' >> pure ())
              `catch` \_ -> unifyChk (unifCxtWithConvState Full cxt) (G topt t) (G topt' t') ty
                | otherwise -> unifyChk (unifCxtWithConvState Rigid cxt) (G topt t) (G topt' t') ty
          Flex  | eqUH h h' -> unifySp (unifCxtWithConvState Flex cxt) hTy sp sp' >> return ()
                | otherwise -> err
          _                 -> error "unfold in Full conversion state"
      (VUnfold h sp t, _, _) -> case cs cxt of
        Rigid -> unifyChk cxt (G topt t) (G topt' t') ty
        Flex  -> err
        _     -> error "unfold in Full conversion state"
      (_, VUnfold h' sp' t', _) -> case cs cxt of
        Rigid -> unifyChk cxt (G topt t) (G topt' t') ty
        Flex  -> err
        _     -> error "unfold in Full conversion state"
      (VFlex x sp, VFlex x' sp', _)
        | x == x' -> do
           xTy <- metaType cxt x
           unifySp cxt xTy sp sp'
           return ()
        | otherwise -> guardCS (cs cxt) >> flexFlex cxt topt x sp topt' x' sp'
      (VFlex x sp, t', ty) -> do
        guardCS (cs cxt)
        solve cxt x sp topt' `catch` \_ ->
          solveLong cxt x sp t' ty
      (t, VFlex x' sp', ty) -> do
        guardCS (cs cxt)
        solve cxt x' sp' topt `catch` \_ ->
          solveLong cxt x' sp' t ty
      (t, t', ty) -> throw (UnifyEx Conversion)


doApp :: Dbg => UnifCxt -> Val -> Val -> Val
doApp cxt (VLam _ c) a = appCl (mcxt cxt) c a
doApp _ (VLocalVar x sp) a = VLocalVar x (SApp sp a Expl)
doApp _ (VFlex x sp) a = VFlex x (SApp sp a Expl)
doApp cxt (VUnfold x sp f) a = VUnfold x (SApp sp a Expl) (doApp cxt f a)
doApp _ _ _ = error "applied non function"
