{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP #-}

module Apecs.Linear.THTuples where

import qualified Prelude
import qualified Data.Vector.Unboxed as U
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax
import qualified Control.Functor.Linear as Linear
import Prelude.Base

{--
instance (Component a, Component b) => Component (a, b) where
  type Storage (a,b) = (Storage a, Storage b)

instance (Has w a, Has w b) => Has w (a,b) where
  getStore = Linear.do
    Ur a <- getStore
    Ur b <- getStore
    pure (Ur (a, b))

type instance Elem (a,b) = (Elem a, Elem b)

instance (ExplGet a, ExplGet b) => ExplGet (a, b) where
  explExists (sa, sb) ety = Linear.do
    Ur ea <- explExists sa ety
    Ur eb <- explExists sb ety
    pure (Ur (ea && eb))
  explGet (sa, sb) ety = Linear.do
    Ur a <- explGet sa ety
    Ur b <- explGet sb ety
    pure (Ur (a,b))

instance (ExplSet a, ExplSet b) => ExplSet (a, b) where
  explSet (sa,sb) ety (a,b) = explSet sa ety a >> explSet sb ety b

instance (ExplDestroy a, ExplDestroy b) => ExplDestroy (a, b) where
  explDestroy (sa, sb) ety = explDestroy sa ety >> explDestroy sb ety

instance (ExplMembers m a, ExplGet m b) => ExplMembers m (a, b) where
  explMembers (sa, sb) = Linear.do
    Ur xs <- explMembers sa
    Ur.runUrT $ U.filterM (\x -> Ur.UrT $ explExists sb x) xs

instance (ExplMembers m a, ExplGet m b, ExplGet m c) => ExplMembers m (a, b, c) where
  explMembers (sa, sb, sc) = Linear.do
    Ur sas <- explMembers sa
    Ur.runUrT $ U.filterM (\x -> Ur.UrT $ explExists sb x) sas Prelude.Base.>>= U.filterM (\x -> Ur.UrT $ explExists sb x)
--}

-- | Generate tuple instances for the following tuple sizes.
makeInstances :: [Int] -> Q [Dec]
makeInstances is = concat <$> traverse tupleInstances is

tupleInstances :: Int -> Q [Dec]
tupleInstances n = do
  let vars = [ VarT . mkName $ "t_" ++ show i | i <- [0..n-1]]
      m = VarT $ mkName "m"

      -- [''a,''b] -> ''(a,b)
      tupleUpT :: [Type] -> Type
      tupleUpT = foldl AppT (TupleT n)
      -- ''(t_0, t_1, .. )
      varTuple :: Type
      varTuple = tupleUpT vars

      tupleNExp = TupE [Just (VarE (mkName $ "x" ++ show i)) | i <- [1..n]]

      urN = mkName "Ur"
      pureN = mkName "pure"

      pureUrN = (VarE pureN) `AppE` (ConE urN `AppE` tupleNExp)

      xEs = [VarE (mkName $ "x" ++ show i) | i <- [1..n]]

      tupleName :: Name
      tupleName = tupleDataName n
      tuplE :: Exp
      tuplE = ConE tupleName

      -- Component
      compN = mkName "Component"
      compT var = ConT compN `AppT` var
      strgN = mkName "Storage"
      strgT var = ConT strgN `AppT` var
      compI = InstanceD Nothing (fmap compT vars) (compT varTuple) [
#if MIN_VERSION_template_haskell(2,15,0)
          TySynInstD $ TySynEqn Nothing (strgT varTuple) (tupleUpT . fmap strgT $ vars)
#else
          TySynInstD strgN $ TySynEqn [varTuple] (tupleUpT . fmap strgT $ vars)
#endif
        ]

      dupableC = ConT (mkName "Dupable") `AppT` VarT (mkName "w")

      -- Has
      hasN = mkName "Has"
      hasT var = ConT hasN `AppT` VarT (mkName "w") `AppT` m `AppT` var
      getStoreN = mkName "getStore"
      getStoreE = VarE getStoreN
      apN = mkName "<*>"
      apE = VarE apN
      hasI = InstanceD Nothing (dupableC : (hasT <$> vars)) (hasT varTuple)
        [ FunD getStoreN
          -- Assumes Control.Functor.Linear as Linear is imported
          [Clause [] (NormalB$ DoE (Just (ModName "Linear")) ([ BindS (ConP urN [] [VarP (mkName $ "x" ++ show i)]) getStoreE | i <- [1..n] ] ++ [ NoBindS pureUrN ]) --liftAll tuplE (replicate n getStoreE )
                     ) [] ]
        , PragmaD$ InlineP getStoreN Inline FunLike AllPhases
        ]

      liftAll f mas = foldl (\a x -> AppE (AppE apE a) x) (AppE (VarE (mkName "pure")) f) mas
      sequenceAll :: [Exp] -> Exp
      sequenceAll = foldl1 (\a x -> AppE (AppE (VarE$ mkName ">>") a) x)

      -- Elem
      elemN = mkName "Elem"
      elemT var = ConT elemN `AppT` var
#if MIN_VERSION_template_haskell(2,15,0)
      elemI = TySynInstD $ TySynEqn Nothing (elemT varTuple) (tupleUpT $ fmap elemT vars)
#else
      elemI = TySynInstD elemN $ TySynEqn [varTuple] (tupleUpT $ fmap elemT vars)
#endif

      -- s, ety, w arguments
      sNs = [ mkName $ "s_" ++ show i | i <- [0..n-1]]
      sEs = VarE <$> sNs
      etyN = mkName "ety"
      etyE = VarE etyN
      etyPat = VarP etyN
      wNs = [ mkName $ "w_" ++ show i | i <- [0..n-1]]
#if MIN_VERSION_template_haskell(2,18,0)
      sPat = ConP tupleName [] (VarP <$> sNs)
      wPat = ConP tupleName [] (VarP <$> wNs)
#else
      sPat = ConP tupleName (VarP <$> sNs)
      wPat = ConP tupleName (VarP <$> wNs)
#endif
      wEs = VarE <$> wNs

      getN     = mkName "ExplGet"
      setN     = mkName "ExplSet"
      membersN = mkName "ExplMembers"
      destroyN = mkName "ExplDestroy"

      getT     s = ConT getN     `AppT` m `AppT` s
      setT     s = ConT setN     `AppT` m `AppT` s
      membersT s = ConT membersN `AppT` m `AppT` s
      destroyT s = ConT destroyN `AppT` m `AppT` s

      explSetN     = mkName "explSet"
      explDestroyN = mkName "explDestroy"
      explExistsN  = mkName "explExists"
      explMembersN = mkName "explMembers"
      explGetN     = mkName "explGet"

      explSetE     = VarE explSetN
      explDestroyE = VarE explDestroyN
      explExistsE  = VarE explExistsN
      explMembersE = VarE explMembersN
      explGetE     = VarE explGetN

      explSetF sE wE  = AppE explSetE sE `AppE` etyE `AppE` wE
      explDestroyF sE = AppE explDestroyE sE `AppE` etyE
      explExistsF sE  = AppE explExistsE sE
      explMembersF sE = AppE explMembersE sE
      explGetF sE     = AppE explGetE sE `AppE` etyE

      explExistsAnd va vb =
        AppE (AppE (VarE '(>>=)) va)
#if MIN_VERSION_template_haskell(2,18,0)
          (LamCaseE [ Match (ConP 'False [] []) (NormalB$ AppE (VarE 'return) (ConE 'False)) []
                    , Match (ConP 'True [] []) (NormalB vb) []
#else
          (LamCaseE [ Match (ConP 'False []) (NormalB$ AppE (VarE 'return) (ConE 'False)) []
                    , Match (ConP 'True []) (NormalB vb) []
#endif
                    ])

      --                                  vvv Must be unrestricted for instance to be correct! (we're using UrT)
      explMembersFold va vb = AppE (VarE '(>>=)) va `AppE` AppE (VarE 'U.filterM) vb

      getI = InstanceD Nothing (getT <$> vars) (getT varTuple)
        [ FunD explGetN [Clause [sPat, etyPat]
              ( NormalB$
                DoE (Just (ModName "Linear"))
                    ([ BindS (ConP urN [] [VarP (mkName $ "x" ++ show i)]) (explGetF sE) | (sE, i) <- zip sEs [1..] ] ++ [ NoBindS pureUrN ])
              )
              [] ]
        , PragmaD$ InlineP explGetN Inline FunLike AllPhases

        , FunD explExistsN [Clause [sPat, etyPat]
            (NormalB$
                DoE (Just (ModName "Linear"))
                    ([ BindS (ConP urN [] [VarP (mkName $ "x" ++ show i)]) (explExistsF sE `AppE` etyE) | (sE, i) <- zip sEs [1..] ] ++ [ NoBindS $ (VarE pureN) `AppE` (ConE urN `AppE` (foldr (\x y -> UInfixE x (VarE (mkName "&&")) y) (ConE 'True) xEs) ) ])
                -- foldr explExistsAnd (AppE (VarE 'pure) (ConE 'True)) ((`AppE` etyE) . explExistsF <$> sEs)
            ) [] ]
        , PragmaD$ InlineP explExistsN Inline FunLike AllPhases
        ]

      setI = InstanceD Nothing (setT <$> vars) (setT varTuple)
        [ FunD explSetN [Clause [sPat, etyPat, wPat]
            (NormalB$ sequenceAll (zipWith explSetF sEs wEs)) [] ]
        , PragmaD$ InlineP explSetN Inline FunLike AllPhases
        ]

      destroyI = InstanceD Nothing (destroyT <$> vars) (destroyT varTuple)
        [ FunD explDestroyN [Clause [sPat, etyPat]
            (NormalB$ sequenceAll (explDestroyF <$> sEs)) [] ]
        , PragmaD$ InlineP explDestroyN Inline FunLike AllPhases
        ]

      membersI = InstanceD Nothing (membersT (head vars) : (getT <$> tail vars)) (membersT varTuple)
        [ FunD explMembersN [Clause [sPat]
            (NormalB$
              DoE (Just (ModName "Linear"))
                  ([BindS (ConP urN [] [VarP (mkName "xs")]) (explMembersF (head sEs))] ++
                   [NoBindS $
                     ( VarE (mkName "Ur.runUrT") `AppE`
                      ( foldl explMembersFold
                              (VarE 'U.filterM `AppE` (LamE [VarP (mkName "x")] ((ConE $ mkName "Ur.UrT") `AppE` (explExistsF (sEs !! 1) `AppE` (VarE (mkName "x"))))) `AppE` VarE (mkName "xs"))
                              ((\se -> LamE [VarP (mkName "x")] ((ConE $ mkName "Ur.UrT") `AppE` (explExistsF se `AppE` (VarE (mkName "x"))))) <$> drop 2 sEs)
                      )
                     )
                   ]
                  )
            ) [] ]
        , PragmaD$ InlineP explMembersN Inline FunLike AllPhases
        ]
-- instance (ExplMembers a, ExplGet b) => ExplMembers (a, b) where
--   explMembers (sa, sb) = Linear.do
--     Ur sas <- explMembers sa
--     Ur.runUrT U.filterM (\x -> Ur.UrT (explExists sb x)) sas

  return [compI, hasI, elemI, getI, setI, destroyI, membersI]
