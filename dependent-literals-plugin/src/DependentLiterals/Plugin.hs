-- Copyright 2020-2021 Google LLC
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--      http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module DependentLiterals.Plugin where

import Data.Foldable (for_)
import Data.Maybe (fromMaybe, isJust)

import qualified Data.Generics as SYB

import BasicTypes (IntegralLit(IL), SourceText(NoSourceText))
import GhcPlugins
         ( Hsc, HsParsedModule(..)
         , Plugin(parsedResultAction, pluginRecompile), defaultPlugin
         , PluginRecompile(NoForceRecompile)
         , CommandLineOption
         , DynFlags, Located, GenLocated(L), noSrcSpan
         , getDynFlags, liftIO
         , gopt_set, GeneralFlag(Opt_SuppressModulePrefixes)
         , SrcSpan
         )
import HsExpr (HsExpr(HsAppType, HsOverLit, HsApp, NegApp))
import HsExtension (NoExt(..))
import HsLit (HsOverLit(..), OverLitVal(HsIntegral))
import HsPat (LPat, Pat(ConPatIn, NPat, ViewPat))
import HsSyn
         ( GhcPs, HsModule(..), LHsExpr, HsWildCardBndrs(HsWC)
         , HsTyLit(HsNumTy)
         , ImportDecl(..), IEWrappedName(..), IE(..)
         )
import HsTypes
         ( HsType(HsAppTy, HsParTy, HsTyLit, HsTyVar)
         , LHsType, HsConDetails(PrefixCon)
         )
import HsUtils (nlHsVar, nlHsApp)
import Module (ModuleName, mkModuleName)
import OccName (OccName, mkTcOcc, mkVarOcc, mkDataOcc)
import Outputable ((<+>), Outputable, nest, pprPrec, sep, showSDoc, text)
import RdrName (RdrName, mkRdrQual, mkRdrUnqual)

#if MIN_VERSION_ghc(8,8,0)
import BasicTypes (PromotionFlag(..))
#else
import GhcPlugins (noLoc)
import HsTypes (Promoted(..))
type PromotionFlag = Promoted
pattern IsPromoted :: PromotionFlag
pattern IsPromoted = Promoted
#endif

data Config = Config
  { _cDoLiterals :: Bool
  , _cDoPatterns :: Bool
  , _cTraceThings :: Bool
  }

defaultConfig :: Config
defaultConfig = Config True True False

interpretOpts :: [CommandLineOption] -> Config
interpretOpts opts0 = go opts0 defaultConfig
 where
  go [] c = c
  go ("nolits":opts) c = go opts c { _cDoLiterals = False }
  go ("nopats":opts) c = go opts c { _cDoPatterns = False }
  go ("trace":opts) c = go opts c { _cTraceThings = True }
  go (opt:_) _ = error $
    "Illegal option " ++ show opt ++
    ".\nAll options: " ++ show opts0

plugin :: Plugin
plugin = defaultPlugin
  { parsedResultAction = \opts _ -> parsedResultPlugin (interpretOpts opts)
  , pluginRecompile = \_ -> return NoForceRecompile
  }

parsedResultPlugin :: Config -> HsParsedModule -> Hsc HsParsedModule
parsedResultPlugin cfg m = do
  df <- getDynFlags
  hpm_module' <- transformParsed cfg df (hpm_module m)
  return $ m { hpm_module = hpm_module' }

when_ :: Applicative f => Bool -> (a -> f a) -> a -> f a
when_ True f = f
when_ False _ = pure

pattern LPat :: Pat p -> LPat p
#if MIN_VERSION_ghc(8,8,0)
pattern LPat pat = pat
#else
pattern LPat pat <- L _ pat
#endif

nlPat :: Pat p -> LPat p
nlPat = id
#if !MIN_VERSION_ghc(8,8,0)
  . noLoc
#endif

transformParsed
  :: Config
  -> DynFlags
  -> Located (HsModule GhcPs)
  -> Hsc (Located (HsModule GhcPs))
transformParsed Config{..} df' (L modLoc HsModule{..}) = do
  decls <-
    pure hsmodDecls
      >>= when_ _cDoLiterals
            ( SYB.everywhereM (SYB.mkM (wrapDebug "expression" transformExp))
            . SYB.everywhere (SYB.mkT foldNegation)
            )
      >>= when_ _cDoPatterns
            (SYB.everywhereM (SYB.mkM (wrapDebug "pattern" transformPat)))

  return $ L modLoc $ HsModule
    { hsmodDecls = decls
    , hsmodImports =
        mkModImport litMod Nothing True Nothing :
        unqualLitModImport :
        qualIntModImport :
        hsmodImports
    , ..
    }
 where
  df = gopt_set df' Opt_SuppressModulePrefixes

  nl :: a -> Located a
  nl = L noSrcSpan

  litMod, intMod :: ModuleName
  litMod = mkModuleName "DependentLiterals.Int"
  intMod = mkModuleName "Kinds.Integer"

  -- import qualified DependentLiterals.Int
  mkModImport nm as q imports = nl $ ImportDecl
    NoExt
    NoSourceText
    (nl nm)
    Nothing -- no package qualifier
    False -- not SOURCE
    False -- not marked safe
    q -- qualified
    True -- implicit
    as -- "as" rename
    ((False,) . nl . map nl <$> imports) -- no "hiding"

  -- Import a few things unqualified implicitly.  This way, when they appear in
  -- error messages, they won't have bulky module names attached.  All of these
  -- have -XMagicHash names so that they can't conflict with the subset of the
  -- namespace used by reasonable Haskell programmers, and most people can't
  -- ever tell that they're imported.
  -- TODO can we move this plugin post-renamer and do this by generating names
  -- that claim to have been originally unqualified?
  importVar = IEVar NoExt . nl . IEName .nl
  importAll = IEThingAll NoExt . nl . IEName . nl
  importTyOp = IEThingAbs NoExt . nl . IEType . nl
  unqualLitModImport = mkModImport litMod Nothing False $ Just
    [ importVar litHashName
    , importTyOp minusHashName
    ]
  qualIntModImport = mkModImport intMod Nothing True $ Just
    [ importAll integerName
    ]

  qual :: OccName -> RdrName
  qual = mkRdrQual litMod

  integerName   = mkRdrUnqual (mkTcOcc "Integer")
  minusHashName = mkRdrUnqual (mkTcOcc "-#")
  negName       = mkRdrQual intMod (mkDataOcc "Neg")
  posName       = mkRdrQual intMod (mkDataOcc "Pos")
  cjustConName  = qual (mkDataOcc "CJust")
  litHashName   = mkRdrUnqual (mkVarOcc "lit#")
  matchHashName = qual (mkVarOcc "match#")

  infixl 4 `mkHsAppType`
  mkHsAppType :: LHsExpr GhcPs -> LHsType GhcPs -> HsExpr GhcPs
  mkHsAppType expr ty = HsAppType
#if MIN_VERSION_ghc(8,8,0)
    NoExt
    expr
    (HsWC NoExt ty)
#else
    (HsWC NoExt ty)
    expr
#endif

  infixl 4 `nlHsAppType`
  nlHsAppType :: LHsExpr GhcPs -> LHsType GhcPs -> LHsExpr GhcPs
  nlHsAppType expr ty = L noSrcSpan $ mkHsAppType expr ty

  infixl 4 `nlHsApp_`
  nlHsApp_ = nlHsApp

  litToTyLit :: IntegralLit -> LHsType GhcPs
  litToTyLit (IL txt neg val) = nl $ HsParTy NoExt $ nl $ HsAppTy NoExt
    (nl $ HsTyVar NoExt IsPromoted $ nl (if neg then negName else posName))
    (nl $ HsTyLit NoExt (HsNumTy txt (abs val)))

  debug :: String -> Hsc ()
  debug s
    | _cTraceThings = liftIO (putStrLn s)
    | otherwise = return ()

  wrapDebug :: Outputable a => String -> (a -> Maybe a) -> a -> Hsc a
  wrapDebug thing f x = do
    let r = f x
    for_ r (\x' ->
      debug $ showSDoc df $ sep
        [ text "Rewrote" <+> text thing <+> pprPrec 11 x <+> text "to"
        , nest 2 $ pprPrec 11 x'
        ])
    return $ fromMaybe x r

  extractLit :: HsExpr GhcPs -> Maybe (IntegralLit, HsExpr GhcPs)
  extractLit (HsOverLit _ (OverLit _ (HsIntegral il) w)) = Just (il, w)
  extractLit _ = Nothing

  fuseNegation :: Bool -> IntegralLit -> IntegralLit
  fuseNegation negated (IL _txt neg val) =
    let -- You can write patterns/exprs that are the negation of a neg literal.
        -- We'll just sweep those under the rug by making them into a positive
        -- literal.  If there's more than one negation, too bad.  Those will
        -- try to call into a Num instance.
        neg' = neg /= negated

        -- If the thing described in the previous comment happened, we have
        -- e.g. "-4" as the source text.  Just drop the source text always.
        txt' = NoSourceText

        -- Set the sign of the resulting literal according to 'neg''.
        val' = (if neg' then negate else id) (abs val)

        -- Refabricated literal.
    in  IL txt' neg' val'

  buildReprLit :: SrcSpan -> IntegralLit -> HsExpr GhcPs -> LHsExpr GhcPs
  buildReprLit l il witness =
    L l $ HsOverLit NoExt $ OverLit NoExt (HsIntegral il) witness

  rewriteLit :: SrcSpan -> Bool -> IntegralLit -> HsExpr GhcPs -> LHsExpr GhcPs
  rewriteLit l negated il witness =
    let il' = fuseNegation negated il
        wrapper = nlHsVar litHashName `nlHsAppType` litToTyLit il'
        lit = buildReprLit l il' witness
    in  L l $ HsApp NoExt (nlHsApp wrapper lit) lit

  foldNegation :: LHsExpr GhcPs -> LHsExpr GhcPs
  foldNegation (L l (NegApp _ (L _ (extractLit -> Just (il, witness))) _)) =
    buildReprLit l (fuseNegation True il) witness
  foldNegation e = e

  transformExp :: LHsExpr GhcPs -> Maybe (LHsExpr GhcPs)
  transformExp (L l (extractLit -> Just (lit, witness))) =
    Just $ rewriteLit l False lit witness
  transformExp _ = Nothing

  transformPat :: LPat GhcPs -> Maybe (LPat GhcPs)
  transformPat (LPat (NPat _ (L l (OverLit _ (HsIntegral il) witness)) negation _)) =
    let il' = fuseNegation (isJust negation) il

        -- Wrapper application of match# to the LitRepr.
        wrappedLit =
          nlHsVar matchHashName
            `nlHsAppType` litToTyLit il'
            `nlHsApp_` buildReprLit l il' witness
            `nlHsApp_` buildReprLit l il' witness

    in  Just $ nlPat $ ViewPat NoExt
            wrappedLit
            (nlPat $ ConPatIn (nl cjustConName) (PrefixCon []))
  transformPat _ = Nothing
