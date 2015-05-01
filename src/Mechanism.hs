{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns #-}

module Mechanism where

import           Control.Applicative        (Const (..), pure, (<*>))
import           Control.Arrow              (second)
import           Control.Monad              (replicateM)
import qualified Data.Foldable              as F
import           Data.Functor               ((<$>))
import           Data.Monoid                (Monoid (..))
import           Data.Set                   (Set)
import qualified Data.Set                   as S
import qualified Data.Traversable           as T

import           Mechanism.Profile.Sequence (Coll)
import qualified Mechanism.Profile.Sequence as P

-- n agents with N = {1, 2, ..., N}
-- X is set of outcomes
-- type θᵢ
-- Θᵢ the set of private values of agent i
-- Θ = Θ₁ cross ... cross Θₙ
-- common prior P ∈ Δ(Θ)
-- pᵢ : Θᵢ → Δ(Θ_{-i})
-- uᵢ : X cross Θᵢ → R
-- uᵢ : X cross Θ → R
-- common knowledge: X, N, Θ, P, uᵢ


-- Types

newtype Type ty = Type { runType :: ty }
  deriving (Eq, Ord, Num, Show)
newtype Action ac = Action { runAction :: ac }
  deriving (Eq, Ord, Num, Show)
newtype Outcome out = Outcome { runOutcome :: out }
  deriving (Eq, Ord, Show)
newtype Util u = Util { runUtil :: u }
  deriving (Eq, Ord, Num, Fractional, Show)

type Profile con pr = con pr
type Index i = i

type Utility out con ac ty u = Outcome out -> Profile con (Action ac) -> Type ty -> Util u
type Valuation out ac ty u = Utility out (Const ()) ac ty u
type QuasiUtility out ac ty u = Utility (QuasiOutcome out u) (Const ()) ac ty u
type SocialChoice ac out = Actions ac -> Outcome out
type Allocator ac out = SocialChoice ac out
type Transfer u = Util u
type Strategy ty ac = Coll (Type ty, Action ac)
type Match ty ac = Profile Coll (Type ty, Action ac)

type Actions a = Profile Coll (Action a)
type Types a = Profile Coll (Type a)
type Transfers u = Profile Coll (Transfer u)
type TypeSets ty = Profile Coll (Set (Type ty))
type ActionSets ac = Profile Coll (Set (Action ac))
type Valuations out ac ty u = Profile Coll (Valuation out ac ty u)
type Utilities out con ac ty u = Profile Coll (Utility out con ac ty u)
type Utils u = Profile Coll (Util u)

data QuasiOutcome out u =
       QuasiOutcome
         { allocation :: Outcome out
         , transfers  :: Transfers u
         }
  deriving (Eq, Ord, Show)
type DirectMechanism ty out = Mechanism ty ty out
data Mechanism ac ty out =
       Mechanism
         { actionSets   :: ActionSets ac
         , typeSets     :: TypeSets ty
         , socialChoice :: SocialChoice ac out
         }
data Game ac con out ty u =
       Game
         { utilities :: Utilities out con ac ty u
         , mechanism :: Mechanism ac ty out
         }

class Narrow con where
  narrow :: Profile Coll (Action ac) -> Profile con (Action ac)
instance Narrow (Const ()) where
  narrow = const $ Const ()
instance Narrow Coll where
  narrow = id


-- Direct mechanisms

directMechanism :: (Ord ty)
                => TypeSets ty
                -> SocialChoice ty out
                -> DirectMechanism ty out
directMechanism tyss = Mechanism (S.map honest <$> tyss) tyss

honest :: Type ty -> Action ty
honest (Type ty) = Action ty
honest' :: Action ty -> Type ty
honest' (Action ty) = Type ty
isHonest :: (Eq ty) => (Type ty, Action ty) -> Bool
isHonest (Type ty, Action ac) = ty == ac


-- Quasilinear environment

quasiUtility :: (Num u)
             => Util u
             -> Valuation out ac ty u
             -> Index Int
             -> QuasiUtility out ac ty u
quasiUtility initial vl i (Outcome out) (Const ()) ty =
  initial + vl (allocation out) (Const ()) ty + transfers out P.! i

narrowProfile :: Index Int -> Profile Coll a -> Profile Coll a
narrowProfile i = P.ifilter (const . (/=) i)

clarkes :: (Num u)
        => Allocator ty out
        -> Valuations out ac ty u
        -> Types ty
        -> Transfers u
clarkes al vls tys =
  P.imap
    (\i _ -> clarke (al $ honest <$> tys) (al . narrowProfile i $ honest <$> tys) (narrowProfile i vls) (narrowProfile i tys))
    tys

clarke :: (Num u)
       => Outcome out
       -> Outcome out
       -> Valuations out ac ty u
       -> Types ty
       -> Transfer u
clarke withAgent withoutAgent vls tys =
  grove withAgent vls tys . negate $
  totalUtility withoutAgent vls (Const ()) tys

-- `Types` rather than `Actions` because dominant incentive compatible
-- Profiles don't include self, input transfer shouldn't depend on self
grove :: (Num u)
      => Outcome out
      -> Valuations out ac ty u
      -> Types ty
      -> Transfer u
      -> Transfer u
grove out vls tys = (+) (totalUtility out vls (Const ()) tys)

groves :: (Num u)
        => Outcome out
        -> Valuations out ac ty u
        -> Types ty
        -> Transfers u
        -> Transfers u
groves out vls tys =
  P.imap (\i -> grove out (narrowProfile i vls) (narrowProfile i tys))


-- Properties

-- We've modified the standard properties to work with indirect games.
-- Instead of passing in a game and checking for all type profiles,
-- we pass in the matches.
-- By filtering, we choose whether to check the property
-- for all matches, all honest matches, all equilibrium matches, etc.

exPostRational :: (Ord u, Num u, Ord ty, Ord ac, Narrow con)
               => Utilities out con ac ty u
               -> Set (Match ty ac, Outcome out) -> Bool
exPostRational fs =
  F.all (\(P.unzip -> (tys, acs), out) ->
          F.all (>= 0) $ eachAgent out fs (narrow acs) tys)

data BudgetBalance = Strict
                   | Weak
                   | Not
  deriving (Eq, Ord, Show)
instance Monoid BudgetBalance where
  mappend Not _ = Not
  mappend _ Not = Not
  mappend Weak _ = Weak
  mappend _ Weak = Weak
  mappend Strict Strict = Strict
  mempty = Strict

budget :: (Ord u, Num u) => Set (Outcome (QuasiOutcome out u)) -> BudgetBalance
budget os = F.fold . S.map (balanced . F.sum . transfers . runOutcome) $ os
  where
    balanced n
      | n > 0 = Not
      | n < 0 = Weak
      | otherwise = Strict

allocativelyEfficient :: (Num u, Ord u)
                      => Set (Outcome out)
                      -> Valuations out ac ty u
                      -> Set (Match ty ac, Outcome out)
                      -> Bool
allocativelyEfficient outs vls =
  F.all (\(P.unzip -> (tys, _), out) ->
          totalUtility out vls (Const ()) tys ==
          F.maximum (S.map (\out' -> totalUtility out' vls (Const ()) tys) outs))

exPostEfficient :: (Narrow con, Ord ac, Ord ty, Ord u)
                => Set (Outcome out)
                -> Utilities out con ac ty u
                -> Set (Match ty ac, Outcome out)
                -> Bool
exPostEfficient outs fs =
  F.all (\(P.unzip -> (tys, acs), out) ->
          paretoOptimal ((\out' -> eachAgent out' fs (narrow acs) tys) <$> P.fromList (F.toList outs))
          (eachAgent out fs (narrow acs) tys))

-- Textbook definition
paretoOptimal' :: (Ord a) => Coll (Profile Coll a) -> Profile Coll a -> Bool
paretoOptimal' cs c =
  not . F.or $ (\c' -> F.and (P.zipWith (>=) c' c) && F.or (P.zipWith (>) c' c)) <$> cs

-- De Morganed (a little clearer, I think)
paretoOptimal :: (Ord a) => Coll (Profile Coll a) -> Profile Coll a -> Bool
paretoOptimal cs c =
  F.and $ (\c' -> F.or (P.zipWith (<) c' c) || F.and (P.zipWith (<=) c' c)) <$> cs


-- Helper

eachAgent :: Outcome out
          -> Utilities out con ac ty u
          -> Profile con (Action ac)
          -> Types ty
          -> Utils u
eachAgent out fs acs = P.zipWith (\f -> f out acs) fs

totalUtility :: (Num u)
             => Outcome out
             -> Utilities out con ac ty u
             -> Profile con (Action ac)
             -> Types ty
             -> Util u
totalUtility out fs acs tys = F.sum $ eachAgent out fs acs tys

profiles :: (Ord a) => Profile Coll (Set a) -> Set (Profile Coll a)
profiles tyss =
  S.fromList $ P.fromList <$> T.sequence (F.toList $ F.toList <$> tyss)

strategies :: (Ord ac, Ord ty) => Set (Type ty) -> Set (Action ac) -> Set (Strategy ty ac)
strategies tys acs =
  S.fromList $ P.fromList . zip (F.toList tys) <$>
               replicateM (S.size tys) (F.toList acs)

matches :: (Ord ac, Ord ty)
      => TypeSets ty
      -> ActionSets ac
      -> Set (Match ty ac)
matches tyss acss = profiles $ P.zipWith pairs tyss acss
  where
    pairs tys acs = S.fromList . F.toList $ do
      ty <- F.toList tys
      ac <- F.toList acs
      pure (ty, ac)

matches' :: (Ord out, Ord ty, Ord ac)
         => Mechanism ac ty out -> Set (Match ty ac, Outcome out)
matches' (Mechanism acss tyss sc) =
  S.map ((,) <*> sc . snd . P.unzip) $ matches tyss acss


-- Example

data Project = Completed { perCapitaCost :: Util Double }
             | Failed
  deriving (Eq, Ord, Show)

publicProject :: DirectMechanism (Util Double) (QuasiOutcome Project Double)
publicProject =
  directMechanism (P.replicate 2 $ S.fromList [20, 60])
    (\acs ->
       Outcome $ QuasiOutcome (al acs)
       (clarkes al (P.replicate (P.length acs) publicValuation) $ honest' <$> acs))
  where
    cost = Util 50
    al acs =
      Outcome $ if F.sum acs >= Action cost
                  then Completed (cost / fromIntegral (P.length acs))
                  else Failed

publicOutcomes :: Set (Outcome Project)
publicOutcomes = S.fromList $ Outcome <$> [Completed 25, Failed]

publicValuation :: Valuation Project (Util Double) (Util Double) Double
publicValuation out (Const ()) (Type ty) =
  case out of
    Outcome (Completed cs) -> ty - cs
    Outcome Failed         -> 0

publicExPostRational :: Bool
publicExPostRational =
  exPostRational (quasiUtility 0 publicValuation <$> P.fromList [0, 1]) $
    matches' publicProject

publicBudget :: BudgetBalance
publicBudget = budget . S.map (sc . snd . P.unzip) $ matches tyss acss
  where
    (Mechanism acss tyss sc) = publicProject

publicAllocative :: Bool
publicAllocative =
  allocativelyEfficient publicOutcomes (P.replicate 2 publicValuation)
    (S.map (second (allocation . runOutcome)) .
     S.filter (F.all isHonest . fst) $ matches' publicProject)

-- equilibria :: EquilibriumType -> Mechanism ty out -> Strategy ty
-- implementable :: EquilibriumType -> Mechanism ty out ->
--                  SocialChoice ty out -> Bool
-- implements :: EquilibriumType -> Mechanism ty out -> SocialChoice ty out ->
--               Strategy ty -> Bool
-- incentiveCompatible :: EquilibriumType -> DirectMechanism ty out -> Bool
-- dominant :: EquilibriumType
-- nash :: EquilibriumType
-- bayesNash :: EquilibriumType

-- dictator :: Set (Outcome out) -> SocialChoice ty out ->
--             Utility out ty u -> Maybe Integer
-- exAnteRational :: Dist Profile -> Utility out ty u -> Mechanism ty out u -> Bool
-- interimRational :: Dist Profile -> Utility out ty u -> Mechanism ty out u -> Bool

-- type Agent agn = agn
-- type Coalition agn = Set (Agent agn)
-- type Chartyeristic agn b = Coalition agn -> Util b
-- shapleyValue :: Set (Agent agn) -> Chartyeristic agn b -> Util b


-- monotonic :: Set (Outcome out) -> Utility out ty u ->
--              Mechanism (Type ty) out u -> Bool
-- lowerContourSet :: Set (Outcome out) -> Outcome out -> Type ty ->
--                    Utility out ty u -> Set (Outcome out)
-- dagva :: Allocator ty out u -> Valuation out ty u -> Dist Profile ->
--          Transfer ty u
