{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Mechanism where

import qualified Data.Foldable as F
import           Data.Function (on)
import           Data.Functor ((<$>))
import           Data.Functor.Identity (Identity(..))
import           Data.Monoid (Monoid(..))
import           Data.Set (Set)
import qualified Data.Set as S

import           Mechanism.Profile.Vector (Coll)
import qualified Mechanism.Profile.Vector as P

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
  deriving (Eq, Ord, Num)
newtype Outcome out = Outcome { runOutcome :: out }
  deriving (Eq, Ord, Show)
newtype Util u = Util { runUtil :: u }
  deriving (Eq, Ord, Num, Fractional, Show)
type Numeraire n = Util n

type Profile con ty = con ty
type Index i = i

type Utility out con ty i u = out -> Profile con ty -> i -> u
type Valuation out ty u = Utility out Identity ty (Index ()) u
type QuasiUtility out ty u = Utility (Outcome (QuasiOutcome out u)) Identity ty (Index Int) u
type SocialChoice con ty out = Profile con ty -> out
type Allocator con ty out = SocialChoice con ty out
type Transfers u = Coll u
type Strategy ty = Coll (ty, ty)

type Lifter a b out ty u = Utility out a ty b u -> Utility out Coll ty (Index Int) u
quasiLift :: Lifter Identity (Index Int) out ty u 
quasiLift f out pr i = f out (singleProfile i pr) i
valuationLift :: Lifter Identity (Index ()) out ty u 
valuationLift f out pr i = f out (singleProfile i pr) ()
class UtilLift a b where
  utilLift :: Lifter a b out ty u
instance UtilLift Identity Int where
  utilLift = quasiLift
instance UtilLift Identity () where
  utilLift = valuationLift
instance UtilLift Coll Int where
  utilLift = id

data QuasiOutcome out u = QuasiOutcome { allocation :: out
                                       , transfers :: Transfers u
                                       }
  deriving Show
data Mechanism ty out = Mechanism { typeSets :: Coll (Set ty)
                                  , socialChoice :: SocialChoice Coll ty out
                                  }

totalUtility :: (Num u, UtilLift con i)
             => Utility out con ty i u
             -> out
             -> Profile Coll ty -> u
totalUtility f out pr = F.sum $ eachAgent f out pr

profiles :: (Ord ty) => Coll (Set ty) -> Set (Profile Coll ty)
profiles tyss =
  S.fromList $ P.fromList <$> sequence (F.toList $ F.toList <$> tyss)

strategies :: Set ty -> Coll (Strategy ty)
strategies tys = P.zip tys' <$> P.replicateM (S.size tys) tys'
  where
    tys' = P.fromList $ F.toList tys


-- Quasilinear environment

quasiUtility :: (Num u) => u -> Valuation out ty u -> QuasiUtility out ty u
quasiUtility initial vl (Outcome out) ty i =
  initial + vl (allocation out) ty () + transfers out P.! i

summarize :: (Num u)
          => Valuation out ty u
          -> Outcome (QuasiOutcome out u)
          -> Profile Coll ty -> Coll u
summarize vl = eachAgent (quasiUtility 0 vl)

singleProfile :: Index Int -> Profile Coll ty -> Profile Identity ty
singleProfile i pr = Identity $ pr P.! i

narrowProfile :: Index Int -> Profile Coll ty -> Profile Coll ty
narrowProfile i = P.ifilter (const . (/=) i)

clarke :: (Num u)
       => Allocator Coll ty out
       -> Valuation out ty u
       -> Profile Coll ty
       -> Transfers u
clarke al vl pr = groves al vl pr (P.imap tr pr)
  where
    tr i _ = negate $ totalUtility vl (al others) others
      where
        others = narrowProfile i pr

-- input tᵢ should be derived only from θ_{-i}
groves :: (Num u)
       => Allocator Coll ty out
       -> Valuation out ty u
       -> Profile Coll ty
       -> Transfers u
       -> Transfers u
groves al vl pr =
  P.zipWith (+) (P.imap (\i _ -> totalUtility vl (al pr) (narrowProfile i pr)) pr)


-- Properties

exPostRational :: (Num u, Ord u, Ord ty, UtilLift con i)
               => Utility out con ty i u
               -> Mechanism ty out -> Bool
exPostRational f mc =
  F.all (\pr -> F.all (>= 0) $ eachAgent f (socialChoice mc pr) pr) .
  profiles $ typeSets mc

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

budget :: (Ord ty, Ord u, Num u)
       => Mechanism ty (Outcome (QuasiOutcome out u)) -> BudgetBalance
budget mc =
  F.fold .
  S.map (balanced . F.sum . transfers . runOutcome . socialChoice mc) .
  profiles $ typeSets mc
  where
    balanced n
      | n > 0 = Not
      | n < 0 = Weak
      | otherwise = Strict

allocativelyEfficient :: (Ord ty, Num u, Ord u)
                      => Set out
                      -> Mechanism ty (Outcome (QuasiOutcome out u))
                      -> Valuation out ty u -> Bool
allocativelyEfficient outs mc vl = F.all test . profiles $ typeSets mc
  where
    best pr = F.maximum $ S.map (flip (totalUtility vl) pr) outs
    test pr =
      totalUtility vl (allocation . runOutcome $ socialChoice mc pr) pr == best pr

exPostEfficient :: (Ord ty, Ord u, UtilLift con i)
                => Set out
                -> Utility out con ty i u
                -> Mechanism ty out -> Bool
exPostEfficient outs f mc =
  F.all (\pr -> paretoOptimal outs (socialChoice mc pr) f pr) . profiles $
  typeSets mc

paretoOptimal :: (Ord u, UtilLift con i)
              => Set out
              -> out
              -> Utility out con ty i u
              -> Profile Coll ty -> Bool
paretoOptimal outs out f pr =
  not . F.or $ S.map (\out' -> F.and (compareEach (>=) out') &&
                               F.or (compareEach (>) out')) outs
  where
    compareEach cm out' = (P.zipWith cm `on` flip (eachAgent f) pr) out' out


-- Helper

eachAgent :: (UtilLift con i)
          => Utility out con ty i u
          -> out
          -> Profile Coll ty -> Coll u
eachAgent f out pr = P.imap (\i _ -> utilLift f out pr i) pr


-- Example

data Project = Project { completed :: Bool
                       , perCapitaCost :: Util Double
                       }
  deriving (Eq, Ord, Show)
           
publicProject :: Mechanism (Type (Util Double)) (Outcome (QuasiOutcome (Outcome Project) (Util Double)))
publicProject =
  Mechanism (P.replicate 2 $ S.fromList [20, 60])
    (\pr -> Outcome $ QuasiOutcome (al pr) (clarke al publicValuation pr))
  where
    cost = Util 50
    al p =
      Outcome $ Project (F.sum p > Type cost) (cost / fromIntegral (P.length p))

publicOutcomes :: Set (Outcome Project)
publicOutcomes = S.fromList $ (\b -> Outcome $ Project b 25) <$> [True, False]

publicValuation :: Valuation (Outcome Project) (Type (Util Double)) (Util Double)
publicValuation out (Identity (Type ty)) () =
  case out of
    Outcome (Project{completed = True,perCapitaCost = cs}) -> ty - cs
    Outcome (Project{completed = False})                   -> 0

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
