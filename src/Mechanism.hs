{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns               #-}

module Mechanism where

import           Control.Applicative        (Const (..), pure)
import           Control.Arrow              (first)
import           Control.Monad              (replicateM)
import qualified Data.Foldable              as F
import           Data.Function              (on)
import           Data.Functor               ((<$>))
import qualified Data.List                  as L
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
  deriving (Eq, Ord, Num, Show)
newtype Util u = Util { runUtil :: u }
  deriving (Eq, Ord, Num, Fractional, Show)

type Profile con pr = con pr
type Index i = i
type Transfer u = Util u
type Strategy ty ac = Coll (Type ty, Action ac)
type Match ty ac = Profile Coll (Type ty, Action ac)
type ClassicMatch ac = Match () ac

type Utility out con ac ty u = Outcome out -> Profile con (Action ac) -> Type ty -> Util u
type Valuation out ac ty u = Utility out (Const ()) ac ty u
type QuasiUtility out ac ty u = Utility (QuasiOutcome out u) (Const ()) ac ty u
type ClassicUtility ac u = Utility () Coll ac () u

type SocialChoice ac out = Actions ac -> Outcome out
type Allocator ac out = SocialChoice ac out

type Types a = Profile Coll (Type a)
type Actions a = Profile Coll (Action a)
type Utils u = Profile Coll (Util u)
type Transfers u = Profile Coll (Transfer u)

type TypeSets ty = Profile Coll (Set (Type ty))
type ActionSets ac = Profile Coll (Set (Action ac))

type Utilities out con ac ty u = Profile Coll (Utility out con ac ty u)
type Valuations out ac ty u = Profile Coll (Valuation out ac ty u)
type QuasiUtilities out ac ty u = Profile Coll (QuasiUtility out ac ty u)
type ClassicUtilities ac u = Profile Coll (ClassicUtility ac u)

newtype Agent ag = Agent { runAgent :: ag }
type Agents ag = Profile Coll (Agent ag)
type Coalition ag = Agents ag
type Characteristic ag u = Coalition ag -> Util u

data QuasiOutcome out u =
       QuasiOutcome
         { runAllocation :: Outcome out
         , runTransfers  :: Transfers u
         }
  deriving (Eq, Ord, Show)
data Mechanism ac ty out =
       Mechanism
         { runActionSets   :: ActionSets ac
         , runTypeSets     :: TypeSets ty
         , runSocialChoice :: SocialChoice ac out
         }
type DirectMechanism ty out = Mechanism ty ty out
type ClassicMechanism ac = Mechanism ac () ()
data Game out con ac ty u =
       Game
         { runUtilities :: Utilities out con ac ty u
         , runMechanism :: Mechanism ac ty out
         }
type DirectGame out con ty u = Game out con ty ty u
type QuasiGame out ac ty u = Game (QuasiOutcome out u) (Const ()) ac ty u
type DirectQuasiGame out ty u = Game (QuasiOutcome out u) (Const ()) ty ty u
type ClassicGame ac u = Game () Coll ac () u

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


-- Classic game (e.g. Prisoner's dilemma)

classicUtility :: (Actions ac -> Util u) -> ClassicUtility ac u
classicUtility f (Outcome ()) acs (Type ()) = f acs

classicMechanism :: ActionSets ac -> ClassicMechanism ac
classicMechanism acss =
  Mechanism acss (P.replicate (P.length acss) . S.singleton $ Type ()) (const $ Outcome ())

-- Quasilinear environment

valuation :: (Outcome out -> Type ty -> Util u) -> Valuation out ty ty u
valuation vl out (Const ()) = vl out

quasiUtility :: (Num u)
             => Util u
             -> Valuation out ac ty u
             -> Index Int
             -> QuasiUtility out ac ty u
quasiUtility initial vl i (Outcome (QuasiOutcome al tr)) (Const ()) ty =
  initial + vl al (Const ()) ty + tr P.! i

exclude :: Index Int -> Profile Coll a -> Profile Coll a
exclude i = P.ifilter (const . (/=) i)

clarkes :: (Num u)
        => Allocator ty out
        -> Valuations out ac ty u
        -> Types ty
        -> Transfers u
clarkes al vls tys =
  P.imap (\i _ -> clarke (al acs) (al $ exclude i acs) (exclude i vls) (exclude i tys)) tys
  where
    acs = honest <$> tys

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
  P.imap (\i -> grove out (exclude i vls) (exclude i tys))


-- Properties

-- We've modified the standard properties a bit to work with indirect games.
-- Instead of passing in a game and checking for all type profiles,
-- we pass in the matches.
-- By pre-filtering, we choose whether to check the property
-- for all matches, all honest matches, all equilibrium matches, etc.

exPostRational :: (Ord u, Num u, Ord ty, Ord ac, Narrow con)
               => Utilities out con ac ty u
               -> SocialChoice ac out
               -> Set (Match ty ac) -> Bool
exPostRational fs sc = F.all go
  where
    go (P.unzip -> (tys, acs)) =
      F.all (>= 0) $ agentUtilities out fs (narrow acs) tys
      where
        out = sc acs

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
budget os = F.fold . S.map (balanced . F.sum . runTransfers . runOutcome) $ os
  where
    balanced n
      | n > 0 = Not
      | n < 0 = Weak
      | otherwise = Strict

allocativelyEfficient :: (Num u, Ord u)
                      => Set (Outcome out)
                      -> Valuations out ty ty u
                      -> SocialChoice ty out
                      -> Set (Types ty)
                      -> Bool
allocativelyEfficient outs vls sc =
  F.all (\tys ->
          totalUtility (sc $ honest <$> tys) vls (Const ()) tys ==
          F.maximum (S.map (\out' -> totalUtility out' vls (Const ()) tys) outs))

exPostEfficient :: (Narrow con, Ord ac, Ord ty, Ord u)
                => Set (Outcome out)
                -> Utilities out con ac ty u
                -> SocialChoice ac out
                -> Set (Match ty ac)
                -> Bool
exPostEfficient outs fs sc =
  F.all
    (\(P.unzip -> (tys, acs)) ->
       paretoOptimal ((\out' -> agentUtilities out' fs (narrow acs) tys) <$> outs')
         (agentUtilities (sc acs) fs (narrow acs) tys))
  where
    outs' = P.fromList $ F.toList outs

-- Textbook definition
paretoOptimal_ :: (Ord a) => Coll (Profile Coll a) -> Profile Coll a -> Bool
paretoOptimal_ cs c =
  not . F.or $ (\c' -> F.and (P.zipWith (>=) c' c) && F.or (P.zipWith (>) c' c)) <$> cs

-- De Morganed (a little clearer, I think)
paretoOptimal :: (Ord a) => Coll (Profile Coll a) -> Profile Coll a -> Bool
paretoOptimal cs c =
  F.and $ (\c' -> F.or (P.zipWith (<) c' c) || F.and (P.zipWith (<=) c' c)) <$> cs

dominantEquilibrium :: (Narrow con, Ord ac, Ord u)
                    => Utilities out con ac ty u
                    -> SocialChoice ac out
                    -> Set (Actions ac)
                    -> Match ty ac
                    -> Bool
dominantEquilibrium fs sc acss m =
  F.and . P.imap (\i ((ty, ac), f) -> dominant f sc acss ty ac i) $ P.zip m fs

dominant :: (Ord ac, Narrow con, Ord u)
         => Utility out con ac ty u
         -> SocialChoice ac out
         -> Set (Actions ac)
         -> Type ty
         -> Action ac
         -> Index Int
         -> Bool
dominant f sc acss ty ac i =
  F.all best . fmap (L.partition ((==) ac . flip (P.!) i)) .
               sortGroup (exclude i) $ F.toList acss
  where
    best ([strat], others) =
      F.all (\other -> u >= f (sc other) (narrow other) ty) others
      where
        u = f (sc strat) (narrow strat) ty

nashEquilibrium :: (Eq ac, Narrow con, Ord u)
                => Utilities out con ac ty u
                -> SocialChoice ac out
                -> Set (Actions ac)
                -> Match ty ac
                -> Bool
nashEquilibrium fs sc acss m = F.and . P.imap each $ P.zip m fs
  where
    each i ((ty, ac), f) = best . S.partition ((==) ac . flip (P.!) i) $
      S.filter (\acs' -> acs == exclude i acs') acss
      where
        acs = exclude i . snd $ P.unzip m
        best (S.elemAt 0 -> strat, others) =
          F.all (\other -> f out (narrow strat) ty >=
                           f (sc other) (narrow other) ty) others
          where
            out = sc strat

equilibria :: (Narrow con, Ord ac, Ord u, Ord ty)
           => Equilibrium out con ac ty u -> Game out con ac ty u -> Set (Match ty ac)
equilibria eq (Game fs (Mechanism acss tyss sc)) =
  S.filter (eq fs sc (profiles acss)) $ matches tyss acss

type Equilibrium out con ac ty u = Utilities out con ac ty u
                                -> SocialChoice ac out
                                -> Set (Actions ac) -> Match ty ac -> Bool

implementable :: (Ord ty, Ord out)
              => SocialChoice ac out
              -> Set (Match ty ac)
              -> SocialChoice ty out
              -> Bool
implementable sca ms sct = F.all go $ S.map (fst . P.unzip) ms
  where
    go tys =
      S.member (sct $ honest <$> tys) .
      S.map (sca . snd . P.unzip) $
        S.filter ((==) tys . fst . P.unzip) ms

incentiveCompatible :: (Ord ty, Narrow con, Ord u)
                    => Equilibrium out con ty ty u
                    -> DirectGame out con ty u -> Bool
incentiveCompatible eq gm = F.any (F.all isHonest) $ equilibria eq gm


-- Helpers

agentUtilities :: Outcome out
               -> Utilities out con ac ty u
               -> Profile con (Action ac)
               -> Types ty
               -> Utils u
agentUtilities out fs acs = P.zipWith (\f -> f out acs) fs

totalUtility :: (Num u)
             => Outcome out
             -> Utilities out con ac ty u
             -> Profile con (Action ac)
             -> Types ty
             -> Util u
totalUtility out fs acs tys = F.sum $ agentUtilities out fs acs tys

profiles :: (Ord a) => Profile Coll (Set a) -> Set (Profile Coll a)
profiles tyss =
  S.fromList $ P.fromList <$> T.sequence (F.toList $ F.toList <$> tyss)

strategies :: (Ord ac, Ord ty)
           => Set (Type ty) -> Set (Action ac) -> Set (Strategy ty ac)
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

sortGroup :: (Ord b) => (a -> b) -> [a] -> [[a]]
sortGroup f = L.groupBy ((==) `on` f) . L.sortBy (compare `on` f)


-- Cooperative games

shapleyValue :: (Num u, Fractional u)
             => Coalition ag -> Characteristic ag u -> Agent ag -> Util u
shapleyValue ags c ag = F.sum $ go <$> powerset ags
  where
    go co = (Util $ fac s * fac (n - s) / fac (n + 1)) * (c (ag P.<| co) - c co)
      where
        s = P.length co
        n = P.length ags
        fac = fromIntegral . factorial

factorial :: Int -> Int
factorial n = product [1..n]

powerset :: Coll a -> Coll (Coll a)
powerset = P.filterM (const $ P.fromList [True, False])

characteristic :: (Num u, Narrow con, Ord ac, Ord u)
               => SocialChoice ac out
               -> Characteristic (Set (Action ac), (Utility out con ac ty u, Type ty)) u
characteristic sc ags = F.maximum $ S.map go acss
  where
    go acs = F.sum $ (\(f, ty) -> f out (narrow acs) ty) <$> ftys where
      out = sc acs
    (acss, ftys) = first profiles . P.unzip $ runAgent <$> ags


-- dictator :: Set (Outcome out) -> SocialChoice ty out ->
--             Utility out ty u -> Maybe Integer
-- exAnteRational :: Dist Profile -> Utility out ty u -> Mechanism ty out u -> Bool
-- interimRational :: Dist Profile -> Utility out ty u -> Mechanism ty out u -> Bool

-- monotonic :: Set (Outcome out) -> Utility out ty u ->
--              Mechanism (Type ty) out u -> Bool
-- lowerContourSet :: Set (Outcome out) -> Outcome out -> Type ty ->
--                    Utility out ty u -> Set (Outcome out)
-- dagva :: Allocator ty out u -> Valuation out ty u -> Dist Profile ->
--          Transfer ty u
