module Mechanism.Examples.PublicProject where

import qualified Data.Foldable              as F
import           Data.Functor               ((<$>))
import           Data.Set                   (Set)
import qualified Data.Set                   as S

import           Mechanism
import           Mechanism.Profile.Sequence (Coll)
import qualified Mechanism.Profile.Sequence as P

data Project = Completed { perCapitaCost :: Util Double }
             | Failed
  deriving (Eq, Ord, Show)

players :: Profile Coll Int
players = P.fromList [0, 1]

cost :: Util Double
cost = Util 50

typeSet :: Set (Type (Util Double))
typeSet = S.fromList [20, 60]

actionSet :: Set (Action (Util Double))
actionSet = S.fromList [20, 60]

outcomes :: Set (Outcome Project)
outcomes =
  S.fromList $ Outcome <$>
               [Completed (cost / fromIntegral (P.length players)), Failed]

valuation' :: Valuation Project (Util Double) (Util Double) Double
valuation' = valuation go
  where
    go (Outcome out) (Type ty) =
      case out of
        (Completed cs) -> ty - cs
        Failed         -> 0

allocator :: Allocator (Util Double) Project
allocator acs =
  Outcome $ if F.sum acs >= Action cost
              then Completed (cost / fromIntegral (P.length acs))
              else Failed

choice :: SocialChoice (Util Double) (QuasiOutcome Project Double)
choice acs =
  Outcome $ QuasiOutcome (allocator acs)
              (clarkes allocator (P.replicate (P.length acs) valuation') $ honest' <$> acs)

mechanism :: DirectMechanism (Util Double) (QuasiOutcome Project Double)
mechanism = directMechanism (P.replicate (P.length players) typeSet) choice

utilities :: QuasiUtilities Project (Util Double) (Util Double) Double
utilities = quasiUtility 0 valuation' <$> players

game :: DirectQuasiGame Project (Util Double) Double
game = Game utilities mechanism

shapleys :: Types (Util Double) -> Utils Double
shapleys tys = P.imap go tys
  where
    go i ty = shapleyValue ((\ty' -> Agent (actionSet, (valuation', ty'))) <$> exclude i tys)
                (characteristic allocator) $ Agent (actionSet, (valuation', ty))

clarkes' :: Types (Util Double) -> Transfers Double
clarkes' tys = clarkes allocator (P.replicate (P.length tys) valuation') tys

exPostRational' :: Bool
exPostRational' =
  exPostRational fs choice $ matches tyss acss
  where
    Game fs (Mechanism acss tyss _) = game

budget' :: BudgetBalance
budget' = budget . S.map (sc . snd . P.unzip) $ matches tyss acss
  where
    Mechanism acss tyss sc = mechanism

allocative' :: Bool
allocative' =
  allocativelyEfficient
    outcomes
    (P.replicate (P.length players) valuation')
    (runAllocation . runOutcome . sc)
    (profiles tyss)
  where
    Mechanism _ tyss sc = mechanism
