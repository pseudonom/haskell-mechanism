module Mechanism.Examples.PrisonersDilemma where

import qualified Data.Foldable              as F
import           Data.Functor               ((<$>))
import           Data.Set                   (Set)
import qualified Data.Set                   as S

import           Mechanism
import qualified Mechanism.Profile.Sequence as P

data Cooperate = Cooperate | Defect deriving (Eq, Ord, Show, Enum, Bounded)

actions :: Set (Action Cooperate)
actions = S.fromList $ Action <$> enumFromTo minBound maxBound

mechanism :: ClassicMechanism Cooperate
mechanism = classicMechanism (P.replicate 2 actions)

player1 :: Actions Cooperate -> Util Int
player1 acs =
  case F.toList $ runAction <$> acs of
    [Cooperate, Cooperate] -> 2
    [Cooperate, Defect]    -> 0
    [Defect, Cooperate]    -> 3
    [Defect, Defect]       -> 1

player2 :: Actions Cooperate -> Util Int
player2 acs =
  case F.toList $ runAction <$> acs of
    [Cooperate, Cooperate] -> 2
    [Cooperate, Defect]    -> 3
    [Defect, Cooperate]    -> 0
    [Defect, Defect]       -> 1

utilities :: ClassicUtilities Cooperate Int
utilities = classicUtility <$> P.fromList [player1, player2]

game :: ClassicGame Cooperate Int
game = Game utilities mechanism

exPostRational' :: Bool
exPostRational' = exPostRational fs sc $ matches tyss acss
  where
    Game fs (Mechanism acss tyss sc) = game

dominantEquilibria :: Set (ClassicMatch Cooperate)
dominantEquilibria= equilibria dominantEquilibrium game

nashEquilibria :: Set (ClassicMatch Cooperate)
nashEquilibria = equilibria nashEquilibrium game
