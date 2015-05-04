module Mechanism.Examples.Gloves where

import           Data.Monoid                ((<>))
import           Prelude                    hiding (Either (..))

import           Mechanism
import qualified Mechanism.Profile.Sequence as P

data Glove = Left | Right deriving (Eq, Ord, Show)

isLeft :: Glove -> Bool
isLeft Left = True
isLeft Right = False

characteristic' :: Agents Glove -> Util Double
characteristic' ags =
  Util $ min (fromIntegral $ P.length ls) (fromIntegral $ P.length rs)
  where
    (ls, rs) = P.partition (isLeft . runAgent) ags

shapleys :: (Int, Int) -> Utils Double
shapleys (l, r) = P.imap (\i -> shapleyValue (exclude i ags) characteristic') ags
  where
    ags = P.replicate l (Agent Left) <> P.replicate r (Agent Right)
