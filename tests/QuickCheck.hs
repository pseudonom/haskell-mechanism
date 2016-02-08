{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Main where

import           Data.Functor ((<$>))

import           Test.QuickCheck

import           Mechanism
import           Mechanism.Profile.Sequence (Coll)
import qualified Mechanism.Profile.Sequence as P

type ParetoInput a = (Coll (Coll a), Coll a)

instance (Arbitrary a) => Arbitrary (Coll a) where
  arbitrary = P.fromList <$> arbitrary

instance (Arbitrary a) => Arbitrary (ParetoInput a) where
  arbitrary = do
    c <- arbitrary
    cs <- fmap P.fromList . listOf $ P.fromList <$> vectorOf (P.length c) arbitrary
    return (cs, c)

pareto :: ParetoInput Int -> Bool
pareto a = uncurry paretoOptimal a == uncurry paretoOptimal_ a

-- Fails with:
-- Module ‘Distribution.Simple.Test’ does not export ‘stubMain’
-- tests :: IO [Test]
-- tests = return [testProperty "De Morgan's Pareto" pareto]

main :: IO ()
main = quickCheck pareto
