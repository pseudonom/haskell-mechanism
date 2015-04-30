module Mechanism.Profile.Sequence where

import           Data.Sequence (Seq)
import qualified Data.Sequence as S

type Coll = Seq

fromList :: [a] -> Seq a
fromList = S.fromList

replicateM :: (Monad m) => Int -> m a -> m (Seq a)
replicateM = S.replicateM

zip :: Seq a -> Seq b -> Seq (a, b)
zip = S.zip

(!) :: Seq a -> Int -> a
(!) = S.index

ifilter :: (Int -> a -> Bool) -> Seq a -> Seq a
ifilter f = fmap snd . S.filter (uncurry f) . S.mapWithIndex (,)

imap :: (Int -> a -> b) -> Seq a -> Seq b
imap = S.mapWithIndex

zipWith :: (a -> b -> c) -> Seq a -> Seq b -> Seq c
zipWith = S.zipWith

replicate :: Int -> a -> Seq a
replicate = S.replicate

length :: Seq a -> Int
length = S.length
