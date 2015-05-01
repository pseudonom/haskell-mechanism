module Mechanism.Profile.Vector where

import           Data.Vector (Vector)
import qualified Data.Vector as V

type Coll = Vector

fromList :: [a] -> Vector a
fromList = V.fromList

replicateM :: (Monad m) => Int -> m a -> m (Vector a)
replicateM = V.replicateM

zip :: Vector a -> Vector b -> Vector (a, b)
zip = V.zip

unzip :: Vector (a, b) -> (Vector a, Vector b)
unzip = V.unzip

(!) :: Vector a -> Int -> a
(!) = (V.!)

ifilter :: (Int -> a -> Bool) -> Vector a -> Vector a
ifilter = V.ifilter

imap :: (Int -> a -> b) -> Vector a -> Vector b
imap = V.imap

zipWith :: (a -> b -> c) -> Vector a -> Vector b -> Vector c
zipWith = V.zipWith

replicate :: Int -> a -> Vector a
replicate = V.replicate

length :: Vector a -> Int
length = V.length
