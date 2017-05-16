module Main where

import PBKDF2
import Control.Monad
import Control.DeepSeq
import System.CPUTime

main :: IO ()
main =
  do start <- getCPUTime
     ((iterate sha1 msg) !! 1000) `deepseq` return ()
     end <- getCPUTime
     let diff = (fromIntegral (end - start)) / (10^12)
     putStrLn $ "Computation time: " ++ show (diff :: Double) ++ " sec"
