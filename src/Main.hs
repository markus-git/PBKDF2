module Main where

import PBKDF2
import Control.Monad
import Control.DeepSeq
import System.CPUTime
import Text.Printf

main :: IO ()
main =
  do putStrLn "start"
     test 1
     test 10
     test 100
     test 1000
     putStrLn "end"

test :: Int -> IO ()
test n =
  do start <- getCPUTime
     ((iterate sha1 msg) !! n) `deepseq` return ()
     end <- getCPUTime
     let diff = (fromIntegral (end - start)) / (10^12)
     printf "iter %d, time %0.6f sec\n" (n :: Int) (diff :: Double)

