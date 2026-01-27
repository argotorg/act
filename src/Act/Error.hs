{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Error
Description : An instantiation of 'Validation' with our error type.

This specializes 'Data.Validation.Validation' to keep its errors in a 'NonEmpty' list
and keep track of a 'Pn' for every error it logs. There is also some infrastructure
around modified chaining/branching behaviours.
-}

module Act.Error (module Act.Error) where

import Data.List (find)
import Data.Validation as Act.Error

import Act.Syntax.Untyped (Pn)
import Act.Lex
import System.IO (hPutStrLn, stderr)
import System.Exit (exitFailure)

import qualified Data.Text as Text

-- Reexport NonEmpty so that we can use `-XOverloadedLists` without thinking.
import Data.List.NonEmpty as Act.Error (NonEmpty)


-- Error with position information
type Error e = Validation (NonEmpty (Pn,e))

throw :: (Pn,e) -> Error e a
throw msg = Failure [msg]


assert :: (Pn, e) -> Bool -> Error e ()
assert err b = if b then pure () else throw err

foldValidation :: (b -> a -> Error err b) -> b -> [a] -> Error err b
foldValidation _ b [] = pure b
foldValidation f b (a:as) = f b a `bindValidation` \b' -> foldValidation f b' as


-- Error without position information for use with HEVM equivalence
type EquivError e = Validation (NonEmpty e)

throwErr :: e -> EquivError e a
throwErr msg = Failure [msg]

infixr 1 <==<, >==>

-- Like 'Control.Monad.(>=>)' but allows us to chain error-prone
-- computations even without a @Monad@ instance.
(>==>) :: (a -> Error e b) -> (b -> Error e c) -> a -> Error e c
f >==> g = \x -> f x `bindValidation` g

(<==<) :: (b -> Error e c) -> (a -> Error e b) -> a -> Error e c
(<==<) = flip (>==>)

-- | Runs through a list of error-prone computations and returns the first
-- successful one, with the definition of "success" expanded to include
-- failures which did not generate any error at the supplied position.
notAtPosn :: Pn -> [Error e a] -> Maybe (Error e a)
notAtPosn p = find valid
  where
    valid (Success _)    = True
    valid (Failure errs) = all ((p /=) . fst) errs

-- | Try to find a succesfull computation in a list, and if it fails
-- it returns a default computation
findSuccess :: Error e a -> [Error e a] -> Error e a
findSuccess d comp = case find valid comp of
                       Just a -> a
                       Nothing -> foldl (*>) d comp
  where
    valid (Success _) = True
    valid _ = False


concatError ::  Error e a -> [Error e a] -> Error e a
concatError def = \case
  [] -> def
  x:xs -> foldl (*>) x xs


prettyErrs :: Traversable t => String -> t (Pn, String) -> IO ()
prettyErrs contents errs = mapM_ prettyErr errs >> exitFailure
  where
  prettyErr (pn, msg) | pn == nowhere = do
    hPutStrLn stderr "Internal error:"
    hPutStrLn stderr msg
  prettyErr (pn, msg) | pn == lastPos = do
    let culprit = last $ lines contents
        line' = length (lines contents) - 1
        col  = length culprit
    hPutStrLn stderr $ show line' <> " | " <> culprit
    hPutStrLn stderr $ Text.unpack (Text.replicate (col + length (show line' <> " | ") - 1) " " <> "^")
    hPutStrLn stderr msg
  prettyErr (AlexPn _ line' col, msg) = do
    let cxt = safeDrop (line' - 1) (lines contents)
    hPutStrLn stderr $ msg <> ":"
    hPutStrLn stderr $ show line' <> " | " <> head cxt
    hPutStrLn stderr $ Text.unpack (Text.replicate (col + length (show line' <> " | ") - 1) " " <> "^")
    where
      safeDrop :: Int -> [a] -> [a]
      safeDrop 0 a = a
      safeDrop _ [] = []
      safeDrop _ [a] = [a]
      safeDrop n (_:xs) = safeDrop (n-1) xs
