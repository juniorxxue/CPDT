{-# LANGUAGE GADTs #-}

module Demo where

-- oh, reflexive types
data Formula where
    Eq :: Integer -> Integer -> Formula
    And :: Formula -> Formula -> Formula
    Forall :: (Integer -> Formula) -> Formula

example1 = Forall (\x -> Eq x x)