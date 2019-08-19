{-# LANGUAGE OverloadedStrings #-}
module Main where

import Imports

import qualified KAT_PubKey

tests = testGroup "p384"
    [ KAT_PubKey.tests
    ]

main = defaultMain tests
