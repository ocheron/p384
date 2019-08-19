{-# LANGUAGE OverloadedStrings #-}
module KAT_PubKey (tests) where

import Test.Tasty

import qualified KAT_PubKey.P384 as P384

tests = testGroup "PubKey"
    [ P384.tests
    ]
