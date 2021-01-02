module Language.Edh.Meta.AQ where

import Prelude

data FIFO a = FIFO ![a] ![a]
  deriving (Eq, Show)

fifoEmpty :: FIFO a
fifoEmpty = FIFO [] []

fifoEnque :: a -> FIFO a -> FIFO a
fifoEnque !e (FIFO back front) = FIFO (e : back) front

fifoDeque :: FIFO a -> (Maybe a, FIFO a)
fifoDeque (FIFO [] []) = (Nothing, fifoEmpty)
fifoDeque (FIFO back []) = fifoDeque $ FIFO [] (reverse back)
fifoDeque (FIFO back (tip : front)) = (Just tip, FIFO back front)

fifoPeek :: FIFO a -> (Maybe a, FIFO a)
fifoPeek (FIFO [] []) = (Nothing, fifoEmpty)
fifoPeek (FIFO back []) = fifoPeek $ FIFO [] (reverse back)
fifoPeek (FIFO back front@(tip : _)) = (Just tip, FIFO back front)
