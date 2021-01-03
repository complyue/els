module Language.Edh.Meta.AQ where

import Control.Concurrent.STM
import Prelude

data FIFO a = FIFO ![a] ![a]
  deriving (Eq, Show)

fifoEmpty :: FIFO a
fifoEmpty = FIFO [] []

fifoSingleton :: a -> FIFO a
fifoSingleton !a = FIFO [] [a]

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

type AnalysisInQueue = STM () -> STM ()

data AnalysisPhase
  = ScanPhase
  | DefinePhase
  | CallInPhase
  deriving (Eq, Ord)

type AnalysisQueue = [(AnalysisPhase, TVar (FIFO AnalysisInQueue))]

el'scheduleAnalysis ::
  TVar AnalysisQueue ->
  AnalysisPhase ->
  AnalysisInQueue ->
  STM ()
el'scheduleAnalysis !aqv !ap !aiq = do
  !aq <- readTVar aqv
  let go ::
        [(AnalysisPhase, TVar (FIFO AnalysisInQueue))] ->
        [(AnalysisPhase, TVar (FIFO AnalysisInQueue))] ->
        STM [(AnalysisPhase, TVar (FIFO AnalysisInQueue))]
      go !earlierQues = \case
        [] ->
          newTVar (fifoSingleton aiq) >>= \ !pqv ->
            return $ reverse earlierQues ++ [(ap, pqv)]
        ques@(pSlot@(!phase, !pqv) : laterQues) -> case compare ap phase of
          EQ -> do
            modifyTVar' pqv $ fifoEnque aiq
            return aq
          LT ->
            newTVar (fifoSingleton aiq) >>= \ !pqv' ->
              return $ reverse earlierQues ++ (ap, pqv') : ques
          GT -> go (pSlot : earlierQues) laterQues
  go [] aq >>= writeTVar aqv

el'performAnalysis :: TVar AnalysisQueue -> STM () -> STM ()
el'performAnalysis !aqv !exit =
  readTVar aqv >>= \case
    [] -> exit
    (_phase, !pqv) : laterQues -> do
      writeTVar aqv laterQues
      let go :: (Maybe AnalysisInQueue, FIFO AnalysisInQueue) -> STM ()
          go (Nothing, _) = el'performAnalysis aqv exit
          go (Just !aiq, !more) = aiq $ go $ fifoDeque more
      readTVar pqv >>= go . fifoDeque
