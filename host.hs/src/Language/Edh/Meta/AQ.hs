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

-- | CPS computation performing analysis jobs, should capture their respective
-- input data and output `TVar`s as appropriate
type AnalysisInQueue = STM () -> STM ()

-- | Phases the whole analysis would go over, an analysis job pertain to a
-- later phase won't be performed until all jobs pertain to earlier phases have
-- finished.
data AnalysisPhase
  = -- | the 1st pass going over parsed nodes, probably not needed to be defined
    -- here
    ScanPhase
  | -- | analysis on the constructors an similar artifacts, those should be
    -- considered integral part of its outer artifact instead of nested,
    -- standalone members
    DefinePhase
  | -- | analysis on nested, standalone member artifacts, those separately
    -- callable, much later via a namespace (e.g. an object) reference
    CallInPhase
  deriving (Eq, Ord)

-- | Analysis job queue
--
-- this is a list of FIFO queues grouped and sorted by analysis phase
type AnalysisQueue = [(AnalysisPhase, TVar (FIFO AnalysisInQueue))]

-- | Schedule an analysis job into the queue
--
-- invariant: the list by `aqv` kept sorted
el'ScheduleAnalysis ::
  TVar AnalysisQueue ->
  AnalysisPhase ->
  AnalysisInQueue ->
  STM ()
el'ScheduleAnalysis !aqv !ap !aiq = do
  !aq <- readTVar aqv
  let go ::
        [(AnalysisPhase, TVar (FIFO AnalysisInQueue))] ->
        [(AnalysisPhase, TVar (FIFO AnalysisInQueue))] ->
        STM [(AnalysisPhase, TVar (FIFO AnalysisInQueue))]
      go !earlierPhases = \case
        [] ->
          newTVar (fifoSingleton aiq) >>= \ !pqv ->
            return $ reverse earlierPhases ++ [(ap, pqv)]
        curPhases@(phaseSlot@(!phase, !pqv) : laterPhases) ->
          case compare ap phase of
            EQ -> do
              modifyTVar' pqv $ fifoEnque aiq
              return aq
            LT ->
              newTVar (fifoSingleton aiq) >>= \ !pqv' ->
                return $ reverse earlierPhases ++ (ap, pqv') : curPhases
            GT -> go (phaseSlot : earlierPhases) laterPhases
  go [] aq >>= writeTVar aqv

-- | Perform all analysis jobs in the queue, including subsequent jobs
-- scheduled by earlier jobs per run
el'PerformAnalysis :: TVar AnalysisQueue -> STM () -> STM ()
el'PerformAnalysis !aqv !exit = iteration
  where
    iteration =
      readTVar aqv >>= \case
        [] -> exit
        (_phase, !pqv) : laterPhases -> do
          writeTVar aqv laterPhases
          let go :: (Maybe AnalysisInQueue, FIFO AnalysisInQueue) -> STM ()
              go (Nothing, _) = iteration
              go (Just !aiq, !more) = aiq $ go $ fifoDeque more
          readTVar pqv >>= go . fifoDeque
