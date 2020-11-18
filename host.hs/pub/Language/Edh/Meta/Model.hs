module Language.Edh.Meta.Model where

-- import           Debug.Trace

import           Control.Concurrent.STM
import           Control.Monad
import           Control.Monad.ST
import           Data.HashMap.Strict            ( HashMap )
import qualified Data.HashMap.Strict           as Map
import           Data.Vector                    ( Vector )
import qualified Data.Vector                   as V
import qualified Data.Vector.Mutable           as MV
import           Language.Edh.EHI
import           Prelude

data EL'Scope = EL'Scope
  { el'scope'src'loc :: !SrcLoc,
    -- a new region is created upon each attr definition or deletion
    el'scope'regions :: !EL'Region
  }

data EL'Region = EL'Region
  { el'region'src'span :: !SrcRange,
    el'region'attrs :: !(HashMap AttrKey EL'Arti)
  }

data EL'Arti = EL'Arti
  { el'arti'origin :: !SrcLoc,
    el'arti'type :: !(Maybe EdhTypeValue),
    el'arti'value :: !(Maybe EdhValue)
  }
