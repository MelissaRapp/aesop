

import Lean.Meta.Tactic.Simp


open Lean Lean.Meta
namespace Aesop

structure NegativeCachingState where
  negativeCache : Simp.NegativeCache
  knownHyps : HashSet Origin
  deriving Inhabited

abbrev CacheRef := IO.Ref NegativeCachingState

class MonadCache (m) extends
    MonadLiftT (ST IO.RealWorld) m,
    MonadLiftT BaseIO m,
    MonadOptions m where
  readCacheRef : m CacheRef

export MonadCache (readCacheRef)

variable [Monad m]
variable [MonadCache m]

def getCurrentCache : m Simp.NegativeCache := do
  return (← (← readCacheRef).get).negativeCache

def getCurrentKnownHyps : m (HashSet Origin) := do
  return (← (← readCacheRef).get).knownHyps

def modifyNegativeCachingState (f : NegativeCachingState → NegativeCachingState) : m Unit := do
    (← readCacheRef).modify f
