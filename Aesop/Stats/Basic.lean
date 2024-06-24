/-
Copyright (c) 2022-2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Nanos
import Aesop.Rule.Name
import Aesop.Tracing

open Lean

namespace Aesop

initialize collectStatsOption : Lean.Option Bool ←
  Lean.Option.register `aesop.collectStats {
    defValue := false
    group := "aesop"
    descr := "(aesop) collect statistics about Aesop invocations. Use #aesop_stats to display the collected statistics."
  }

-- All times are in nanoseconds.
structure RuleStats where
  rule : DisplayRuleName
  elapsed : Nanos
  successful : Bool
  deriving Inhabited

namespace RuleStats

instance : ToString RuleStats where
  toString rp :=
    let success := if rp.successful then "successful" else "failed"
    s!"[{rp.elapsed.printAsMillis}] apply rule {rp.rule} ({success})"

end RuleStats


structure Stats where
  total : Nanos
  configParsing : Nanos
  ruleSetConstruction : Nanos
  search : Nanos
  ruleSelection : Nanos
  ruleStats : Array RuleStats
  cacheHits : Meta.Simp.CacheHits

namespace Stats

protected def empty : Stats where
  total := 0
  configParsing := 0
  ruleSetConstruction := 0
  search := 0
  ruleSelection := 0
  ruleStats := #[]
  cacheHits := {}

instance : EmptyCollection Stats :=
  ⟨Stats.empty⟩

instance : Inhabited Stats :=
  ⟨Stats.empty⟩

end Stats


structure RuleStatsTotals where
  /--
  Number of successful applications of a rule.
  -/
  numSuccessful : Nat
  /--
  Number of failed applications of a rule.
  -/
  numFailed : Nat
  /--
  Total elapsed time of successful applications of a rule.
  -/
  elapsedSuccessful : Nanos
  /--
  Total elapsed time of failed applications of a rule.
  -/
  elapsedFailed : Nanos

namespace RuleStatsTotals

protected def empty : RuleStatsTotals where
  numSuccessful := 0
  numFailed := 0
  elapsedSuccessful := 0
  elapsedFailed := 0

instance : EmptyCollection RuleStatsTotals :=
  ⟨.empty⟩

def compareByTotalElapsed : (x y : RuleStatsTotals) → Ordering :=
  compareOn λ totals => totals.elapsedSuccessful + totals.elapsedFailed

end RuleStatsTotals


namespace Stats

def ruleStatsTotals (p : Stats)
    (init : HashMap DisplayRuleName RuleStatsTotals := ∅) :
    HashMap DisplayRuleName RuleStatsTotals :=
  p.ruleStats.foldl (init := init) λ m rp => Id.run do
    let mut stats := m.findD rp.rule ∅
    if rp.successful then
      stats := { stats with
        numSuccessful := stats.numSuccessful + 1
        elapsedSuccessful := stats.elapsedSuccessful + rp.elapsed
      }
    else
      stats := { stats with
        numFailed := stats.numFailed + 1
        elapsedFailed := stats.elapsedFailed + rp.elapsed
      }
    m.insert rp.rule stats

def _root_.Aesop.sortRuleStatsTotals
    (ts : Array (DisplayRuleName × RuleStatsTotals)) :
    Array (DisplayRuleName × RuleStatsTotals) :=
  let lt := λ (n₁, t₁) (n₂, t₂) =>
    RuleStatsTotals.compareByTotalElapsed t₁ t₂ |>.swap.then
    (compare n₁ n₂)
    |>.isLT
  ts.qsort lt

def trace (p : Stats) (opt : TraceOption) : CoreM Unit := do
  if ! (← opt.isEnabled) then
    return
  let totalRuleApplications :=
    p.ruleStats.foldl (init := 0) λ total rp =>
      total + rp.elapsed
  aesop_trace![opt] "Total: {p.total.printAsMillis}"
  aesop_trace![opt] "Configuration parsing: {p.configParsing.printAsMillis}"
  aesop_trace![opt] "Rule set construction: {p.ruleSetConstruction.printAsMillis}"
  aesop_trace![opt] "Simp CacheHits / Hitrate:
    Negative: {p.cacheHits.negativeCacheHits} => {(p.cacheHits.negativeCacheHits / p.cacheHits.simpCalls) * 100}%
    Both: {p.cacheHits.bothCacheHits} => {(p.cacheHits.bothCacheHits / p.cacheHits.simpCalls) * 100}%
    Positive: {p.cacheHits.positiveCacheHits} => {(p.cacheHits.positiveCacheHits / p.cacheHits.simpCalls) * 100}%
    in {p.cacheHits.simpCalls} total simpCalls => {((p.cacheHits.negativeCacheHits+p.cacheHits.bothCacheHits+p.cacheHits.positiveCacheHits) /p.cacheHits.simpCalls)*100}%"
  withConstAesopTraceNode opt (collapsed := false)
      (return m!"Search: {p.search.printAsMillis}") do
    aesop_trace![opt] "Rule selection: {p.ruleSelection.printAsMillis}"
    withConstAesopTraceNode opt (collapsed := false)
        (return m!"Rule applications: {totalRuleApplications.printAsMillis}") do
      let timings := sortRuleStatsTotals p.ruleStatsTotals.toArray
      for (n, t) in timings do
        aesop_trace![opt] "[{(t.elapsedSuccessful + t.elapsedFailed).printAsMillis} / {t.elapsedSuccessful.printAsMillis} / {t.elapsedFailed.printAsMillis}] {n}"

end Stats


abbrev StatsRef := IO.Ref Stats

class MonadStats (m) extends
    MonadLiftT (ST IO.RealWorld) m,
    MonadLiftT BaseIO m,
    MonadOptions m where
  readStatsRef : m StatsRef

export MonadStats (readStatsRef)

variable [Monad m]

@[inline, always_inline]
def isStatsCollectionEnabled [MonadOptions m] : m Bool :=
  collectStatsOption.get <$> getOptions

@[inline, always_inline]
def isStatsTracingEnabled [MonadOptions m] : m Bool :=
  TraceOption.stats.isEnabled

@[inline, always_inline]
def isStatsCollectionOrTracingEnabled [MonadOptions m] : m Bool :=
  isStatsCollectionEnabled <||> isStatsTracingEnabled

variable [MonadStats m]

@[inline, always_inline]
def profiling (recordStats : Stats → α → Nanos → Stats) (x : m α) : m α := do
  if ← isStatsCollectionOrTracingEnabled then
    let (result, elapsed) ← time x
    (← readStatsRef).modify λ stats => recordStats stats result elapsed
    return result
  else
    x

@[inline, always_inline]
def profilingRuleSelection : m α → m α :=
  profiling λ stats _ elapsed =>
    { stats with ruleSelection := stats.ruleSelection + elapsed }

@[inline, always_inline]
def profilingRule (rule : DisplayRuleName) (wasSuccessful : α → Bool) :
    m α → m α :=
  profiling λ stats a elapsed =>
    let rp := { successful := wasSuccessful a, rule, elapsed }
    { stats with ruleStats := stats.ruleStats.push rp }

@[inline, always_inline]
def profilingRuleSimp (rule : DisplayRuleName) (wasSuccessful : α → Bool) (cacheHits : α → Lean.Meta.Simp.CacheHits):
    m α → m α :=
  profiling λ stats a elapsed =>
    let cacheHits := cacheHits a
    let rp := { successful := wasSuccessful a, rule, elapsed }
    { stats with ruleStats := stats.ruleStats.push rp , cacheHits := stats.cacheHits.mergeCacheHits cacheHits}

end Aesop
