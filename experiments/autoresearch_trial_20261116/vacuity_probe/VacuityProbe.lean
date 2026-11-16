import Lean
import Recaman.LineCapacityPeriodic

/-!
# Mathlib-free vacuity probe (trial, 2026-11-16)

Modelled on the "vacuous hypotheses" / "unused binder" linters of atp-checkers
(arXiv 2606.29493) and on lean-lsp-mcp's `lean_minimal_hypotheses`, but
implemented directly as a metaprogram over the *elaborated* constants, so it
needs no Mathlib, no MCP server and no source rewriting.

For a theorem `∀ xs, concl` with proof value `v`, it reports

* `unused`    : Prop hypotheses whose free variable does not occur in `v xs`
                (conservative: an eta-reduced or delegated proof counts as use);
* `concl=hyp` : some hypothesis type is definitionally the conclusion;
* `False`     : `False` is closed from the hypotheses by `omega`, `simp_all`
                or `grind` under a heartbeat cap (contradictory hypotheses);
* `shallow`   : the conclusion is closed by `omega` or `grind` from the
                hypotheses alone, ignoring the proof (a "pure automation" signal,
                informative only; many genuine helper lemmas are shallow);
* `objects`   : some binder or the conclusion mentions a `Recaman.*` constant.
                `shallow` without `objects` is the elaborated form of G3's
                "pure arithmetic over free Nat/Int" rule and is flagged.

The output is a review signal for the auditor, not a verdict.  This file is
outside the `Recaman` library and is not imported by it.
-/

open Lean Meta Elab Term Command

namespace VacuityProbe

/-- Run `x` under a fresh heartbeat budget; any exception, including the
deterministic-timeout runtime exception (not caught by plain `try`), yields `dflt`. -/
def capped {α} (x : TermElabM α) (dflt : α) (hb : Nat := 4000) : TermElabM α := do
  let s ← saveState
  tryCatchRuntimeEx
    (do
      let r ← withTheReader Core.Context (fun c => { c with maxHeartbeats := hb * 1000 }) do
        withCurrHeartbeats x
      s.restore
      pure r)
    (fun _ => do s.restore; pure dflt)

/-- Try a tactic on `goal` without keeping any state; true iff it closes the goal. -/
def closes (goal : MVarId) (tac : TSyntax `tactic) (hb : Nat := 4000) : TermElabM Bool :=
  capped (do
    let gs ← Tactic.run goal (Tactic.evalTactic tac)
    pure gs.isEmpty) false hb

def anyCloses (ty : Expr) (tacs : List (TSyntax `tactic)) : TermElabM (Option String) := do
  for t in tacs do
    let g ← mkFreshExprMVar ty
    if ← closes g.mvarId! t then
      return some (toString t.raw.getKind |>.replace "Lean.Parser.Tactic." "" |>.replace "tactic" "")
  return none

structure Report where
  name : Name
  nHyps : Nat
  unused : List Name
  conclIsHyp : Bool
  falseBy : Option String
  shallowBy : Option String
  objects : Bool

def probe (c : Name) : TermElabM Report := do
  let info ← getConstInfo c
  -- `ConstantInfo.value?` returns `none` for theorems in Lean 4.33, so match directly.
  let body? : Option Expr := match info with
    | .thmInfo t => some t.value
    | .defnInfo d => some d.value
    | _ => none
  forallTelescope info.type fun xs concl => do
    let mut hyps : Array Expr := #[]
    for x in xs do
      if ← isProp (← inferType x) then hyps := hyps.push x
    let mut unused : List Name := []
    if let some v := body? then
      let b := (mkAppN v xs).headBeta
      for h in hyps do
        unless b.containsFVar h.fvarId! do
          unused := unused ++ [← h.fvarId!.getUserName]
    let mut conclIsHyp := false
    for h in hyps do
      let ht ← inferType h
      if ← capped (withNewMCtxDepth (isDefEq ht concl)) false then conclIsHyp := true
    let falseBy ← if hyps.isEmpty then pure none else
      anyCloses (mkConst ``False) [← `(tactic| omega), ← `(tactic| simp_all), ← `(tactic| grind)]
    let shallowBy ← anyCloses concl [← `(tactic| omega), ← `(tactic| grind)]
    -- does any binder type or the conclusion mention a `Recaman.*` constant?
    let mut objects := (concl.getUsedConstants.any (·.getRoot == `Recaman))
    for x in xs do
      if (← inferType x).getUsedConstants.any (·.getRoot == `Recaman) then objects := true
    return { name := c, nHyps := hyps.size, unused, conclIsHyp, falseBy, shallowBy, objects }

def flagged (r : Report) : Bool :=
  !r.unused.isEmpty || r.conclIsHyp || r.falseBy.isSome || (!r.objects && r.shallowBy.isSome)

def render (r : Report) : String :=
  s!"{if flagged r then "FLAG" else "ok  "} {r.name} hyps={r.nHyps} unused={r.unused} " ++
  s!"concl=hyp={r.conclIsHyp} False={r.falseBy.getD "-"} shallow={r.shallowBy.getD "-"} " ++
  s!"objects={r.objects}"

/-- `#vacuity_probe n₁ n₂ ...` probes the named theorems. -/
elab "#vacuity_probe " ns:ident* : command => liftTermElabM do
  for n in ns do
    let c ← realizeGlobalConstNoOverloadWithInfo n
    logInfo (render (← probe c))

/-- `#vacuity_probe_module M` probes every theorem declared in module `M`
(auxiliary and internal declarations skipped). -/
elab "#vacuity_probe_module " m:ident : command => liftTermElabM do
  let env ← getEnv
  let some idx := env.getModuleIdx? m.getId | throwError "module {m.getId} not imported"
  let names := (env.header.moduleData[idx.toNat]!).constNames
  let mut lines : Array String := #[]
  let mut flagged := 0
  let mut total := 0
  for c in names do
    if c.isInternalDetail then continue
    let some (.thmInfo _) := env.find? c | continue
    total := total + 1
    let r ← probe c
    if VacuityProbe.flagged r then flagged := flagged + 1
    lines := lines.push (render r)
  logInfo (s!"module {m.getId}: {total} theorems, {flagged} flagged\n" ++ "\n".intercalate lines.toList)

end VacuityProbe
