import Lean

/-!
# Lean-side harness tools (G6 statement pins and the vacuity lint)

Outside the `Recaman` library; compiled by `scripts/harness_lean.py` into
`.lake/build/harness/`. Nothing here is a research result.

* `#pin_deps n₁ n₂ ...` prints one line per constant in the transitive closure of
  `Recaman.*` / `RecamanProtected.*` constants used by the named pins (types,
  definition values, inductive constructors), with structural hashes of type and
  value. `docs/protected_pins/definitions.lock` stores this output; G6 fails on
  any drift, so redefining e.g. `signSum` cannot silently change a pinned claim.
* `#pin_sanity n` tries to derive `False` from the hypotheses of the pinned `Prop`
  (a pin whose hypotheses are contradictory would be vacuously provable).
* `#vacuity_probe n₁ ...` / `#vacuity_probe_module M` report, per theorem:
  Prop hypotheses absent from the proof term, a hypothesis definitionally equal to
  the conclusion, `False` derivable from the hypotheses, and a conclusion closed by
  automation without mentioning any `Recaman.*` constant. `?` means a heartbeat
  timeout, i.e. not probed, never "clean".
-/

open Lean Meta Elab Term Command

namespace HarnessTools

/-! ## Bounded tactic attempts -/

/-- Result of a bounded attempt: closed, not closed, or timed out (unknown). -/
inductive Attempt where
  | closed | failed | timeout
deriving BEq, Inhabited

/-- Run `x` under a fresh heartbeat budget without keeping state. Runtime
exceptions (heartbeat/recursion limits) are not caught by plain `try`. -/
def capped (x : TermElabM Bool) (hb : Nat := 4000) : TermElabM Attempt := do
  let s ← saveState
  let r ← tryCatchRuntimeEx
    (do
      let ok ← withTheReader Core.Context (fun c => { c with maxHeartbeats := hb * 1000 }) do
        withCurrHeartbeats x
      pure (if ok then Attempt.closed else Attempt.failed))
    (fun ex => pure (if ex.isRuntime then Attempt.timeout else Attempt.failed))
  s.restore
  return r

def tacName (t : TSyntax `tactic) : String :=
  match t.raw.getKind with
  | `Lean.Parser.Tactic.omega => "omega"
  | `Lean.Parser.Tactic.simpAll => "simp_all"
  | `Lean.Parser.Tactic.grind => "grind"
  | k => toString k

/-- `some name` if a tactic closes `ty`; `none` if all fail; `some "?"` if none
closed it and at least one timed out. -/
def anyCloses (ty : Expr) (tacs : List (TSyntax `tactic)) : TermElabM (Option String) := do
  let mut timedOut := false
  for t in tacs do
    let g ← mkFreshExprMVar ty
    match ← capped (do
        let gs ← Tactic.run g.mvarId! (Tactic.evalTactic t)
        pure gs.isEmpty) with
    | .closed => return some (tacName t)
    | .timeout => timedOut := true
    | .failed => pure ()
  return if timedOut then some "?" else none

def falseTactics : TermElabM (List (TSyntax `tactic)) :=
  return [← `(tactic| omega), ← `(tactic| simp_all), ← `(tactic| grind)]

/-! ## Vacuity probe -/

structure Report where
  name : Name
  nHyps : Nat
  unused : List Name
  conclIsHyp : String      -- "yes" | "no" | "?"
  falseBy : Option String  -- tactic deriving False from the hypotheses, "?" = timeout
  shallowBy : Option String
  objects : Bool

def mentionsLibrary (e : Expr) : Bool :=
  e.getUsedConstants.any (·.getRoot == `Recaman)

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
    let mut conclIsHyp := "no"
    for h in hyps do
      let ht ← inferType h
      match ← capped (withNewMCtxDepth (isDefEq ht concl)) with
      | .closed => conclIsHyp := "yes"
      | .timeout => if conclIsHyp == "no" then conclIsHyp := "?"
      | .failed => pure ()
    let falseBy ← if hyps.isEmpty then pure none else anyCloses (mkConst ``False) (← falseTactics)
    let shallowBy ← anyCloses concl [← `(tactic| omega), ← `(tactic| grind)]
    let mut objects := mentionsLibrary concl
    for x in xs do
      if mentionsLibrary (← inferType x) then objects := true
    return { name := c, nHyps := hyps.size, unused, conclIsHyp, falseBy, shallowBy, objects }

def flagged (r : Report) : Bool :=
  !r.unused.isEmpty || r.conclIsHyp == "yes" ||
    (r.falseBy.isSome && r.falseBy != some "?") ||
    (!r.objects && r.shallowBy.isSome && r.shallowBy != some "?")

def unknown (r : Report) : Bool :=
  r.conclIsHyp == "?" || r.falseBy == some "?"

def render (r : Report) : String :=
  let tag := if flagged r then "FLAG" else if unknown r then "?   " else "ok  "
  s!"{tag} {r.name} hyps={r.nHyps} unused={r.unused} concl=hyp={r.conclIsHyp} " ++
  s!"False={r.falseBy.getD "-"} shallow={r.shallowBy.getD "-"} objects={r.objects}"

elab "#vacuity_probe " ns:ident* : command => liftTermElabM do
  for n in ns do
    let c ← realizeGlobalConstNoOverloadWithInfo n
    logInfo (render (← probe c))

elab "#vacuity_probe_module " m:ident : command => liftTermElabM do
  let env ← getEnv
  let some idx := env.getModuleIdx? m.getId | throwError "module {m.getId} not imported"
  let names := (env.header.moduleData[idx.toNat]!).constNames
  let mut lines : Array String := #[]
  let mut nFlag := 0
  let mut nUnknown := 0
  let mut total := 0
  for c in names do
    if c.isInternalDetail then continue
    let some (.thmInfo _) := env.find? c | continue
    total := total + 1
    let r ← probe c
    if flagged r then nFlag := nFlag + 1
    else if unknown r then nUnknown := nUnknown + 1
    lines := lines.push (render r)
  logInfo (s!"module {m.getId}: {total} theorems, {nFlag} flagged, {nUnknown} unknown\n" ++
    "\n".intercalate lines.toList)

/-! ## Statement pins -/

def tracked (n : Name) : Bool :=
  n.getRoot == `Recaman || n.getRoot == `RecamanProtected

def hex (h : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 h.toNat)
  "".pushn '0' (16 - s.length) ++ s

/-- 64-bit hash of the full debug rendering (`Expr.hash` itself is only 32-bit). -/
def fingerprint (e : Expr) : String := hex (toString e).hash

/-- Transitive dependencies (tracked constants only), each with a kind and
structural hashes of its type and value. -/
def pinDeps (roots : Array Name) : CoreM (Array String) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo := roots.toList
  let mut out : Array (Name × String) := #[]
  for _ in [0:100000] do
    match todo with
    | [] => break
    | c :: rest =>
      todo := rest
      if seen.contains c then continue
      seen := seen.insert c
      let some info := env.find? c | throwError "unknown constant {c}"
      let (kind, valHash, more) : String × String × Array Name := match info with
        | .defnInfo d => ("def", fingerprint d.value, d.value.getUsedConstants)
        | .thmInfo _ => ("theorem", "-", #[])
        | .opaqueInfo o => ("opaque", fingerprint o.value, o.value.getUsedConstants)
        | .inductInfo i => ("inductive", s!"ctors={i.ctors}", i.ctors.toArray)
        | .ctorInfo _ => ("ctor", "-", #[])
        | .recInfo _ => ("recursor", "-", #[])
        | .axiomInfo _ => ("postulate", "-", #[])
        | .quotInfo _ => ("quot", "-", #[])
      out := out.push (c, s!"{c}\t{kind}\t{fingerprint info.type}\t{valHash}")
      for d in info.type.getUsedConstants ++ more do
        if tracked d && !seen.contains d then todo := d :: todo
  return (out.qsort (fun a b => a.1.toString < b.1.toString)).map (·.2)

elab "#pin_deps " ns:ident* : command => liftTermElabM do
  let cs ← ns.mapM fun n => realizeGlobalConstNoOverloadWithInfo n
  let lines ← pinDeps cs
  logInfo ("PIN-DEPS-BEGIN\n" ++ "\n".intercalate lines.toList ++ "\nPIN-DEPS-END")

elab "#pin_sanity " n:ident : command => liftTermElabM do
  let c ← realizeGlobalConstNoOverloadWithInfo n
  let some (.defnInfo d) := (← getEnv).find? c | throwError "{c} is not a definition"
  forallTelescope d.value fun xs _ => do
    let mut nh := 0
    for x in xs do
      if ← isProp (← inferType x) then nh := nh + 1
    let r ← if nh == 0 then pure none else anyCloses (mkConst ``False) (← falseTactics)
    let verdict := match r with
      | none => "consistent"
      | some "?" => "unknown (timeout)"
      | some t => s!"VACUOUS (False by {t})"
    logInfo s!"PIN-SANITY {c} hyps={nh} {verdict}"

end HarnessTools
