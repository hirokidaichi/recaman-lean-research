import Recaman.PrefixKeySourceBudget
import Recaman.FreePrefixCounterexample
import Lean.Util.FoldConsts
import Lean.Elab.Command

open Lean Elab Command
namespace ResearchDependencyAudit

private def isProject (n : Name) : Bool :=
  n.toString.startsWith "Recaman." || n.toString.startsWith "_private.Recaman."

partial def collect (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n::rest =>
    if seen.contains n then collect env rest seen else
      let seen := seen.insert n
      match env.find? n with
      | none => collect env rest seen
      | some c =>
        let deps := c.getUsedConstantsAsSet.toList.filter isProject
        collect env (deps++rest) seen

run_cmd do
  let env ← getEnv
  for target in [`Recaman.ThreeRunFreeGap.three_run_free_gap_int,
      `Recaman.PrefixKeySourceBudget.actual_local_source_prefix_A_of_key] do
    let names := (collect env [target] {}).toList.map Name.toString
    logInfo s!"DEPENDENCY_TARGET={target}"
    logInfo (Json.compress (toJson names))

end ResearchDependencyAudit
