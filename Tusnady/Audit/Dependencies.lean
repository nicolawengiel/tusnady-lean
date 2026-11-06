import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-!
Read-only audit support for Lean 4.34.1.

`Lean.collectAxioms` is the public recursive axiom API. Separately, this
walker follows constants in both types and values, including opaque values
and inductive/constructor/recursor dependencies. Missing kernel declarations
are retained explicitly, so callers can fail closed rather than silently
report a truncated dependency list. This metaprogram is not a proof premise.
-/
namespace TusnadyAudit
open Lean

structure DependencyClosure where
  visited : NameSet := {}
  axioms : NameSet := {}
  missing : NameSet := {}

private partial def visit (env : Environment) (descend : Name → Bool)
    (name : Name) : StateM DependencyClosure Unit := do
  if (← get).visited.contains name then return
  modify fun s => { s with visited := s.visited.insert name }
  match env.checked.get.find? name with
  | none => modify fun s => { s with missing := s.missing.insert name }
  | some info =>
    if let .axiomInfo _ := info then
      modify fun s => { s with axioms := s.axioms.insert name }
    if descend name then
      for dependency in info.getUsedConstantsAsSet do
        visit env descend dependency

/-- Complete closure when `descend = fun _ => true`; callers may explicitly
restrict traversal for a separately labelled project-only component report. -/
def collectDependencies (env : Environment) (name : Name)
    (descend : Name → Bool := fun _ => true) : DependencyClosure :=
  ((visit env descend name).run {}).2

end TusnadyAudit
