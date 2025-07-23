import LeanDisco.miniF2F_valid
import Lean

/--
`extract_no_sorry.lean`

A small Lean 4 metaprogram that walks through the current environment and
prints every theorem/definition whose value *does not* contain a `sorry`.

To use it:
1. `lean --run extract_no_sorry.lean` **after** your file has been compiled, or
2. Add `#eval printNoSorryProofs` at the bottom of your working file.

The script filters out proofs that contain synthetic or explicit `sorry`
terms by checking `Expr.hasSorry`.  It pretty‑prints the surviving proof
terms using Lean’s `PrettyPrinter`.
-/-/

open Lean Meta

/-- Return `true` iff the expression contains *any* kind of `sorry` marker. -/
private def hasSorryExpr (e : Expr) : Bool :=
  e.hasSorry

/-- Collect every declaration in the environment whose value has no `sorry`. -/
private def collectNoSorryProofs : MetaM (List (Name × Expr)) := do
  let env ← getEnv
  env.constants.foldlM (init := ([] : List (Name × Expr))) fun acc (n, decl) => do
    match decl with
    | ConstantInfo.thmInfo info =>
        if !hasSorryExpr info.value then
          pure <| (n, info.value) :: acc
        else
          pure acc
    | ConstantInfo.defnInfo info =>
        if info.safety == DefinitionSafety.safe && !hasSorryExpr info.value then
          pure <| (n, info.value) :: acc
        else
          pure acc
    | _ => pure acc

/-- Pretty‑print every proof/definition that passed the filter. -/
def printNoSorryProofs : MetaM Unit := do
  let proofs ← collectNoSorryProofs
  for (n, pr) in proofs.reverse do -- reverse to keep original order
    let fmt ← PrettyPrinter.ppExpr pr
    IO.println s!"\n--- {n} ---\n{fmt}"

/-- Uncomment the line below to run from inside an editor.
#eval printNoSorryProofs
-/
