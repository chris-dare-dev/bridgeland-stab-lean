/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean
import MathFormalContract

/-!
# The emitter, pointed at this repository's library

`lake exe emit --out attest/lean-emission.json` sweeps `Environment.constants`
and calls `Lean.collectAxioms`. **It never parses Lean source**, which is what
makes `set_option maxHeartbeats 400000 in theorem sneaky : False := by sorry`
structurally unable to hide rather than merely caught — there is no text for it
to hide in. The contract package ships a compiled fixture for exactly that
(`testdata/lean/set-option-evasion.lean`).

This complements `scripts/Audit.lean` rather than replacing it. `Audit` prints
`#print axioms` for a hand-maintained list of names, so it fails to *build* when
a name it lists disappears — useful, and orthogonal. It is not a gate: `#print
axioms` prints `[sorryAx]` and exits 0. The emitter is the gate; `emitMain`
returns non-zero when any constant's axiom closure contains `sorryAx`, and it
writes the artifact either way, because the record is most useful exactly when
the build is not clean.

## `leanOptions` is declared here, not observed

Elaboration options are compile flags and are not recorded in the `.olean`, so
the emitter cannot read them back out of the environment; reporting the process
defaults would make the artifact claim a setting the build did not use.

It must therefore mirror the `[leanOptions]` block of `lakefile.toml`
**character for character**, and `mfc lint` fails a mismatch. If you change one,
change the other in the same commit.
-/

def main (args : List String) : IO UInt32 :=
  MathFormalContract.emitMain
    (rootLib := `BridgelandStabLean)
    (leanOptions := [("autoImplicit", .bool false),
                     ("relaxedAutoImplicit", .bool false)])
    args
