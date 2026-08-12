# Third-party licences

This repository is **MIT** (see [`LICENSE`](../LICENSE)). Two files are not.

## Apache-2.0

`BridgelandStabLean/ForMathlib/CategoryTheory/` contains material vendored from
[`mattrobball/BridgelandStability`](https://github.com/mattrobball/BridgelandStability)
at revision `9e48f23a`, which is Apache-2.0:

| file | vendored from |
|---|---|
| `ObjectProperty/FullSubcategory.lean` | `BridgelandStability/HeartEquivalence/Basic.lean` |
| `Triangulated/TStructure/HeartAbelian.lean` | `BridgelandStability/TStructure/{HeartAbelian}.lean`, `HeartEquivalence/{Basic,H0Functor,H0Homological}.lean` |

Both retain the Apache-2.0 header of their origin. A copy of the licence is at
[`Apache-2.0.txt`](Apache-2.0.txt), as Apache-2.0 §4(a) requires.

**These files are not, and cannot unilaterally be, relicensed to MIT.** Apache-2.0
permits redistribution and use inside an MIT-licensed project provided the notices
survive; it does not permit stripping the licence from someone else's work. The
repository being MIT and these two files being Apache-2.0 is the correct and
compatible arrangement, not an inconsistency to tidy away.

Two routes exist to an all-MIT tree, and only these two:

1. **Re-prove the five constants from Mathlib primitives.** They are small — the
   largest is two hypothesis discharges against Mathlib's own
   `AbelianSubcategory.abelian`. Independently written proofs are original work
   and can be MIT.
2. **Obtain a dual-licence grant** from the copyright holder of the anchor.

Deleting these files once Mathlib carries the declarations — the deletion
conditions in each file header — resolves it as well, and is the outcome the
files are written to expect.
