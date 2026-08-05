# First faithfulness review — worksheet

**Status: NOT REVIEWED.** Nothing below is filled in, and nothing below may be
filled in by an agent. `faithfulness` is the one human-only axis
(`.claude/decisions/ADR-0005-trust-axes.md:56` — *"`faithfulness` is
human-only"*), and `faithfulness: agent_drafted` was deliberately rejected there.
This file exists so the reviewer reads and judges instead of gathering.

Prepared from the built environment — every Lean type below is the ELABORATED
type as Lean sees it, `pp.proofs true`, not a transcription of the source.

Two passes, both 2026-08-05:

| pass | commit | entries |
|---|---|---|
| first | `bcd6939` | the four then-existing bindings |
| second | `6ce0d0f` | the three `AutIsometry.lean` bindings, below |

The second pass also **rewrote `actStabAut`'s author note in place**, because
the note the first pass quoted has since been corrected in the source. It said
*"no metric is constructed here, so isometry is not proved"*; the anchor has
carried `slicingDist` all along. A worksheet quoting a superseded note would
put the reviewer's judgement against a claim its author no longer makes. The
Lean type of `actStabAut` is byte-identical across both passes — only the note
moved.

## The question, per entry

> Does the Lean declaration state what the paper's sentence says?

Not "does it typecheck" — the issue cites TheoremGraph's statement-only
experiment where **22/24 outputs typechecked and 5/24 were semantically
faithful**. Typechecking is not fidelity, and the whole reason this axis is
human-only is that nothing mechanical distinguishes the two.

Answer with one of `adequate` / `divergent` / `inadequate` / `inconclusive`,
and if the verdict is `divergent` or `inadequate` the schema **requires** at
least one written divergence.

## What is blocked, and why the verdicts cannot be recorded yet

A `review/1.0` record requires `reviewed_env_digest`, and an
`environment/1.0` record requires 14 fields including `emitter_version`,
`lake_version` and per-package resolved revs. **This repo has no emitter**
(contract-v1-e4 / #4), so there is nothing to attest against and a review
recorded now would carry a digest matching no environment.

`reviewed_statement_digest` is blocked by the same thing: it is a Merkle node
over `type_pp` plus topic-local dependency digests, which is the emitter's
output.

So the sequence is: **judge now on this worksheet, record when the emitter
lands.** The judgements below do not expire — they are about a statement pair,
and `statement_stable` exists precisely to detect it if the Lean side moves
underneath them.

`reviewed_quote_sha256` IS available today and is given per entry, because it
comes from the registry rather than from the environment.

---

## `CategoryTheory.Triangulated.mapEquiv_isLocallyFinite`

**cites** `bridgeland2007.def-5.7` — claimed **`noClaim`** (related, but no implication claimed)
**frontier:** none declared

**Author's note on the binding:**
> Bound to the locally-finite DEFINITION because this theorem is what preserves it, not what states it. no_claim is the honest relation: a transport result neither states the definition nor is implied by it.

### The paper says

> Definition 5.7. A slicing $\mathcal{P}$ of a triangulated category $\operatorname{\mathcal{D}}$ is locally-finite if there exists a real number $\eta>0$ such that for all $t\in\mathbb{R}$ the quasi-abelian category $\mathcal{P}((t-\eta,t+\eta))\subset\operatorname{\mathcal{D}}$ is of finite length. A stability condition $(Z,\mathcal{P})$ is locally-finite if the corresponding slicing $\mathcal{P}$ is.

`reviewed_quote_sha256` = `829028bbb714a19f051deb50c8034eb77bda316b29f11f7811d0abecb4f9aa46`

### Lean says

```lean
∀ {C : Type u} [inst : CategoryTheory.Category.{w, u} C] [inst_1 : CategoryTheory.Limits.HasZeroObject C]
  [inst_2 : CategoryTheory.HasShift C ℤ] [inst_3 : CategoryTheory.Preadditive C]
  [inst_4 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] [inst_5 : CategoryTheory.Pretriangulated C]
  [inst_6 : CategoryTheory.IsTriangulated C] (Φ : C ≌ C) [inst_7 : Φ.functor.Additive] [inst_8 : Φ.inverse.Additive]
  [inst_9 : Φ.functor.CommShift ℤ] [inst_10 : Φ.inverse.CommShift ℤ] [inst_11 : Φ.functor.IsTriangulated]
  [inst_12 : Φ.inverse.IsTriangulated] (s : CategoryTheory.Triangulated.Slicing C),
  CategoryTheory.Triangulated.Slicing.IsLocallyFinite C s →
    CategoryTheory.Triangulated.Slicing.IsLocallyFinite C (s.mapEquiv Φ)
```

### Reviewer

| field | value |
|---|---|
| `faithfulness` | ☐ adequate ☐ divergent ☐ inadequate ☐ inconclusive |
| `relation_confirmed` | ☐ exact ☐ equivalent ☐ specialization ☐ one_way ☐ no_claim ☐ disputed |
| `divergences[]` | *(required if divergent/inadequate)* |
| `reviewer` / `reviewed_at` | |

**Is the author's claimed relation `noClaim` right?** It is a claim, not a
measurement, and confirming it is half of this review.

---

## `BridgelandStabLean.GroupAction.gltildeSlicingMulAction`

**cites** `bridgeland2007.lem-8.2` — claimed **`noClaim`** (related, but no implication claimed)
**frontier:** none declared

**Author's note on the binding:**
> A COMPONENT of the Lemma 8.2 action, not a weaker version of it: the paper states an action on Stab(D), and says nothing about GLTilde acting on slicings alone. Neither statement implies the other, so no_claim rather than one_way.

### The paper says

> Lemma 8.2. The generalised metric space $\operatorname{Stab}(\operatorname{\mathcal{D}})$ carries a right action of the group ${\tilde{\operatorname{GL^{+}}}}(2,\mathbb{R})$, the universal covering space of $\operatorname{GL^{+}}(2,\mathbb{R})$, and a left action by isometries of the group $\operatorname{Aut}(\operatorname{\mathcal{D}})$ of exact autoequivalences of $\operatorname{\mathcal{D}}$. These two actions commute.

`reviewed_quote_sha256` = `a82c3230040fd724ffad1d6655c190b00b99321d3fc1ab5eb74dafdfe8c38d1f`

### Lean says

```lean
(C : Type u) →
  [inst : CategoryTheory.Category.{v, u} C] →
    [inst_1 : CategoryTheory.Limits.HasZeroObject C] →
      [inst_2 : CategoryTheory.HasShift C ℤ] →
        [inst_3 : CategoryTheory.Preadditive C] →
          [inst_4 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] →
            [inst_5 : CategoryTheory.Pretriangulated C] →
              MulAction BridgelandStabLean.GroupAction.GLTilde (CategoryTheory.Triangulated.Slicing C)
```

### Reviewer

| field | value |
|---|---|
| `faithfulness` | ☐ adequate ☐ divergent ☐ inadequate ☐ inconclusive |
| `relation_confirmed` | ☐ exact ☐ equivalent ☐ specialization ☐ one_way ☐ no_claim ☐ disputed |
| `divergences[]` | *(required if divergent/inadequate)* |
| `reviewer` / `reviewed_at` | |

**Is the author's claimed relation `noClaim` right?** It is a claim, not a
measurement, and confirming it is half of this review.

---

## `BridgelandStabLean.GroupAction.stabMulAction`

**cites** `bridgeland2007.lem-8.2` — claimed **`oneWay`** (the cited statement implies this one, not conversely)
**frontier left open:** `gltilde-universal-cover`

**Author's note on the binding:**
> Lemma 8.2 names GLTilde as the universal covering space of GL+(2,R). Here it is a group of compatible pairs, proved to be a group and nothing more -- the covering-space facts are absent from Mathlib at this revision. The paper's statement implies this one; not conversely.

### The paper says

> Lemma 8.2. The generalised metric space $\operatorname{Stab}(\operatorname{\mathcal{D}})$ carries a right action of the group ${\tilde{\operatorname{GL^{+}}}}(2,\mathbb{R})$, the universal covering space of $\operatorname{GL^{+}}(2,\mathbb{R})$, and a left action by isometries of the group $\operatorname{Aut}(\operatorname{\mathcal{D}})$ of exact autoequivalences of $\operatorname{\mathcal{D}}$. These two actions commute.

`reviewed_quote_sha256` = `a82c3230040fd724ffad1d6655c190b00b99321d3fc1ab5eb74dafdfe8c38d1f`

### Lean says

```lean
(C : Type u) →
  [inst : CategoryTheory.Category.{w, u} C] →
    [inst_1 : CategoryTheory.Limits.HasZeroObject C] →
      [inst_2 : CategoryTheory.HasShift C ℤ] →
        [inst_3 : CategoryTheory.Preadditive C] →
          [inst_4 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] →
            [inst_5 : CategoryTheory.Pretriangulated C] →
              [inst_6 : CategoryTheory.IsTriangulated C] →
                {Λ : Type u'} →
                  [inst_7 : AddCommGroup Λ] →
                    (v : CategoryTheory.Triangulated.K₀ C →+ Λ) →
                      MulAction BridgelandStabLean.GroupAction.GLTilde
                        (CategoryTheory.Triangulated.StabilityCondition.WithClassMap C v)
```

### Reviewer

| field | value |
|---|---|
| `faithfulness` | ☐ adequate ☐ divergent ☐ inadequate ☐ inconclusive |
| `relation_confirmed` | ☐ exact ☐ equivalent ☐ specialization ☐ one_way ☐ no_claim ☐ disputed |
| `divergences[]` | *(required if divergent/inadequate)* |
| `reviewer` / `reviewed_at` | |

**Is the author's claimed relation `oneWay` right?** It is a claim, not a
measurement, and confirming it is half of this review.

---

## `CategoryTheory.Triangulated.actStabAut`

**cites** `bridgeland2007.lem-8.2` — claimed **`oneWay`** (the cited statement implies this one, not conversely)
**frontier:** none declared

**Author's note on the binding** *(rewritten at `6ce0d0f`; see the header)*:
> The Aut half of Lemma 8.2, and weaker than it in two stated ways. The paper says Aut(D) acts by ISOMETRIES; that clause is not proved. What IS proved is actStabAut_slicingDist (AutIsometry.lean): this map preserves the anchor's slicingDist, which carries the two phase discrepancies of Bridgeland's d and omits the mass ratio |log(m2/m1)|. That omission is not closable at this pin -- the anchor defines no mass function. And the acting object is a PAIR (Phi, lam) rather than an autoequivalence, so this is not a MulAction -- AutQuot groups the Phi's alone, which suffices for slicings but not once a class lattice is in play.

### The paper says

> Lemma 8.2. The generalised metric space $\operatorname{Stab}(\operatorname{\mathcal{D}})$ carries a right action of the group ${\tilde{\operatorname{GL^{+}}}}(2,\mathbb{R})$, the universal covering space of $\operatorname{GL^{+}}(2,\mathbb{R})$, and a left action by isometries of the group $\operatorname{Aut}(\operatorname{\mathcal{D}})$ of exact autoequivalences of $\operatorname{\mathcal{D}}$. These two actions commute.

`reviewed_quote_sha256` = `a82c3230040fd724ffad1d6655c190b00b99321d3fc1ab5eb74dafdfe8c38d1f`

### Lean says

```lean
{C : Type u} →
  [inst : CategoryTheory.Category.{w, u} C] →
    [inst_1 : CategoryTheory.Limits.HasZeroObject C] →
      [inst_2 : CategoryTheory.HasShift C ℤ] →
        [inst_3 : CategoryTheory.Preadditive C] →
          [inst_4 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] →
            [inst_5 : CategoryTheory.Pretriangulated C] →
              [inst_6 : CategoryTheory.IsTriangulated C] →
                (Φ : C ≌ C) →
                  [Φ.functor.Additive] →
                    [inst_8 : Φ.inverse.Additive] →
                      [inst_9 : Φ.functor.CommShift ℤ] →
                        [inst_10 : Φ.inverse.CommShift ℤ] →
                          [Φ.functor.IsTriangulated] →
                            [inst_12 : Φ.inverse.IsTriangulated] →
                              {Λ : Type u'} →
                                [inst_13 : AddCommGroup Λ] →
                                  (v : CategoryTheory.Triangulated.K₀ C →+ Λ) →
                                    (lam : Λ →+ Λ) →
                                      (∀ (x : CategoryTheory.Triangulated.K₀ C),
                                          v ((CategoryTheory.Triangulated.K₀.mapF Φ.inverse) x) = lam (v x)) →
                                        CategoryTheory.Triangulated.StabilityCondition.WithClassMap C v →
                                          CategoryTheory.Triangulated.StabilityCondition.WithClassMap C v
```

### Reviewer

| field | value |
|---|---|
| `faithfulness` | ☐ adequate ☐ divergent ☐ inadequate ☐ inconclusive |
| `relation_confirmed` | ☐ exact ☐ equivalent ☐ specialization ☐ one_way ☐ no_claim ☐ disputed |
| `divergences[]` | *(required if divergent/inadequate)* |
| `reviewer` / `reviewed_at` | |

**Is the author's claimed relation `oneWay` right?** It is a claim, not a
measurement, and confirming it is half of this review.

---

## The three `AutIsometry.lean` bindings — read this first

All three cite the same sentence, and the same question decides all three, so
it is stated once here rather than three times below.

Each proves that the action preserves **`slicingDist`**, which is the *anchor's*
function, not the paper's. Bridgeland's `d` is a supremum of **three**
quantities per nonzero object:

```
d(σ₁,σ₂) = sup_{0≠E} { |φ⁻₂(E) − φ⁻₁(E)| , |φ⁺₂(E) − φ⁺₁(E)| , |log(m₂(E)/m₁(E))| }
```

`slicingDist` is the first two and drops the third. The dropped term is the
only one that reads the central charge, hence the only one an autoequivalence
could move — `actStabAut` sends `Z` to `Z ∘ lam`. **The anchor defines no mass
function**, so the third term is not expressible at this pin and no proof here
touches it.

**The question for the reviewer is therefore not "is the proof right".** It is
whether binding a theorem about a *two-term* distance to a sentence about a
*three-term* one is `no_claim` (the author's call) or `disputed`. The author's
argument for `no_claim`: a supremum of three being preserved does not give that
each term is, so the paper does not imply this — and this plainly does not
imply the paper. Both directions fail, which is what `no_claim` means.

The counter-argument the reviewer should weigh: a binding is a pointer, and a
reader who follows this one lands on a sentence containing the word
*isometries* while the Lean says something materially weaker. Whether the
author's note is sufficient mitigation is a judgement, and it is exactly the
kind ADR-0005 reserves for a human.

---

## `CategoryTheory.Triangulated.mapEquiv_slicingDist`

**cites** `bridgeland2007.lem-8.2` — claimed **`noClaim`** (related, but no implication claimed)
**frontier:** none declared

**Author's note on the binding:**
> The ISOMETRY clause of Lemma 8.2, for a DIFFERENT distance, so neither statement implies the other. The paper's d is a sup of THREE quantities; the anchor's slicingDist carries the two phase discrepancies and omits |log(m2/m1)|, the mass ratio -- the only term that sees the central charge, hence the only one Z-composed-with-lam could move. A sup of three being preserved does not give that each term is, so isometry for d does NOT imply this; and preserving slicingDist plainly does not imply isometry for d. Separately, slicingDist is a distance on Slicing C, not on Stab(D). The anchor defines no mass function, so the omitted term is not expressible at this pin.

### The paper says

> Lemma 8.2. The generalised metric space $\operatorname{Stab}(\operatorname{\mathcal{D}})$ carries a right action of the group ${\tilde{\operatorname{GL^{+}}}}(2,\mathbb{R})$, the universal covering space of $\operatorname{GL^{+}}(2,\mathbb{R})$, and a left action by isometries of the group $\operatorname{Aut}(\operatorname{\mathcal{D}})$ of exact autoequivalences of $\operatorname{\mathcal{D}}$. These two actions commute.

`reviewed_quote_sha256` = `a82c3230040fd724ffad1d6655c190b00b99321d3fc1ab5eb74dafdfe8c38d1f`

### Lean says

```lean
∀ {C : Type u} [inst : CategoryTheory.Category.{w, u} C] [inst_1 : CategoryTheory.Limits.HasZeroObject C]
  [inst_2 : CategoryTheory.HasShift C ℤ] [inst_3 : CategoryTheory.Preadditive C]
  [inst_4 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] [inst_5 : CategoryTheory.Pretriangulated C]
  (Φ : C ≌ C) [inst_6 : Φ.functor.Additive] [inst_7 : Φ.inverse.Additive] [inst_8 : Φ.functor.CommShift ℤ]
  [inst_9 : Φ.inverse.CommShift ℤ] [inst_10 : Φ.functor.IsTriangulated] [inst_11 : Φ.inverse.IsTriangulated]
  (s₁ s₂ : CategoryTheory.Triangulated.Slicing C),
  CategoryTheory.Triangulated.slicingDist C (s₁.mapEquiv Φ) (s₂.mapEquiv Φ) =
    CategoryTheory.Triangulated.slicingDist C s₁ s₂
```

**Second divergence, independent of the distance:** the carrier is
`Slicing C`, not `Stab(D)`. The paper's sentence is about the space of
stability conditions; this one is about bare slicings, with no central charge
in the statement at all.

### Reviewer

| field | value |
|---|---|
| `faithfulness` | ☐ adequate ☐ divergent ☐ inadequate ☐ inconclusive |
| `relation_confirmed` | ☐ exact ☐ equivalent ☐ specialization ☐ one_way ☐ no_claim ☐ disputed |
| `divergences[]` | *(required if divergent/inadequate)* |
| `reviewer` / `reviewed_at` | |

**Is the author's claimed relation `noClaim` right?** It is a claim, not a
measurement, and confirming it is half of this review.

---

## `CategoryTheory.Triangulated.actStabAut_slicingDist`

**cites** `bridgeland2007.lem-8.2` — claimed **`noClaim`** (related, but no implication claimed)
**frontier:** none declared

**Author's note on the binding:**
> Same non-implication as mapEquiv_slicingDist: the distance is the anchor's slicingDist, not Bridgeland's d, and d omits nothing while slicingDist omits the mass ratio. What this adds over that theorem is only the carrier -- the statement is now about stability conditions rather than bare slicings, matching the paper's Stab(D). It is still not the paper's isometry claim.

### The paper says

> Lemma 8.2. The generalised metric space $\operatorname{Stab}(\operatorname{\mathcal{D}})$ carries a right action of the group ${\tilde{\operatorname{GL^{+}}}}(2,\mathbb{R})$, the universal covering space of $\operatorname{GL^{+}}(2,\mathbb{R})$, and a left action by isometries of the group $\operatorname{Aut}(\operatorname{\mathcal{D}})$ of exact autoequivalences of $\operatorname{\mathcal{D}}$. These two actions commute.

`reviewed_quote_sha256` = `a82c3230040fd724ffad1d6655c190b00b99321d3fc1ab5eb74dafdfe8c38d1f`

### Lean says

```lean
∀ {C : Type u} [inst : CategoryTheory.Category.{w, u} C] [inst_1 : CategoryTheory.Limits.HasZeroObject C]
  [inst_2 : CategoryTheory.HasShift C ℤ] [inst_3 : CategoryTheory.Preadditive C]
  [inst_4 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] [inst_5 : CategoryTheory.Pretriangulated C]
  [inst_6 : CategoryTheory.IsTriangulated C] (Φ : C ≌ C) [inst_7 : Φ.functor.Additive] [inst_8 : Φ.inverse.Additive]
  [inst_9 : Φ.functor.CommShift ℤ] [inst_10 : Φ.inverse.CommShift ℤ] [inst_11 : Φ.functor.IsTriangulated]
  [inst_12 : Φ.inverse.IsTriangulated] {Λ : Type u'} [inst_13 : AddCommGroup Λ]
  (v : CategoryTheory.Triangulated.K₀ C →+ Λ) (lam : Λ →+ Λ)
  (hlam : ∀ (x : CategoryTheory.Triangulated.K₀ C), v ((CategoryTheory.Triangulated.K₀.mapF Φ.inverse) x) = lam (v x))
  (σ τ : CategoryTheory.Triangulated.StabilityCondition.WithClassMap C v),
  CategoryTheory.Triangulated.slicingDist C (CategoryTheory.Triangulated.actStabAut Φ v lam hlam σ).slicing
      (CategoryTheory.Triangulated.actStabAut Φ v lam hlam τ).slicing =
    CategoryTheory.Triangulated.slicingDist C σ.slicing τ.slicing
```

**Worth noticing while reading the type:** `lam` appears in the hypotheses and
in neither side of the conclusion. That is not sloppiness — `lam` moves only
the central charge, and `slicingDist` does not read the central charge. It is
the same fact as the missing mass term, visible in the signature.

### Reviewer

| field | value |
|---|---|
| `faithfulness` | ☐ adequate ☐ divergent ☐ inadequate ☐ inconclusive |
| `relation_confirmed` | ☐ exact ☐ equivalent ☐ specialization ☐ one_way ☐ no_claim ☐ disputed |
| `divergences[]` | *(required if divergent/inadequate)* |
| `reviewer` / `reviewed_at` | |

**Is the author's claimed relation `noClaim` right?** It is a claim, not a
measurement, and confirming it is half of this review.

---

## `CategoryTheory.Triangulated.AutPairQuot_smul_slicingDist`

**cites** `bridgeland2007.lem-8.2` — claimed **`noClaim`** (related, but no implication claimed)
**frontier:** none declared

**Author's note on the binding:**
> The closest this repo gets to 'Aut(D) acts by isometries', and still not it, for two independent reasons already recorded elsewhere in this repo. (1) The distance is slicingDist, not Bridgeland's d -- see mapEquiv_slicingDist's note; neither statement implies the other. (2) AutPairQuot v is NOT Aut(D): its elements are pairs (Phi, lam), and the forgetful map to AutQuot C is proved neither injective nor surjective. Cite this as 'the group of autoequivalences carrying a compatible class-lattice automorphism preserves the phase distance'.

### The paper says

> Lemma 8.2. The generalised metric space $\operatorname{Stab}(\operatorname{\mathcal{D}})$ carries a right action of the group ${\tilde{\operatorname{GL^{+}}}}(2,\mathbb{R})$, the universal covering space of $\operatorname{GL^{+}}(2,\mathbb{R})$, and a left action by isometries of the group $\operatorname{Aut}(\operatorname{\mathcal{D}})$ of exact autoequivalences of $\operatorname{\mathcal{D}}$. These two actions commute.

`reviewed_quote_sha256` = `a82c3230040fd724ffad1d6655c190b00b99321d3fc1ab5eb74dafdfe8c38d1f`

### Lean says

```lean
∀ {C : Type u} [inst : CategoryTheory.Category.{w, u} C] [inst_1 : CategoryTheory.Limits.HasZeroObject C]
  [inst_2 : CategoryTheory.HasShift C ℤ] [inst_3 : CategoryTheory.Preadditive C]
  [inst_4 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] [inst_5 : CategoryTheory.Pretriangulated C]
  [inst_6 : CategoryTheory.IsTriangulated C] {Λ : Type u'} [inst_7 : AddCommGroup Λ]
  (v : CategoryTheory.Triangulated.K₀ C →+ Λ) (g : BridgelandStabLean.GroupAction.AutPairQuot v)
  (σ τ : CategoryTheory.Triangulated.StabilityCondition.WithClassMap C v),
  CategoryTheory.Triangulated.slicingDist C (g • σ).slicing (g • τ).slicing =
    CategoryTheory.Triangulated.slicingDist C σ.slicing τ.slicing
```

**This entry carries a second divergence the other two do not.** The paper's
acting group is `Aut(D)`; the Lean's is `AutPairQuot v`, whose elements are
pairs. The repo's own `CLAUDE.md` and `formalization.yaml` both state that
`AutPairQuot v` is not `Aut(D)`, and that the forgetful map to `AutQuot C` is
proved neither injective nor surjective. A reviewer judging *this* entry is
judging two gaps at once, and may want to record them as separate
`divergences[]` items rather than one.

### Reviewer

| field | value |
|---|---|
| `faithfulness` | ☐ adequate ☐ divergent ☐ inadequate ☐ inconclusive |
| `relation_confirmed` | ☐ exact ☐ equivalent ☐ specialization ☐ one_way ☐ no_claim ☐ disputed |
| `divergences[]` | *(required if divergent/inadequate)* |
| `reviewer` / `reviewed_at` | |

**Is the author's claimed relation `noClaim` right?** It is a claim, not a
measurement, and confirming it is half of this review.

---

## When the emitter lands

```sh
mfc join --declarations attest/declarations.json \
         --registry registry/bridgeland2007.json \
         --review attest/review.json \
         --environment attest/environment.json
```

Without `--environment` the review columns read `not_run`, deliberately: a
verdict cannot be shown to be about the build in hand, so it does not claim to
be. `J-01` will catch a review whose `reviewed_statement_digest` matches no
declaration, and `J-03` refuses to merge two reviews of one statement that
disagree.

## Coverage, stated rather than implied

Reviewing these entries makes `human_review` non-`none` **for these entries
only**. At `6ce0d0f` the repo carries **198** audited declarations and the
registry 8 entries, against a notebook of 146 papers / 15,280 chunks. **7** of
the 198 carry a `@[cites]` binding at all, and those 7 are what this worksheet
covers. A repo-level `human_review` reading anything but `none` while that is
true is the collapse ADR-0005 forbids.

**Six of the seven point at the same registry entry, `lem-8.2`** — everything
except `mapEquiv_isLocallyFinite`. That is not duplication to be trimmed. The
sentence makes four separate assertions, and the six split across three of
them:

| assertion in Lemma 8.2 | bound by |
|---|---|
| `Stab(D)` carries a right `G̃L⁺(2,ℝ)` action | `gltildeSlicingMulAction`, `stabMulAction` |
| `Aut(D)` acts on the left | `actStabAut` |
| that left action is **by isometries** | `mapEquiv_slicingDist`, `actStabAut_slicingDist`, `AutPairQuot_smul_slicingDist` |
| the two actions **commute** | *nothing* |

**Nothing in this repo binds to the fourth.** The actions are not proved to
commute and no declaration claims they are. A reviewer working entry by entry
will not notice that, because an absent binding has no worksheet section — so
it is stated here.
