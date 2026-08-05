# First faithfulness review — worksheet

**Status: NOT REVIEWED.** Nothing below is filled in, and nothing below may be
filled in by an agent. `faithfulness` is the one human-only axis
(`.claude/decisions/ADR-0005-trust-axes.md:56` — *"`faithfulness` is
human-only"*), and `faithfulness: agent_drafted` was deliberately rejected there.
This file exists so the reviewer reads and judges instead of gathering.

Prepared 2026-08-05 against `bcd6939`, from the built environment — every Lean
type below is the ELABORATED type as Lean sees it, not a transcription of the
source.

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

**Author's note on the binding:**
> The Aut half of Lemma 8.2, and weaker than it in two stated ways. The paper says Aut(D) acts by ISOMETRIES; no metric is constructed here, so isometry is not proved. And the acting object is a PAIR (Phi, lam) rather than an autoequivalence, so this is not a MulAction -- AutQuot groups the Phi's alone, which suffices for slicings but not once a class lattice is in play.

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
only**. The repo carries 189 audited declarations and the registry 8 entries
against a notebook of 146 papers / 15,280 chunks. A repo-level `human_review`
reading anything but `none` while that is true is the collapse ADR-0005 forbids.
