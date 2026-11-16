# ElCruz - Proof of God

A modal argument for the existence of a necessary being. Version 2, 15 November 2026.

**Status:** the deduction is valid and has been formally verified in Lean 4. The argument rests on one possibility premise (P) that can be neither proven nor refuted. As a proof of God, it is worth exactly as much as P is.

**What it establishes:** a coherence constraint. Given two modest axioms about explanation, you cannot hold that a common root of all contingent things is *possible* and deny that a necessary being *exists*.

## Definitions

- **Contingent:** exists in some possible world, but not in all of them.
- **Necessary:** exists in every possible world.
- **Takes part in the explanation of x:** is among the things the existence of x depends on, directly or through intermediaries.
- **Root of a world:** something that takes part in the explanation of the existence of every contingent thing of that world. The world must have at least one contingent thing.

A root does not have to explain anything by itself. Other things may take part in each explanation too.

## Axioms

- **F1 (factivity).** Whatever explains exists, and so does whatever is explained: if m takes part in the explanation of x in a world, both exist in that world.
- **F2 (no circularity).** Nothing contingent takes part in the explanation of its own existence.

## Premise

- **P.** A root is possible: in at least one possible world, something takes part in the explanation of every contingent thing.

## Theorem

Every possible root is a necessary being. So if P holds, there exists, in the actual world, a necessary being that is a root of at least one possible world.

## Proof

1. By P, there is a possible world *w* with contingent things and a root *r*.
2. *r* takes part in the explanation of some contingent thing of *w*; by F1, *r* exists in *w*.
3. *r* is not contingent. If it were, it would be one of the contingent things of *w* and would take part in the explanation of its own existence, which F2 forbids.
4. *r* exists in *w* and is not contingent, so it exists in every possible world: *r* is necessary.
5. The actual world is one of those worlds, so *r* exists here. ∎

Step 3 was an axiom in version 1. It is now derived.

## Corollaries

- **No modal collapse.** The root does not make necessary what it helps explain: for each contingent thing *c* there is a possible world where the root exists and takes no part in the explanation of *c*, because *c* is not there.
- **Actual-world version.** If the actual world has a root, that root is a necessary being that takes part in the explanation of every contingent thing here. This version does not depend on S5, but its premise is stronger: it claims a root for our world, not merely a possible one.

## Modal notation

S5 logic. □ = necessarily, ◇ = possibly, E(x) = x exists, Part(m, x) = m takes part in the explanation of the existence of x.

```
Cont(x)   :=  E(x) ∧ ◇¬E(x)
Root(m)   :=  ∃x Cont(x) ∧ ∀x (Cont(x) → Part(m, x))

F1  □∀m∀x (Part(m, x) → E(m) ∧ E(x))
F2  □∀x ¬(Cont(x) ∧ Part(x, x))
P   ◇∃m Root(m)
T   ∃m (□E(m) ∧ ◇Root(m))
```

## Verification

**Formal proof.** `ElCruz.lean` proves the theorem and both corollaries in Lean 4, with no external libraries. It was checked on 15 November 2026 with Lean 4.36.0-rc2 on the official online editor (live.lean-lang.org): no errors, no `sorry`, and the only axioms used are Lean's three standard ones (`propext`, `Classical.choice`, `Quot.sound`), that is, ordinary classical logic. A Lean proof holds for every model, finite or infinite. To check it yourself, paste the file into https://live.lean-lang.org or run `lean ElCruz.lean`.

The file states each theorem over an arbitrary accessibility relation between worlds, so it shows exactly what each result requires. The actual-world version and the no-collapse corollary require nothing. Existing in the actual world requires symmetry. Being necessary in the actual world requires symmetry and transitivity, both of which hold in S5.

**Exhaustive search.** `elcruz_check.py` (no dependencies) enumerates small models to establish what a proof does not: that the axioms are consistent, that none is redundant, and where the argument stops working.

```bash
python3 elcruz_check.py
```

Result of the run on 15 November 2026 (266,644 models in S5, of which 704 satisfy F1, F2 and P; 45,184 models in other modal logics):

- **Consistency:** there is a model of F1, F2 and P that still contains contingent things.
- **No redundant part:** remove F1, F2 or P and a counterexample appears.
- **Rival premise:** P and "a world with no necessary being is possible" are never true together, and each is consistent on its own.
- **Dependence on S5:** explicit counterexamples show that, without symmetry between worlds, the possible root may fail to exist in the actual world, and that, without transitivity, it may exist here without being necessary.
- **Cross-check:** the theorem and both corollaries have no counterexample among the models enumerated.

## What the model does not assume

- It does not assume that every contingent thing has an explanation. One possible root is enough.
- It does not forbid infinite chains of explanation.
- It does not assume a single explainer of everything. A root only has to take part in each explanation.
- To explain is not to make necessary, so contingent things remain contingent (this is the first corollary).

## Points of attack

1. **P is equivalent to the conclusion.** Given F1 and F2, in S5, "a root is possible" and "a necessary being that could be a root exists" stand or fall together. The rival premise, "a world with no necessary being is possible", leads to the opposite conclusion, and ElCruz does not break the tie. It only fixes the price of denying P: holding that in no possible world do the contingent things share a common root.
2. **F2.** It rules out explanatory loops, where a contingent thing is part of the explanation of itself, directly or in a circle. Whoever accepts closed causal loops or a self-caused universe rejects F2.
3. **S5.** It is the standard logic for metaphysical possibility, but it is a choice. Steps 4 and 5 only hold if "every possible world" is the same set seen from any world. The actual-world version does not need this.
4. **Scope.** The theorem does not say how many necessary beings there are, nor what they are: the domain covers anything that exists, so the root could be a concrete being or an abstract principle. It does not say the root has a mind, a will or goodness. In its modal form it does not say the root explains our universe, only that it exists and could be a root. If "God" means only "a necessary being that everything contingent could trace back to", ElCruz proves God from P. If it means the God of the religions, it does not.

## Changes from version 1

- The contested axiom A2 ("an explainer is not contingent") is gone. Its content is now step 3 of the proof, derived from F2, which only forbids circular explanation.
- The premise asks for less. Version 1 needed a possible entity that explains by itself why there are contingent things. Version 2 needs a possible common root, which only has to take part in each explanation.
- More is proved: the absence of modal collapse is now a theorem rather than an example, and there is an actual-world version that does not depend on S5.
- Verification is a formal proof in Lean instead of an argument about small models.
