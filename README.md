# ElCruz - Proof of God

A modal argument for the existence of a necessary being. Version 3, 16 November 2026.

**Status:** every result below is formally verified in Lean 4. The argument for a necessary being still rests on one possibility premise (P) that can be neither proven nor refuted. As a proof of God, it is worth exactly as much as P is.

**What it establishes:**

1. The explanation of contingent things ends in a brute fact, never ends, or reaches a necessary being. There is no fourth option.
2. You cannot hold both that a lone contingent thing could have an explanation and that there could have been nothing at all.

## Vocabulary

- **Contingent:** exists in some possible world, but not in all of them.
- **Necessary:** exists in every possible world.
- **Takes part in the explanation of x:** is among the things the existence of x depends on.
- **Brute fact:** a contingent thing with nothing at all in its explanation.
- **Root of a world:** something that takes part in the explanation of the existence of every contingent thing of that world. The world must have at least one contingent thing.

A root does not have to explain anything by itself. Other things may take part in each explanation too.

## Axioms

- **F1 (factivity).** Whatever explains exists, and so does whatever is explained: if m takes part in the explanation of x in a world, both exist in that world.
- **F2 (no circularity).** Nothing contingent takes part in the explanation of its own existence.
- **F3 (transitivity).** Explanation passes through intermediaries: if a takes part in the explanation of b, and b in the explanation of c, then a takes part in the explanation of c.

Section 1 uses only F1. Sections 2 and 3 use F1 and F2. Only section 4 uses F3.

## 1. The map: three options, no fourth

Take any world that has contingent things. Pick one of them and ask what explains it; then ask the same about whatever you find. At least one of these holds:

1. **Brute fact.** Some contingent thing has no explanation at all.
2. **Endless chain.** The chain of contingent explainers never ends: an infinite regress, or a loop.
3. **Necessary being.** Some contingent thing has a necessary being among its explainers.

This needs no premise about what is possible, and it holds for the actual world. It does not say which option is true. It says there is no fourth.

F2 and F3 together exclude loops, so with all three axioms the endless chain can only be an infinite regress. The axioms do not exclude that: the Lean file contains a model with an infinite regress, no brute fact and no necessary being.

## 2. The argument

**Premise P.** A root is possible: in at least one possible world, something takes part in the explanation of every contingent thing.

**Theorem.** Every possible root is a necessary being. So if P holds, there exists, in the actual world, a necessary being that is a root of at least one possible world.

**Proof.**

1. By P, there is a possible world *w* with contingent things and a root *r*.
2. *r* takes part in the explanation of some contingent thing of *w*; by F1, *r* exists in *w*.
3. *r* is not contingent. If it were, it would be one of the contingent things of *w* and would take part in the explanation of its own existence, which F2 forbids.
4. *r* exists in *w* and is not contingent, so it exists in every possible world: *r* is necessary.
5. The actual world is one of those worlds, so *r* exists here. ∎

**Corollaries.**

- **No modal collapse.** The root does not make necessary what it helps explain: for each contingent thing *c* there is a possible world where the root exists and takes no part in the explanation of *c*, because *c* is not there.
- **No empty world.** If P holds, every possible world contains a necessary being. There could not have been nothing.
- **Actual-world version.** If the actual world has a root, that root is a necessary being that takes part in the explanation of every contingent thing here. This version does not depend on S5, but its premise is stronger: it claims a root for our world, not merely a possible one.

## 3. The simplest way P can be true

Take a possible world with a single contingent thing. If anything at all takes part in its explanation, that thing is a root, and therefore a necessary being. So P follows from very little:

> **A.** A lone contingent thing could have an explanation.

By the second corollary, A is incompatible with:

> **B.** There could have been nothing at all.

Both sound plausible. Given F1 and F2, in S5, at most one of them is true. This is the real content of ElCruz: it does not tell you which one to give up, only that you must give up one.

Each choice has a price. Keeping A means accepting a necessary being and rejecting B. Rejecting A means holding that, in every possible world, a contingent thing that exists alone is necessarily a brute fact.

## 4. What transitivity adds

With F3, two more results hold.

- **Independence.** Nothing contingent takes part in the explanation of a root. Everything contingent traces back to the root, and the root traces back to nothing contingent.
- **Single origin.** Call a contingent thing an *origin* of its world if every other contingent thing of that world has it in its explanation. In a world with an origin, exactly one of two things is true: the origin is a brute fact, or a necessary being takes part in the explanation of every contingent thing of that world.

The single-origin result needs no possibility premise and no S5, so it applies to the actual world. If everything contingent in our universe traces back to one initial state, then either that state has no explanation whatsoever, or there is a necessary being behind everything contingent.

## Modal notation

S5 logic. □ = necessarily, ◇ = possibly, E(x) = x exists, Part(m, x) = m takes part in the explanation of the existence of x.

```
Cont(x)   :=  E(x) ∧ ◇¬E(x)
Root(m)   :=  ∃x Cont(x) ∧ ∀x (Cont(x) → Part(m, x))
Lone(c)   :=  Cont(c) ∧ ∀x (Cont(x) → x = c)

F1  □∀m∀x (Part(m, x) → E(m) ∧ E(x))
F2  □∀x ¬(Cont(x) ∧ Part(x, x))
F3  □∀a∀b∀c (Part(a, b) ∧ Part(b, c) → Part(a, c))

P   ◇∃m Root(m)
T   ∃m (□E(m) ∧ ◇Root(m))
A   ◇∃c∃m (Lone(c) ∧ Part(m, c))
B   ◇¬∃x E(x)

F1, F2, P  ⊢  T
F1, F2, A  ⊢  ¬B
```

## Verification

**Formal proofs.** `ElCruz.lean` proves every result above in Lean 4, with no external libraries. It also contains two explicit models: one where the three axioms and P hold together in a world with contingent things, and one where the three axioms hold in a world with an infinite regress, no brute fact and no necessary being. It was checked on 15 November 2026 with Lean 4.36.0-rc2 on the official online editor (live.lean-lang.org): no errors, no `sorry`, and the only axioms used are Lean's three standard ones (`propext`, `Classical.choice`, `Quot.sound`), that is, ordinary classical logic. A Lean proof holds for every model, finite or infinite. To check it yourself, paste the file into https://live.lean-lang.org or run `lean ElCruz.lean`.

The file states each theorem over an arbitrary accessibility relation between worlds, so it shows exactly what each result requires. The map, the lone-thing result, independence, the single-origin result, the actual-world version and the no-collapse corollary require nothing. Existing in the actual world requires symmetry. Being necessary in the actual world requires symmetry and transitivity, both of which hold in S5. The absence of empty worlds is proved under the same two conditions.

**Exhaustive search.** `elcruz_check.py` (no dependencies) enumerates small models to establish what the proofs do not: that no axiom is redundant and where each result stops working. It also re-checks every result independently of Lean.

```bash
python3 elcruz_check.py
```

Result of the run on 16 November 2026 (325,208 models in S5, of which 19,904 satisfy F1, F2 and P; 45,184 models in other modal logics):

- **No redundant part:** remove F1, F2 or P and the theorem of section 2 has a counterexample; remove F3 and both results of section 4 have counterexamples.
- **All three options of the map occur:** there are worlds whose only option is a brute fact, worlds whose only option is a loop, and worlds whose only option is a necessary being.
- **Rival premise:** P and "a world with no necessary being is possible" are never true together, and each is consistent on its own.
- **Dependence on S5:** explicit counterexamples show that, without symmetry between worlds, the possible root may fail to exist in the actual world, and that, without transitivity, it may exist here without being necessary.
- **Cross-check:** no result has a counterexample among the models enumerated.

## What the model does not assume

- It does not assume that every contingent thing has an explanation. Brute facts are allowed.
- It does not forbid infinite chains of explanation.
- It does not assume a single explainer of everything. A root only has to take part in each explanation.
- To explain is not to make necessary, so contingent things remain contingent.

## Points of attack

1. **P is equivalent to the conclusion.** Given F1 and F2, in S5, "a root is possible" and "a necessary being that could be a root exists" stand or fall together. The rival premise, "a world with no necessary being is possible", leads to the opposite conclusion, and ElCruz does not break the tie. Section 3 only states the price of each side.
2. **F2.** It forbids a contingent thing taking part in its own explanation. Whoever accepts a contingent thing that causes itself rejects F2.
3. **F3.** It is used only in section 4. Together with F2 it rules out closed loops of explanation, so whoever accepts causal loops must reject F3 or F2. Without F3, sections 1 to 3 stand unchanged.
4. **S5.** It is the standard logic for metaphysical possibility, but it is a choice. Steps 4 and 5 of the proof only hold if "every possible world" is the same set seen from any world. Sections 1 and 4 and the actual-world version do not need this.
5. **Scope.** The theorem does not say how many necessary beings there are, nor what they are: the domain covers anything that exists, so the root could be a concrete being or an abstract principle. It does not say the root has a mind, a will or goodness. Since the root exists even in worlds where the things it helps explain do not, its existence alone does not settle what it explains; whether that link is chance or choice is beyond the theorem. In its modal form the argument does not say the root explains our universe, only that it exists and could be a root. If "God" means only "a necessary being that everything contingent could trace back to", ElCruz proves God from P. If it means the God of the religions, it does not.

## Interpretive note: a higher-dimensional being

A common picture treats God as a higher-dimensional being, outside our four-dimensional spacetime, who sees and handles time the way we handle a sheet of paper. ElCruz does not use this picture as a premise, for three reasons:

- It explains how such a being would act, not that it exists.
- A being that needs a dimension in order to exist depends on it. If dimensions, time and gravity are contingent (there could have been a different number of dimensions and different laws), then, by section 4, nothing of that kind takes part in the explanation of a root. Such a being would be a powerful creature, not the root, and the three options of section 1 would apply to it again.
- Extra dimensions are a physics hypothesis with no experimental evidence so far.

As an analogy the picture is useful: the root stands to time as we stand to the sheet of paper. This fits the theorem. Something that exists in every possible world also exists in worlds without time or space, if such worlds are possible, so it cannot depend on time or space in order to exist.

## Changes from version 2

- New section 1: a map of the options that needs no possibility premise.
- New section 3: the premise in its simplest form, and the clash between A and B.
- New axiom F3 and section 4: independence of the root and the single-origin result.
- New corollary: if P holds, no possible world is empty.
- The Lean file now also proves that the axioms and P are consistent and that infinite regress is not excluded.
