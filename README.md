# ElCruz - Proof of God

A modal argument for the existence of a necessary being. Created on 15 November 2026.

**Status:** the deduction is valid and has been machine-checked. The argument rests on one possibility premise (P) that can be neither proven nor refuted. As a proof of God, it is worth exactly as much as P is.

## Definitions

- **Contingent:** exists in some possible world, but not in all of them.
- **Necessary:** exists in every possible world.
- **Explainer:** an entity that explains why there are contingent things rather than none.

## Axioms

They only fix what "to explain" means.

- **A1.** What explains, exists: an explainer exists in the world in which it explains.
- **A2.** An explainer is not contingent. If it were, it would be one of the things whose existence it is supposed to explain, and the explanation would presuppose what it sets out to explain.

## Premise

- **P.** It is possible that an explainer exists; that is, in at least one possible world, some entity explains the existence of contingent things.

## Theorem

There exists, in the actual world, a necessary being that is an explainer in at least one possible world.

## Proof

1. By P, there is a possible world *w* with an explainer *e*.
2. By A1, *e* exists in *w*.
3. By A2, *e* is not contingent. Since it exists in *w*, the only way for it not to be contingent is to exist in every possible world. Therefore *e* is necessary.
4. The actual world is one of those worlds, so *e* exists here. ∎

## Modal notation

S5 logic. □ = necessarily, ◇ = possibly, E(y) = y exists, X(y) = y is an explainer.

```
A1  □∀y (X(y) → E(y))
A2  □∀y (X(y) → ¬(E(y) ∧ ◇¬E(y)))
P   ◇∃y X(y)
T   ∃y (□E(y) ∧ ◇X(y))
```

## Verification

The program `elcruz_check.py` (same folder, no dependencies) enumerates every small model and tests each one:

```bash
python3 elcruz_check.py
```

Result of the run on 15 November 2026: 1,062,644 models in S5, of which 12,051 satisfy A1, A2 and P.

- **Validity:** no counterexample. The search is a complete proof, not a sample: refuting the theorem only requires the witnesses demanded by the premises and by the negation of the conclusion (one individual, three worlds), so any larger counterexample would contain one of that size.
- **No modal collapse:** there is a model that satisfies A1, A2 and P and still contains contingent things.
- **No redundant part:** remove A1, A2 or P and a counterexample appears.
- **Dependence on S5:** without symmetry between worlds, the explainer may fail to exist in the actual world. Without transitivity, it may exist here without being necessary. Steps 3 and 4 only hold if "every possible world" is the same set seen from any world.
- **Rival premise:** P and "a world with no necessary being is possible" are never true together, and each is consistent on its own.

## What the model does not assume

- It does not assume that every contingent thing has an explanation. It is enough that a single explanation be possible.
- It does not forbid infinite chains of dependence. The argument does not use chains.
- To explain is not to make necessary, so contingent things remain contingent.

## Points of attack

1. **P is equivalent to the conclusion.** P looks modest, but together with A2 it says "a necessary being is possible", and in S5 that already is "a necessary being exists". The rival premise leads to the opposite conclusion, and ElCruz does not break the tie. It only fixes the price of denying P: holding that explaining the existence of contingent things is impossible in every world, not merely absent in ours.
2. **A2.** A critic can say that, in an infinite chain, each contingent thing is explained by the previous one and that this is enough. The usual reply is that this explains each member, but not why there is any member at all. The dispute remains open.
3. **Explanation by an entity.** P assumes that what explains is an entity. If the explanation could be an abstract principle, with no entity at all, the argument does not reach it.
4. **Scope.** The theorem does not say that this being explains our universe, only that it exists and that it could explain one. Nor does it say that it has a mind, a will or goodness. If "God" means only "a necessary being capable of explaining the contingent", ElCruz proves God from P. If it means the God of the religions, it does not.
