/-!
# ElCruz

Formal proof of the ElCruz argument in Lean 4, with no external libraries.

Possible worlds are related by an accessibility relation (acc), so every theorem
states exactly which properties of that relation it uses. S5 is the case where
the relation is symmetric and transitive.
-/

structure Model where
  World : Type
  Thing : Type
  /-- acc w v: world v is possible from the point of view of world w. -/
  acc : World → World → Prop
  /-- exist x w: x exists in world w. -/
  exist : Thing → World → Prop
  /-- part m x w: in world w, m takes part in the explanation of the existence of x. -/
  part : Thing → Thing → World → Prop

namespace Model

variable (M : Model)

/-- x exists in w but is missing from some world possible from w. -/
def Contingent (x : M.Thing) (w : M.World) : Prop :=
  M.exist x w ∧ ∃ v, M.acc w v ∧ ¬ M.exist x v

/-- x exists in every world possible from w. -/
def Necessary (x : M.Thing) (w : M.World) : Prop :=
  ∀ v, M.acc w v → M.exist x v

/-- m is a root of w: w has contingent things and m takes part in explaining each one. -/
def Root (m : M.Thing) (w : M.World) : Prop :=
  (∃ x, M.Contingent x w) ∧ ∀ x, M.Contingent x w → M.part m x w

/-- F1: whatever explains, and whatever is explained, exists. -/
def F1 : Prop :=
  ∀ m x w, M.part m x w → M.exist m w ∧ M.exist x w

/-- F2: nothing contingent takes part in the explanation of its own existence. -/
def F2 : Prop :=
  ∀ x w, M.Contingent x w → ¬ M.part x x w

/-- A root is not contingent. This was an axiom (A2) in the first version. -/
theorem root_not_contingent (h2 : M.F2) {m : M.Thing} {w : M.World}
    (hr : M.Root m w) : ¬ M.Contingent m w :=
  fun hc => h2 m w hc (hr.2 m hc)

/-- A root of w exists in w and is necessary there. No property of acc is used. -/
theorem root_necessary (h1 : M.F1) (h2 : M.F2) {m : M.Thing} {w : M.World}
    (hr : M.Root m w) : M.exist m w ∧ M.Necessary m w := by
  obtain ⟨c, hc⟩ := hr.1
  have hex : M.exist m w := (h1 m c w (hr.2 c hc)).1
  refine ⟨hex, fun v hv => ?_⟩
  apply Classical.byContradiction
  intro hne
  exact M.root_not_contingent h2 hr ⟨hex, v, hv, hne⟩

/-- Main theorem (S5). If a root is possible, a necessary being exists in the actual world a. -/
theorem elcruz (symm : ∀ u v, M.acc u v → M.acc v u)
    (trans : ∀ u v t, M.acc u v → M.acc v t → M.acc u t)
    (h1 : M.F1) (h2 : M.F2) {a : M.World}
    (hP : ∃ w, M.acc a w ∧ ∃ m, M.Root m w) :
    ∃ m, M.exist m a ∧ M.Necessary m a ∧ ∃ w, M.acc a w ∧ M.Root m w := by
  obtain ⟨w, haw, m, hr⟩ := hP
  have hnec : ∀ v, M.acc w v → M.exist m v := (M.root_necessary h1 h2 hr).2
  have hwa : M.acc w a := symm a w haw
  exact ⟨m, hnec a hwa, fun v hav => hnec v (trans w a v hwa hav), w, haw, hr⟩

/-- With symmetry alone (logic B) the possible root still exists in the actual world. -/
theorem exists_actually (symm : ∀ u v, M.acc u v → M.acc v u)
    (h1 : M.F1) (h2 : M.F2) {a : M.World}
    (hP : ∃ w, M.acc a w ∧ ∃ m, M.Root m w) :
    ∃ m, M.exist m a ∧ ∃ w, M.acc a w ∧ M.Root m w := by
  obtain ⟨w, haw, m, hr⟩ := hP
  have hnec : ∀ v, M.acc w v → M.exist m v := (M.root_necessary h1 h2 hr).2
  exact ⟨m, hnec a (symm a w haw), w, haw, hr⟩

/-- Actual-world version. If the actual world a has a root, that root is a necessary being
that takes part in explaining every contingent thing in a. Holds for any acc. -/
theorem actual (h1 : M.F1) (h2 : M.F2) {m : M.Thing} {a : M.World} (hr : M.Root m a) :
    M.exist m a ∧ M.Necessary m a ∧ ∀ x, M.Contingent x a → M.part m x a :=
  ⟨(M.root_necessary h1 h2 hr).1, (M.root_necessary h1 h2 hr).2, hr.2⟩

/-- No modal collapse. For each contingent thing c of w there is a possible world where
the root exists and takes no part in explaining c. -/
theorem no_collapse (h1 : M.F1) (h2 : M.F2) {m c : M.Thing} {w : M.World}
    (hr : M.Root m w) (hc : M.Contingent c w) :
    ∃ v, M.acc w v ∧ M.exist m v ∧ ¬ M.part m c v := by
  have hnec : ∀ v, M.acc w v → M.exist m v := (M.root_necessary h1 h2 hr).2
  obtain ⟨_, v, hv, hne⟩ := hc
  exact ⟨v, hv, hnec v hv, fun hp => hne (h1 m c v hp).2⟩

end Model

#print axioms Model.elcruz
#print axioms Model.exists_actually
#print axioms Model.actual
#print axioms Model.no_collapse
