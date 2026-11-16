/-!
# ElCruz

Formal proofs for the ElCruz argument in Lean 4, with no external libraries.

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

/-! ## Vocabulary -/

/-- x exists in w but is missing from some world possible from w. -/
def Contingent (x : M.Thing) (w : M.World) : Prop :=
  M.exist x w ∧ ∃ v, M.acc w v ∧ ¬ M.exist x v

/-- x exists in every world possible from w. -/
def Necessary (x : M.Thing) (w : M.World) : Prop :=
  ∀ v, M.acc w v → M.exist x v

/-- m is a root of w: w has contingent things and m takes part in explaining each one. -/
def Root (m : M.Thing) (w : M.World) : Prop :=
  (∃ x, M.Contingent x w) ∧ ∀ x, M.Contingent x w → M.part m x w

/-- c is the only contingent thing of w. -/
def Lone (c : M.Thing) (w : M.World) : Prop :=
  M.Contingent c w ∧ ∀ x, M.Contingent x w → x = c

/-- c is an origin of w: every other contingent thing of w has c in its explanation. -/
def Origin (c : M.Thing) (w : M.World) : Prop :=
  M.Contingent c w ∧ ∀ x, M.Contingent x w → x = c ∨ M.part c x w

/-- y is a contingent thing of w that takes part in the explanation of c. -/
def ContingentExplainer (w : M.World) (y c : M.Thing) : Prop :=
  M.Contingent y w ∧ M.part y c w

/-! ## Axioms -/

/-- F1: whatever explains, and whatever is explained, exists. -/
def F1 : Prop :=
  ∀ m x w, M.part m x w → M.exist m w ∧ M.exist x w

/-- F2: nothing contingent takes part in the explanation of its own existence. -/
def F2 : Prop :=
  ∀ x w, M.Contingent x w → ¬ M.part x x w

/-- F3: explanation passes through intermediaries. -/
def F3 : Prop :=
  ∀ a b c w, M.part a b w → M.part b c w → M.part a c w

/-! ## 1. The map: brute fact, endless chain, or necessary being (uses F1 only) -/

/-- In a world with contingent things, if every contingent thing has some explanation and
the chain of contingent explainers always ends, then a necessary being takes part in the
explanation of some contingent thing. -/
theorem trilemma (h1 : M.F1) {w : M.World}
    (hsome : ∃ x, M.Contingent x w)
    (hnobrute : ∀ c, M.Contingent c w → ∃ m, M.part m c w)
    (hends : WellFounded (M.ContingentExplainer w)) :
    ∃ m c, M.Contingent c w ∧ M.part m c w ∧ M.exist m w ∧ M.Necessary m w := by
  apply Classical.byContradiction
  intro hno
  have key : ∀ c, ¬ M.Contingent c w := fun c =>
    hends.induction (C := fun c => ¬ M.Contingent c w) c (fun c ih hc => by
      obtain ⟨m, hm⟩ := hnobrute c hc
      have hex : M.exist m w := (h1 m c w hm).1
      have hmc : M.Contingent m w := by
        refine ⟨hex, ?_⟩
        apply Classical.byContradiction
        intro hall
        apply hno
        refine ⟨m, c, hc, hm, hex, fun v hv => ?_⟩
        apply Classical.byContradiction
        intro hne
        exact hall ⟨v, hv, hne⟩
      exact ih m ⟨hmc, hm⟩ hmc)
  obtain ⟨x, hx⟩ := hsome
  exact key x hx

/-! ## 2. The argument (uses F1 and F2) -/

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

/-- The conclusion gives the premise back, so the two stand or fall together. -/
theorem premise_of_conclusion {a : M.World}
    (hT : ∃ m, M.exist m a ∧ M.Necessary m a ∧ ∃ w, M.acc a w ∧ M.Root m w) :
    ∃ w, M.acc a w ∧ ∃ m, M.Root m w := by
  obtain ⟨m, _, _, w, haw, hr⟩ := hT
  exact ⟨w, haw, m, hr⟩

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

/-- If a root is possible, every possible world contains a necessary being (S5). -/
theorem no_world_without_necessary (symm : ∀ u v, M.acc u v → M.acc v u)
    (trans : ∀ u v t, M.acc u v → M.acc v t → M.acc u t)
    (h1 : M.F1) (h2 : M.F2) {a : M.World}
    (hP : ∃ w, M.acc a w ∧ ∃ m, M.Root m w) :
    ∀ v, M.acc a v → ∃ x, M.exist x v ∧ M.Necessary x v := by
  obtain ⟨m, _, hm, _⟩ := M.elcruz symm trans h1 h2 hP
  have hnec : ∀ v, M.acc a v → M.exist m v := hm
  intro v hav
  exact ⟨m, hnec v hav, fun u hvu => hnec u (trans a v u hav hvu)⟩

/-! ## 3. The simplest case: a lone contingent thing (uses F1 and F2) -/

/-- Whatever takes part in the explanation of a lone contingent thing is a root. -/
theorem lone_root {c m : M.Thing} {w : M.World}
    (hl : M.Lone c w) (hm : M.part m c w) : M.Root m w :=
  ⟨⟨c, hl.1⟩, fun x hx => (by rw [hl.2 x hx]; exact hm)⟩

/-- So it exists in that world and is necessary there. -/
theorem lone_necessary (h1 : M.F1) (h2 : M.F2) {c m : M.Thing} {w : M.World}
    (hl : M.Lone c w) (hm : M.part m c w) : M.exist m w ∧ M.Necessary m w :=
  M.root_necessary h1 h2 (M.lone_root hl hm)

/-- If a lone contingent thing can have an explanation, there could not have been nothing:
every possible world contains something (S5). -/
theorem lone_explanation_excludes_nothing (symm : ∀ u v, M.acc u v → M.acc v u)
    (trans : ∀ u v t, M.acc u v → M.acc v t → M.acc u t)
    (h1 : M.F1) (h2 : M.F2) {a : M.World}
    (hA : ∃ w, M.acc a w ∧ ∃ c m, M.Lone c w ∧ M.part m c w) :
    ∀ v, M.acc a v → ∃ x, M.exist x v := by
  obtain ⟨w, haw, c, m, hl, hm⟩ := hA
  intro v hav
  obtain ⟨x, hx, _⟩ :=
    M.no_world_without_necessary symm trans h1 h2 ⟨w, haw, m, M.lone_root hl hm⟩ v hav
  exact ⟨x, hx⟩

/-! ## 4. What transitivity adds (uses F3) -/

/-- Nothing contingent takes part in the explanation of a root. -/
theorem root_independent (h2 : M.F2) (h3 : M.F3) {r c : M.Thing} {w : M.World}
    (hr : M.Root r w) (hc : M.Contingent c w) : ¬ M.part c r w :=
  fun hcr => h2 c w hc (h3 c r c w hcr (hr.2 c hc))

/-- A chain of contingent explainers leads from a to b. -/
inductive Chain (w : M.World) : M.Thing → M.Thing → Prop where
  | step {a b : M.Thing} : M.ContingentExplainer w a b → Chain w a b
  | more {a b c : M.Thing} : Chain w a b → M.ContingentExplainer w b c → Chain w a c

/-- There are no loops: no chain of contingent explainers leads from a thing back to itself. -/
theorem no_loops (h2 : M.F2) (h3 : M.F3) {w : M.World} {x : M.Thing} : ¬ M.Chain w x x := by
  have key : ∀ a b, M.Chain w a b → M.Contingent a w ∧ M.part a b w := by
    intro a b h
    induction h with
    | step hab => exact hab
    | more _ hbc ih => exact ⟨ih.1, h3 _ _ _ _ ih.2 hbc.2⟩
  intro hxx
  exact h2 x w (key x x hxx).1 (key x x hxx).2

/-- Whatever takes part in the explanation of an origin is a root. -/
theorem origin_root (h3 : M.F3) {c m : M.Thing} {w : M.World}
    (ho : M.Origin c w) (hm : M.part m c w) : M.Root m w :=
  ⟨⟨c, ho.1⟩, fun x hx =>
    (ho.2 x hx).elim (fun h => (by rw [h]; exact hm)) (fun h => h3 m c x w hm h)⟩

/-- A world with an origin: either the origin is a brute fact, or a necessary being takes part
in the explanation of every contingent thing. Holds for any acc. -/
theorem dichotomy (h1 : M.F1) (h2 : M.F2) (h3 : M.F3) {c : M.Thing} {w : M.World}
    (ho : M.Origin c w) :
    (∀ m, ¬ M.part m c w) ∨ ∃ m, M.exist m w ∧ M.Necessary m w ∧ M.Root m w := by
  apply Classical.byCases (p := ∃ m, M.part m c w)
  · intro hex
    obtain ⟨m, hm⟩ := hex
    have hr : M.Root m w := M.origin_root h3 ho hm
    exact Or.inr ⟨m, (M.root_necessary h1 h2 hr).1, (M.root_necessary h1 h2 hr).2, hr⟩
  · intro hno
    exact Or.inl (fun m hm => hno ⟨m, hm⟩)

/-- The two cases exclude each other: a world with a brute origin has no root. -/
theorem brute_origin_has_no_root {c : M.Thing} {w : M.World} (ho : M.Origin c w)
    (hb : ∀ m, ¬ M.part m c w) : ¬ ∃ m, M.Root m w :=
  fun hroot => hroot.elim (fun m hr => hb m (hr.2 c ho.1))

end Model

/-! ## Two explicit models -/

/-- Two worlds, two things. The thing true exists in both worlds and takes part in the
explanation of the thing false, which exists only in the world true. -/
def demo : Model where
  World := Bool
  Thing := Bool
  acc := fun (_ _ : Bool) => True
  exist := fun (x w : Bool) => x = true ∨ w = true
  part := fun (m x w : Bool) => m = true ∧ x = false ∧ w = true

theorem demo_F1 : demo.F1 := by
  intro m x w h
  have h' : m = true ∧ x = false ∧ w = true := h
  exact ⟨Or.inl h'.1, Or.inr h'.2.2⟩

theorem demo_F2 : demo.F2 :=
  fun (x w : Bool) _ (h : x = true ∧ x = false ∧ w = true) =>
    absurd (h.1.symm.trans h.2.1) (by decide)

theorem demo_F3 : demo.F3 :=
  fun (a b c w : Bool) (hab : a = true ∧ b = false ∧ w = true)
      (hbc : b = true ∧ c = false ∧ w = true) =>
    absurd (hbc.1.symm.trans hab.2.1) (by decide)

theorem demo_contingent : demo.Contingent false true := by
  refine ⟨Or.inr rfl, false, trivial, ?_⟩
  intro h
  have h' : false = true ∨ false = true := h
  exact h'.elim (fun e => absurd e (by decide)) (fun e => absurd e (by decide))

theorem demo_root : demo.Root true true := by
  refine ⟨⟨false, demo_contingent⟩, fun (x : Bool) hx => ?_⟩
  have hx' : (x = true ∨ true = true) ∧ ∃ v : Bool, True ∧ ¬ (x = true ∨ v = true) := hx
  obtain ⟨_, v, _, hv⟩ := hx'
  have hxf : x = false := by
    cases x
    · rfl
    · exact absurd (Or.inl rfl) hv
  exact ⟨rfl, hxf, rfl⟩

/-- The axioms and the premise P hold together in a world that has a contingent thing. -/
theorem demo_premise : ∃ w, demo.acc true w ∧ ∃ m, demo.Root m w :=
  ⟨true, trivial, true, demo_root⟩

/-- Infinitely many contingent things in the world true, each explained by all the later
ones. The world false is empty. -/
def regress : Model where
  World := Bool
  Thing := Nat
  acc := fun (_ _ : Bool) => True
  exist := fun (_ : Nat) (w : Bool) => w = true
  part := fun (m x : Nat) (w : Bool) => w = true ∧ x < m

theorem regress_F1 : regress.F1 :=
  fun (m x : Nat) (w : Bool) (h : w = true ∧ x < m) => ⟨h.1, h.1⟩

theorem regress_F2 : regress.F2 :=
  fun (x : Nat) (w : Bool) _ (h : w = true ∧ x < x) => Nat.lt_irrefl x h.2

theorem regress_F3 : regress.F3 :=
  fun (a b c : Nat) (w : Bool) (hab : w = true ∧ b < a) (hbc : w = true ∧ c < b) =>
    ⟨hab.1, Nat.lt_trans hbc.2 hab.2⟩

theorem regress_all_contingent (x : Nat) : regress.Contingent x true := by
  refine ⟨rfl, false, trivial, ?_⟩
  intro h
  have h' : false = true := h
  exact absurd h' (by decide)

/-- Nothing is brute: every thing has an explanation. -/
theorem regress_no_brute (c : Nat) : ∃ m, regress.part m c true :=
  ⟨c + 1, rfl, Nat.lt_succ_self c⟩

/-- Nothing is necessary. -/
theorem regress_nothing_necessary (x : Nat) : ¬ regress.Necessary x true := by
  intro h
  have hall : ∀ v : Bool, True → v = true := h
  exact absurd (hall false trivial) (by decide)

/-- The chain of contingent explainers never ends. -/
theorem regress_endless : ¬ WellFounded (regress.ContingentExplainer true) := by
  intro hwf
  exact hwf.induction (C := fun _ => False) (0 : Nat) (fun (x : Nat) ih =>
    ih (x + 1) ⟨regress_all_contingent (x + 1), rfl, Nat.lt_succ_self x⟩)

/-- Depends on every result above, so printing its axioms shows nothing was left unproved. -/
theorem all_results : True := by
  have _a := @Model.trilemma
  have _b := @Model.elcruz
  have _c := @Model.exists_actually
  have _d := @Model.premise_of_conclusion
  have _e := @Model.actual
  have _f := @Model.no_collapse
  have _g := @Model.lone_necessary
  have _h := @Model.lone_explanation_excludes_nothing
  have _i := @Model.root_independent
  have _j := @Model.no_loops
  have _k := @Model.dichotomy
  have _l := @Model.brute_origin_has_no_root
  have _m := demo_F1
  have _n := demo_F2
  have _o := demo_F3
  have _p := demo_premise
  have _q := regress_F1
  have _r := regress_F2
  have _s := regress_F3
  have _t := regress_no_brute
  have _u := regress_nothing_necessary
  have _v := regress_endless
  trivial

#print axioms Model.trilemma
#print axioms Model.elcruz
#print axioms Model.dichotomy
#print axioms all_results
