#!/usr/bin/env python3
"""Exhaustive small-model checks for the ElCruz argument; notation follows README.md."""
import sys
from itertools import product


class Model:
    def __init__(self, nD, nW, E, part, actual=0, R=None):
        self.D, self.W = range(nD), range(nW)
        self.E, self.part, self.a, self.R = E, part, actual, R

    def acc(self, w, v):
        # R is None means S5: every world sees every world.
        return self.R is None or self.R[w, v]

    def cont(self, x, w):
        return self.E[x, w] and any(self.acc(w, v) and not self.E[x, v] for v in self.W)

    def nec(self, x, w):
        return all(self.E[x, v] for v in self.W if self.acc(w, v))

    def root(self, m, w):
        cs = [x for x in self.D if self.cont(x, w)]
        return bool(cs) and all(self.part[m, x, w] for x in cs)

    def poss_root(self, m):
        return any(self.acc(self.a, w) and self.root(m, w) for w in self.W)

    def F1(self):
        return all(
            self.E[m, w] and self.E[x, w] for (m, x, w), holds in self.part.items() if holds
        )

    def F2(self):
        return not any(self.cont(x, w) and self.part[x, x, w] for x in self.D for w in self.W)

    def P(self):
        return any(self.poss_root(m) for m in self.D)

    def T(self):
        return any(
            self.E[m, self.a] and self.nec(m, self.a) and self.poss_root(m) for m in self.D
        )

    def T_exist(self):
        return any(self.E[m, self.a] and self.poss_root(m) for m in self.D)

    def rival(self):
        return any(
            self.acc(self.a, w)
            and not any(self.E[m, w] and self.nec(m, w) for m in self.D)
            for w in self.W
        )

    def actual_version(self):
        return all(
            self.E[m, self.a] and self.nec(m, self.a) for m in self.D if self.root(m, self.a)
        )

    def no_collapse(self):
        return all(
            any(self.acc(w, v) and self.E[m, v] and not self.part[m, c, v] for v in self.W)
            for w in self.W
            for m in self.D
            if self.root(m, w)
            for c in self.D
            if self.cont(c, w)
        )

    def contingent_in_actual(self):
        return any(self.cont(x, self.a) for x in self.D)

    def show(self):
        out = [f"    worlds {list(self.W)}, actual world = {self.a}"]
        if self.R is not None:
            arrows = [f"{w}->{v}" for w in self.W for v in self.W if w != v and self.R[w, v]]
            out.append("    accessibility (besides w->w): " + (", ".join(arrows) or "none"))
        for x in self.D:
            out.append(f"    thing {x}: exists in {[w for w in self.W if self.E[x, w]]}")
        parts = [
            f"{m} in the explanation of {x} (world {w})"
            for (m, x, w), holds in self.part.items()
            if holds
        ]
        out.append("    takes part: " + ("; ".join(parts) or "nothing"))
        return "\n".join(out)


def interps(nD, nW):
    e_keys = [(x, w) for x in range(nD) for w in range(nW)]
    p_keys = [(m, x, w) for m in range(nD) for x in range(nD) for w in range(nW)]
    for eb in product((False, True), repeat=len(e_keys)):
        E = dict(zip(e_keys, eb))
        for pb in product((False, True), repeat=len(p_keys)):
            yield E, dict(zip(p_keys, pb))


def frames(nW):
    off = [(w, v) for w in range(nW) for v in range(nW) if w != v]
    for bits in product((False, True), repeat=len(off)):
        R = {(w, w): True for w in range(nW)}
        R.update(zip(off, bits))
        yield R


def is_sym(R, nW):
    return all(R[w, v] == R[v, w] for w in range(nW) for v in range(nW))


def is_trans(R, nW):
    rng = range(nW)
    return all(not (R[w, v] and R[v, u]) or R[w, u] for w in rng for v in rng for u in rng)


failures = []


def expect(label, ok, model=None):
    print(f"[{'OK' if ok else 'FAILED'}] {label}" + (f"\n{model.show()}" if model else ""))
    if not ok:
        failures.append(label)


def run_s5():
    sizes = [(1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3)]
    total = premises = counter = p_and_rival = bad_actual = bad_collapse = 0
    wit = {}
    for nD, nW in sizes:
        for E, part in interps(nD, nW):
            total += 1
            m = Model(nD, nW, E, part)
            f1, f2, p = m.F1(), m.F2(), m.P()
            if f1 and f2:
                if not m.no_collapse():
                    bad_collapse += 1
                for a in m.W:
                    m.a = a
                    if not m.actual_version():
                        bad_actual += 1
                m.a = 0
            if f1 and f2 and p:
                premises += 1
                if not m.T():
                    counter += 1
                    wit.setdefault("counter", m)
                if m.rival():
                    p_and_rival += 1
                if "contingency" not in wit:
                    for a in m.W:
                        m.a = a
                        if m.contingent_in_actual():
                            wit["contingency"] = m
                            break
                    else:
                        m.a = 0
            elif f2 and p and not f1:
                if "no_F1" not in wit and not m.T():
                    wit["no_F1"] = m
            elif f1 and p and not f2:
                if "no_F2" not in wit and not m.T():
                    wit["no_F2"] = m
            elif f1 and f2 and not p:
                if "no_P" not in wit and not m.T():
                    wit["no_P"] = m
                if m.rival():
                    wit.setdefault("rival_without_P", m)
                else:
                    wit.setdefault("neither", m)

    print(f"S5: {total} models enumerated, {premises} satisfy F1, F2 and P.\n")
    expect(
        f"1. Main theorem on small models: F1, F2, P => T ({counter} counterexamples)",
        counter == 0,
        wit.get("counter"),
    )
    expect(
        "2. Consistency: a model of F1, F2, P with a contingent thing in the actual world",
        "contingency" in wit,
        wit.get("contingency"),
    )
    for key, name in (("no_F1", "F1"), ("no_F2", "F2"), ("no_P", "P")):
        expect(f"3. Independence: without {name} there is a counterexample", key in wit, wit.get(key))
    expect(
        f"4a. P and the rival premise never hold together ({p_and_rival} models with both)",
        p_and_rival == 0,
    )
    expect(
        "4b. The rival premise without P is consistent (the opposite side also has a model)",
        "rival_without_P" in wit,
        wit.get("rival_without_P"),
    )
    expect(
        "4c. Neither P nor the rival premise is also consistent",
        "neither" in wit,
        wit.get("neither"),
    )
    expect(f"5. No modal collapse on small models ({bad_collapse} counterexamples)", bad_collapse == 0)
    expect(f"6. Actual-world version on small models ({bad_actual} counterexamples)", bad_actual == 0)


def build(nD, nW, exists, parts, actual, arrows):
    E = {(x, w): (x, w) in exists for x in range(nD) for w in range(nW)}
    part = {
        (m, x, w): (m, x, w) in parts
        for m in range(nD)
        for x in range(nD)
        for w in range(nW)
    }
    R = {(w, v): w == v or (w, v) in arrows for w in range(nW) for v in range(nW)}
    return Model(nD, nW, E, part, actual, R)


# Thing 0 is a root of world 1 (it helps explain thing 1, which is missing from world 2).
NO_SYMMETRY = build(2, 3, {(0, 1), (0, 2), (1, 1)}, {(0, 1, 1)}, 0, {(0, 1), (1, 2)})
NO_TRANSITIVITY = build(
    2, 3, {(0, 0), (0, 1), (1, 1)}, {(0, 1, 1)}, 0, {(0, 1), (1, 0), (0, 2), (2, 0)}
)


def run_frames():
    sizes = [(1, 2), (1, 3), (2, 2)]
    total = bad_actual = bad_collapse = b_exist_counter = s5_counter = 0
    for nD, nW in sizes:
        for R in frames(nW):
            sym, trans = is_sym(R, nW), is_trans(R, nW)
            kind = "S5" if sym and trans else "B" if sym else "T"
            for E, part in interps(nD, nW):
                for a in range(nW):
                    total += 1
                    m = Model(nD, nW, E, part, a, R)
                    if not (m.F1() and m.F2()):
                        continue
                    if not m.actual_version():
                        bad_actual += 1
                    if not m.no_collapse():
                        bad_collapse += 1
                    if not m.P():
                        continue
                    if kind in ("B", "S5") and not m.T_exist():
                        b_exist_counter += 1
                    if kind == "S5" and not m.T():
                        s5_counter += 1

    print(f"\nOther modal logics: {total} models enumerated.\n")
    m = NO_SYMMETRY
    expect(
        "7a. Without symmetry between worlds the possible root may not exist in the actual world",
        not is_sym(m.R, 3) and m.F1() and m.F2() and m.P() and not m.T_exist(),
        m,
    )
    expect(
        f"7b. With symmetry (B) it exists in the actual world ({b_exist_counter} counterexamples)",
        b_exist_counter == 0,
    )
    m = NO_TRANSITIVITY
    expect(
        "7c. With symmetry but without transitivity it may not be necessary in the actual world",
        is_sym(m.R, 3)
        and not is_trans(m.R, 3)
        and m.F1()
        and m.F2()
        and m.P()
        and m.T_exist()
        and not m.T(),
        m,
    )
    expect(f"7d. In S5 the main theorem holds ({s5_counter} counterexamples)", s5_counter == 0)
    expect(
        f"8. Actual-world version and no-collapse hold in every frame tried "
        f"({bad_actual} and {bad_collapse} counterexamples)",
        bad_actual == 0 and bad_collapse == 0,
    )


if __name__ == "__main__":
    run_s5()
    run_frames()
    print("\nRESULT:", "all confirmed" if not failures else f"failures: {failures}")
    sys.exit(1 if failures else 0)
