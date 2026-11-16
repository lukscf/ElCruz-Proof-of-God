#!/usr/bin/env python3
"""Exhaustive finite-model check of the ElCruz argument; notation follows README.md."""
import sys
from itertools import product


class Model:
    def __init__(self, nD, nW, E, X, actual, R=None):
        self.D, self.W = range(nD), range(nW)
        self.E, self.X, self.a, self.R = E, X, actual, R

    def acc(self, w, v):
        # R is None means S5: every world sees every world.
        return self.R is None or self.R[w, v]

    def cont(self, d, w):
        return self.E[d, w] and any(self.acc(w, v) and not self.E[d, v] for v in self.W)

    def nec(self, d, w):
        return all(self.E[d, v] for v in self.W if self.acc(w, v))

    def poss_expl(self, d):
        return any(self.acc(self.a, w) and self.X[d, w] for w in self.W)

    def A1(self):
        return all(self.E[d, w] for d in self.D for w in self.W if self.X[d, w])

    def A2(self):
        return not any(self.X[d, w] and self.cont(d, w) for d in self.D for w in self.W)

    def P(self):
        return any(self.poss_expl(d) for d in self.D)

    def T(self):
        return any(
            self.E[d, self.a] and self.nec(d, self.a) and self.poss_expl(d) for d in self.D
        )

    def T_exist(self):
        return any(self.E[d, self.a] and self.poss_expl(d) for d in self.D)

    def rival(self):
        return any(
            self.acc(self.a, w)
            and not any(self.E[d, w] and self.nec(d, w) for d in self.D)
            for w in self.W
        )

    def contingent_in_actual(self):
        return any(self.cont(d, self.a) for d in self.D)

    def show(self):
        out = [f"    worlds {list(self.W)}, actual world = {self.a}"]
        if self.R is not None:
            arrows = [f"{w}->{v}" for w in self.W for v in self.W if w != v and self.R[w, v]]
            out.append("    accessibility (besides w->w): " + (", ".join(arrows) or "none"))
        for d in self.D:
            ex = [w for w in self.W if self.E[d, w]]
            xs = [w for w in self.W if self.X[d, w]]
            out.append(f"    individual {d}: exists in {ex}, explains in {xs}")
        return "\n".join(out)


def interps(nD, nW):
    pairs = [(d, w) for d in range(nD) for w in range(nW)]
    for eb in product((False, True), repeat=len(pairs)):
        E = dict(zip(pairs, eb))
        for xb in product((False, True), repeat=len(pairs)):
            yield E, dict(zip(pairs, xb))


def s5_models(sizes):
    for nD, nW in sizes:
        for E, X in interps(nD, nW):
            for a in range(nW):
                yield Model(nD, nW, E, X, a)


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


def frame_models(sizes):
    for nD, nW in sizes:
        for R in frames(nW):
            sym, trans = is_sym(R, nW), is_trans(R, nW)
            kind = "S5" if sym and trans else "B" if sym else "T"
            for E, X in interps(nD, nW):
                for a in range(nW):
                    yield kind, Model(nD, nW, E, X, a, R)


failures = []


def expect(label, ok, detail=""):
    print(f"[{'OK' if ok else 'FAILED'}] {label}" + (f"\n{detail}" if detail else ""))
    if not ok:
        failures.append(label)


def run_s5():
    sizes = [(d, w) for d in (1, 2) for w in (1, 2, 3, 4)] + [(3, 3)]
    total = premises = counter = p_and_rival = 0
    wit = {}
    for m in s5_models(sizes):
        total += 1
        a1, a2, p = m.A1(), m.A2(), m.P()
        if a1 and a2 and p:
            premises += 1
            if not m.T():
                counter += 1
                wit.setdefault("counter", m)
            if m.rival():
                p_and_rival += 1
            if "contingency" not in wit and m.contingent_in_actual():
                wit["contingency"] = m
        elif a2 and p and not a1:
            if "no_A1" not in wit and not m.T():
                wit["no_A1"] = m
        elif a1 and p and not a2:
            if "no_A2" not in wit and not m.T():
                wit["no_A2"] = m
        elif a1 and a2 and not p:
            if "no_P" not in wit and not m.T():
                wit["no_P"] = m
            if m.rival():
                wit.setdefault("rival_without_P", m)
            else:
                wit.setdefault("neither", m)

    print(f"S5: {total} models enumerated, {premises} satisfy A1, A2 and P.\n")
    expect(
        f"1. Validity: A1, A2, P => T ({counter} counterexamples)",
        counter == 0,
        wit["counter"].show() if "counter" in wit else "",
    )
    expect(
        "2. Consistency without modal collapse: a model of A1, A2, P with a contingent thing",
        "contingency" in wit,
        wit["contingency"].show() if "contingency" in wit else "",
    )
    for key, name in (("no_A1", "A1"), ("no_A2", "A2"), ("no_P", "P")):
        expect(
            f"3. Independence: without {name} there is a counterexample",
            key in wit,
            wit[key].show() if key in wit else "",
        )
    expect(
        f"4a. P and the rival premise never hold together ({p_and_rival} models with both)",
        p_and_rival == 0,
    )
    expect(
        "4b. The rival premise without P is consistent (the opposite side also has a model)",
        "rival_without_P" in wit,
        wit["rival_without_P"].show() if "rival_without_P" in wit else "",
    )
    expect(
        "4c. Neither P nor the rival premise is also consistent",
        "neither" in wit,
        wit["neither"].show() if "neither" in wit else "",
    )


def run_frames():
    sizes = [(1, 2), (1, 3), (2, 2)]
    total = 0
    t_counter = None
    b_exist_counter = 0
    b_nec_counter = None
    s5_counter = 0
    for kind, m in frame_models(sizes):
        total += 1
        if not (m.A1() and m.A2() and m.P()):
            continue
        if kind == "T" and t_counter is None and not m.T_exist():
            t_counter = m
        if kind in ("B", "S5") and not m.T_exist():
            b_exist_counter += 1
        if kind == "B" and b_nec_counter is None and not m.T():
            b_nec_counter = m
        if kind == "S5" and not m.T():
            s5_counter += 1

    print(f"\nOther modal logics: {total} models enumerated.\n")
    expect(
        "5a. Without symmetry between worlds the explainer may not exist in the actual world",
        t_counter is not None,
        t_counter.show() if t_counter else "",
    )
    expect(
        f"5b. With symmetry (B) it exists in the actual world ({b_exist_counter} counterexamples)",
        b_exist_counter == 0,
    )
    expect(
        "5c. With symmetry but without transitivity it may not be necessary in the actual world",
        b_nec_counter is not None,
        b_nec_counter.show() if b_nec_counter else "",
    )
    expect(f"5d. In S5 the full theorem holds ({s5_counter} counterexamples)", s5_counter == 0)


if __name__ == "__main__":
    run_s5()
    run_frames()
    print("\nRESULT:", "all confirmed" if not failures else f"failures: {failures}")
    sys.exit(1 if failures else 0)
