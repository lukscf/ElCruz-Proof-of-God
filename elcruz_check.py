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

    def contingents(self, w):
        return [x for x in self.D if self.cont(x, w)]

    def root(self, m, w):
        cs = self.contingents(w)
        return bool(cs) and all(self.part[m, x, w] for x in cs)

    def poss_root(self, m):
        return any(self.acc(self.a, w) and self.root(m, w) for w in self.W)

    def F1(self):
        return all(
            self.E[m, w] and self.E[x, w] for (m, x, w), holds in self.part.items() if holds
        )

    def F2(self):
        return not any(self.cont(x, w) and self.part[x, x, w] for x in self.D for w in self.W)

    def F3(self):
        return all(
            self.part[a, c, w]
            for (a, b, w), holds in self.part.items()
            if holds
            for c in self.D
            if self.part[b, c, w]
        )

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

    def no_empty_world(self):
        return all(any(self.E[x, w] for x in self.D) for w in self.W if self.acc(self.a, w))

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
            for c in self.contingents(w)
        )

    def contingent_in_actual(self):
        return bool(self.contingents(self.a))

    def brute(self, c, w):
        return self.cont(c, w) and not any(self.part[m, c, w] for m in self.D)

    def endless(self, w):
        edges = {(y, c) for y in self.contingents(w) for c in self.D if self.part[y, c, w]}
        reach = set(edges)
        for _ in self.D:
            reach |= {(a, c) for (a, b) in reach for (b2, c) in edges if b == b2}
        return any((x, x) in reach for x in self.D)

    def necessary_explainer(self, w):
        return any(
            self.part[m, c, w] and self.E[m, w] and self.nec(m, w)
            for c in self.contingents(w)
            for m in self.D
        )

    def options(self, w):
        return (any(self.brute(c, w) for c in self.D), self.endless(w), self.necessary_explainer(w))

    def map_holds(self):
        return all(any(self.options(w)) for w in self.W if self.contingents(w))

    def lone_holds(self):
        return all(
            self.E[m, w] and self.nec(m, w)
            for w in self.W
            if len(self.contingents(w)) == 1
            for m in self.D
            if self.part[m, self.contingents(w)[0], w]
        )

    def independence_holds(self):
        return not any(
            self.part[c, r, w]
            for w in self.W
            for r in self.D
            if self.root(r, w)
            for c in self.contingents(w)
        )

    def origins(self, w):
        cs = self.contingents(w)
        return [c for c in cs if all(x == c or self.part[c, x, w] for x in cs)]

    def necessary_root(self, w):
        return any(self.root(m, w) and self.E[m, w] and self.nec(m, w) for m in self.D)

    def origin_holds(self):
        return all(
            self.root(m, w) and self.E[m, w] and self.nec(m, w)
            for w in self.W
            for c in self.origins(w)
            for m in self.D
            if self.part[m, c, w]
        )

    def dichotomy_holds(self):
        return all(
            self.brute(c, w) != self.necessary_root(w) for w in self.W for c in self.origins(w)
        )

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


def interps(nD, nW, f1_only=False):
    e_keys = [(x, w) for x in range(nD) for w in range(nW)]
    p_keys = [(m, x, w) for m in range(nD) for x in range(nD) for w in range(nW)]
    for eb in product((False, True), repeat=len(e_keys)):
        E = dict(zip(e_keys, eb))
        free = p_keys
        if f1_only:
            if not any(0 < sum(E[x, w] for w in range(nW)) < nW for x in range(nD)):
                continue
            free = [k for k in p_keys if E[k[0], k[2]] and E[k[1], k[2]]]
        base = dict.fromkeys(p_keys, False)
        for pb in product((False, True), repeat=len(free)):
            part = dict(base)
            part.update(zip(free, pb))
            yield E, part


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

failures = []


def expect(label, ok, model=None):
    print(f"[{'OK' if ok else 'FAILED'}] {label}" + (f"\n{model.show()}" if model else ""))
    if not ok:
        failures.append(label)


def run_s5():
    full_sizes = [(1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3)]
    bad = dict.fromkeys(
        (
            "theorem",
            "p_and_rival",
            "empty",
            "collapse",
            "actual",
            "map",
            "lone",
            "independence",
            "origin",
            "dichotomy",
        ),
        0,
    )
    wit = {}
    totals = {"full": 0, "f1": 0, "premises": 0}

    def check(m):
        f1, f2, f3, p = m.F1(), m.F2(), m.F3(), m.P()
        if f1:
            bad["map"] += not m.map_holds()
            for w in m.W:
                if not m.contingents(w):
                    continue
                opts = m.options(w)
                if f2 and f3 and opts == (True, False, False):
                    wit.setdefault("only_brute", m)
                if f2 and f3 and opts == (False, False, True):
                    wit.setdefault("only_necessary", m)
                if f2 and not f3 and opts == (False, True, False):
                    wit.setdefault("only_loop", m)
        if f2 and f3:
            bad["independence"] += not m.independence_holds()
        if f1 and f2:
            bad["lone"] += not m.lone_holds()
            bad["collapse"] += not m.no_collapse()
            for a in m.W:
                m.a = a
                bad["actual"] += not m.actual_version()
            m.a = 0
            if f3:
                bad["origin"] += not m.origin_holds()
                bad["dichotomy"] += not m.dichotomy_holds()
            else:
                if not m.independence_holds():
                    wit.setdefault("no_F3_independence", m)
                if not m.origin_holds():
                    wit.setdefault("no_F3_origin", m)
        if f1 and f2 and p:
            totals["premises"] += 1
            if not m.T():
                bad["theorem"] += 1
                wit.setdefault("counter", m)
            bad["p_and_rival"] += m.rival()
            bad["empty"] += not m.no_empty_world()
            if f3 and "consistency" not in wit:
                for a in m.W:
                    m.a = a
                    if m.contingent_in_actual():
                        wit["consistency"] = m
                        break
                else:
                    m.a = 0
        elif f2 and p and not f1:
            if not m.T():
                wit.setdefault("no_F1", m)
        elif f1 and p and not f2:
            if not m.T():
                wit.setdefault("no_F2", m)
        elif f1 and f2 and not p:
            if not m.T():
                wit.setdefault("no_P", m)
            wit.setdefault("rival_without_P" if m.rival() else "neither", m)

    for nD, nW in full_sizes:
        for E, part in interps(nD, nW):
            totals["full"] += 1
            check(Model(nD, nW, E, part))
    for E, part in interps(3, 2, f1_only=True):
        totals["f1"] += 1
        check(Model(3, 2, E, part))

    print(
        f"S5: {totals['full']} models of every kind (up to 2 things and 3 worlds) and "
        f"{totals['f1']} models satisfying F1 with 3 things and 2 worlds; "
        f"{totals['premises']} satisfy F1, F2 and P.\n"
    )

    print("Section 1: the map")
    expect(f"1a. Brute fact, endless chain or necessary being ({bad['map']} counterexamples)", bad["map"] == 0)
    expect("1b. A world whose only option is a brute fact", "only_brute" in wit, wit.get("only_brute"))
    expect(
        "1c. A world whose only option is a loop (F3 fails there)",
        "only_loop" in wit,
        wit.get("only_loop"),
    )
    expect(
        "1d. A world whose only option is a necessary being",
        "only_necessary" in wit,
        wit.get("only_necessary"),
    )

    print("\nSection 2: the argument")
    expect(f"2a. F1, F2, P => T ({bad['theorem']} counterexamples)", bad["theorem"] == 0, wit.get("counter"))
    expect(
        "2b. Consistency: a model of F1, F2, F3 and P with a contingent thing in the actual world",
        "consistency" in wit,
        wit.get("consistency"),
    )
    for key, name in (("no_F1", "F1"), ("no_F2", "F2"), ("no_P", "P")):
        expect(f"2c. Independence: without {name} there is a counterexample", key in wit, wit.get(key))
    expect(
        f"2d. P and the rival premise never hold together ({bad['p_and_rival']} models with both)",
        bad["p_and_rival"] == 0,
    )
    expect(
        "2e. The rival premise without P is consistent (the opposite side also has a model)",
        "rival_without_P" in wit,
        wit.get("rival_without_P"),
    )
    expect("2f. Neither P nor the rival premise is also consistent", "neither" in wit, wit.get("neither"))
    expect(f"2g. No modal collapse ({bad['collapse']} counterexamples)", bad["collapse"] == 0)
    expect(f"2h. Actual-world version ({bad['actual']} counterexamples)", bad["actual"] == 0)
    expect(f"2i. If P holds no world is empty ({bad['empty']} counterexamples)", bad["empty"] == 0)

    print("\nSection 3: a lone contingent thing")
    expect(
        f"3a. Whatever explains a lone contingent thing is necessary ({bad['lone']} counterexamples)",
        bad["lone"] == 0,
    )

    print("\nSection 4: transitivity")
    expect(
        f"4a. Nothing contingent explains a root ({bad['independence']} counterexamples)",
        bad["independence"] == 0,
    )
    expect(
        "4b. Without F3 a contingent thing can explain a root",
        "no_F3_independence" in wit,
        wit.get("no_F3_independence"),
    )
    expect(
        f"4c. Whatever explains an origin is a necessary root ({bad['origin']} counterexamples)",
        bad["origin"] == 0,
    )
    expect(
        "4d. Without F3 a contingent thing can explain an origin",
        "no_F3_origin" in wit,
        wit.get("no_F3_origin"),
    )
    expect(
        f"4e. Origin: brute fact or necessary root, never both ({bad['dichotomy']} counterexamples)",
        bad["dichotomy"] == 0,
    )


def run_frames():
    sizes = [(1, 2), (1, 3), (2, 2)]
    total = b_exist_counter = s5_counter = 0
    bad = dict.fromkeys(("map", "actual", "collapse", "lone", "independence", "origin", "dichotomy"), 0)
    for nD, nW in sizes:
        for R in frames(nW):
            sym, trans = is_sym(R, nW), is_trans(R, nW)
            kind = "S5" if sym and trans else "B" if sym else "T"
            for E, part in interps(nD, nW):
                for a in range(nW):
                    total += 1
                    m = Model(nD, nW, E, part, a, R)
                    f1, f2, f3 = m.F1(), m.F2(), m.F3()
                    if f1:
                        bad["map"] += not m.map_holds()
                    if f2 and f3:
                        bad["independence"] += not m.independence_holds()
                    if not (f1 and f2):
                        continue
                    bad["actual"] += not m.actual_version()
                    bad["collapse"] += not m.no_collapse()
                    bad["lone"] += not m.lone_holds()
                    if f3:
                        bad["origin"] += not m.origin_holds()
                        bad["dichotomy"] += not m.dichotomy_holds()
                    if not m.P():
                        continue
                    if kind in ("B", "S5") and not m.T_exist():
                        b_exist_counter += 1
                    if kind == "S5" and not m.T():
                        s5_counter += 1

    print(f"\nOther modal logics: {total} models enumerated.\n")
    m = NO_SYMMETRY
    expect(
        "5a. Without symmetry between worlds the possible root may not exist in the actual world",
        not is_sym(m.R, 3) and m.F1() and m.F2() and m.F3() and m.P() and not m.T_exist(),
        m,
    )
    expect(
        f"5b. With symmetry (B) it exists in the actual world ({b_exist_counter} counterexamples)",
        b_exist_counter == 0,
    )
    m = NO_TRANSITIVITY
    expect(
        "5c. With symmetry but without transitivity it may not be necessary in the actual world",
        is_sym(m.R, 3)
        and not is_trans(m.R, 3)
        and m.F1()
        and m.F2()
        and m.F3()
        and m.P()
        and m.T_exist()
        and not m.T(),
        m,
    )
    expect(f"5d. In S5 the main theorem holds ({s5_counter} counterexamples)", s5_counter == 0)
    expect(
        "5e. Results that need no frame condition hold in every frame tried "
        f"({sum(bad.values())} counterexamples)",
        sum(bad.values()) == 0,
    )


if __name__ == "__main__":
    run_s5()
    run_frames()
    print("\nRESULT:", "all confirmed" if not failures else f"failures: {failures}")
    sys.exit(1 if failures else 0)
