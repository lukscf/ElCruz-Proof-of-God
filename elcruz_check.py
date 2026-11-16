#!/usr/bin/env python3
"""ElCruz: verificacao exaustiva em modelos finitos.

W = mundos, D = individuos.
E[d, w]: d existe em w.
X[d, w]: em w, d explica por que existem coisas contingentes.
R: acessibilidade entre mundos (None = S5, todo mundo acessa todo mundo).
"""
import sys
from itertools import product


class Model:
    def __init__(self, nD, nW, E, X, actual, R=None):
        self.D, self.W = range(nD), range(nW)
        self.E, self.X, self.a, self.R = E, X, actual, R

    def acc(self, w, v):
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

    def Q(self):
        return any(
            self.acc(self.a, w)
            and not any(self.E[d, w] and self.nec(d, w) for d in self.D)
            for w in self.W
        )

    def contingent_in_actual(self):
        return any(self.cont(d, self.a) for d in self.D)

    def show(self):
        out = [f"    mundos {list(self.W)}, mundo real = {self.a}"]
        if self.R is not None:
            arrows = [f"{w}->{v}" for w in self.W for v in self.W if w != v and self.R[w, v]]
            out.append("    acessibilidade (alem de w->w): " + (", ".join(arrows) or "nenhuma"))
        for d in self.D:
            ex = [w for w in self.W if self.E[d, w]]
            xs = [w for w in self.W if self.X[d, w]]
            out.append(f"    individuo {d}: existe em {ex}, explica em {xs}")
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
    print(f"[{'OK' if ok else 'FALHOU'}] {label}" + (f"\n{detail}" if detail else ""))
    if not ok:
        failures.append(label)


def run_s5():
    sizes = [(d, w) for d in (1, 2) for w in (1, 2, 3, 4)] + [(3, 3)]
    total = premises = counter = p_and_q = 0
    wit = {}
    for m in s5_models(sizes):
        total += 1
        a1, a2, p = m.A1(), m.A2(), m.P()
        if a1 and a2 and p:
            premises += 1
            if not m.T():
                counter += 1
                wit.setdefault("contra", m)
            if m.Q():
                p_and_q += 1
            if "contingencia" not in wit and m.contingent_in_actual():
                wit["contingencia"] = m
        elif a2 and p and not a1:
            if "semA1" not in wit and not m.T():
                wit["semA1"] = m
        elif a1 and p and not a2:
            if "semA2" not in wit and not m.T():
                wit["semA2"] = m
        elif a1 and a2 and not p:
            if "semP" not in wit and not m.T():
                wit["semP"] = m
            if m.Q():
                wit.setdefault("Q_sem_P", m)
            else:
                wit.setdefault("nem_P_nem_Q", m)

    print(f"S5: {total} modelos enumerados, {premises} satisfazem A1, A2 e P.\n")
    expect(
        f"1. Validade: A1, A2, P => T ({counter} contraexemplos)",
        counter == 0,
        wit["contra"].show() if "contra" in wit else "",
    )
    expect(
        "2. Consistencia sem colapso modal: modelo de A1, A2, P com coisa contingente",
        "contingencia" in wit,
        wit["contingencia"].show() if "contingencia" in wit else "",
    )
    for key, name in (("semA1", "A1"), ("semA2", "A2"), ("semP", "P")):
        expect(
            f"3. Independencia: sem {name} existe contraexemplo",
            key in wit,
            wit[key].show() if key in wit else "",
        )
    expect(f"4a. P e Q nunca juntas ({p_and_q} modelos com as duas)", p_and_q == 0)
    expect(
        "4b. Q sem P e consistente (lado oposto tambem tem modelo)",
        "Q_sem_P" in wit,
        wit["Q_sem_P"].show() if "Q_sem_P" in wit else "",
    )
    expect(
        "4c. Nem P nem Q tambem e consistente",
        "nem_P_nem_Q" in wit,
        wit["nem_P_nem_Q"].show() if "nem_P_nem_Q" in wit else "",
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

    print(f"\nOutras logicas modais: {total} modelos enumerados.\n")
    expect(
        "5a. Sem simetria entre mundos o explicador pode nao existir no mundo real",
        t_counter is not None,
        t_counter.show() if t_counter else "",
    )
    expect(
        f"5b. Com simetria (B) ele existe no mundo real ({b_exist_counter} contraexemplos)",
        b_exist_counter == 0,
    )
    expect(
        "5c. Com simetria mas sem transitividade ele pode nao ser necessario no mundo real",
        b_nec_counter is not None,
        b_nec_counter.show() if b_nec_counter else "",
    )
    expect(f"5d. Em S5 o teorema completo vale ({s5_counter} contraexemplos)", s5_counter == 0)


if __name__ == "__main__":
    run_s5()
    run_frames()
    print("\nRESULTADO:", "tudo confirmado" if not failures else f"falhas: {failures}")
    sys.exit(1 if failures else 0)
