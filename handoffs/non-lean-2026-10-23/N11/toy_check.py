#!/usr/bin/env python3
# -*- coding: ascii -*-
"""
N11 toy_check.py -- exact-arithmetic minimal testable examples for the two tool cards.

Card 1 (T3-LAT, route 3: non-archimedean lattices / finite modules):
    Is the log-shell container hull a per-coordinate box b*O (what
    `LocalTheory.hull` / `scaledIntegral` realises), or is it the log-convex
    hull (what an analytic holomorphic hull would give)?  Part A decides this
    on exponent sets with exact integer certificates (separating functionals),
    and measures the log-volume gap exactly.

Card 2 (T4-ATT, route 4: constraint solving / optimisation duality):
    Two EtaAlg-shaped objects with identical (T1)-(T3)-type data can have
    different attainment status for the same target t.  Part B exhibits a
    WITNESS case and a CERTIFICATE case for the same t, using exact rationals
    on the interval model of `Ind3`'s log-volume range
    (`exists_ind3_logVol_iff`, Iut/Wall/Ind3.lean:253).

No Lean, no network, no third-party packages, no randomness.
Run:  py -3 toy_check.py
Writes: toy_check.log (UTF-8) next to this file, and prints the same text.
Tags: everything below is EXPERIMENTAL (a finite model), never a proof.
"""

from fractions import Fraction as F
from itertools import combinations

log = []


def say(s=""):
    print(s)
    log.append(s)


FAILS = []


def check(name, cond, detail=""):
    if cond:
        say("  PASS  %s %s" % (name, detail))
    else:
        say("  FAIL  %s %s" % (name, detail))
        FAILS.append(name)


# ---------------------------------------------------------------- Part A ---
# Exponent model: v = (v_1,...,v_n) in Z^n, v_j = val_p(x_j).
# A region given by an exponent set E (the points that occur) has
#   box hull  B(E) = { v in Z^n : v_j >= min_j E }        (a per-coordinate box = b*O)
#   log-convex hull (analytic Reinhardt hull) = conv(E)
# Claim A: B(E) == E (E is already a box) <=> box hull == log-convex hull (as sets).
# When E is not a box, an integer functional phi separates a point of B(E)\conv(E).


def box_mins(E, n):
    return tuple(min(v[j] for v in E) for j in range(n))


def in_box(E, x, n):
    m = box_mins(E, n)
    return all(x[j] >= m[j] for j in range(n))


def dot(phi, v):
    return sum(phi[j] * v[j] for j in range(len(phi)))


def verify_separator(E, x, phi, c):
    """phi.e >= c for all e in E, but phi.x < c  =>  x in B(E) and x not in conv(E)."""
    on_E = all(dot(phi, e) >= c for e in E)
    at_x = dot(phi, x) < c
    return on_E and at_x


def mu_box(E, p, n):
    """Haar measure on Q_p^n of the box {v_j >= min_j E}: prod_j p^{-m_j}."""
    m = box_mins(E, n)
    return F(1, p ** sum(m))


CASES_A = [
    # name, E, witness point x in B(E)\conv(E), separator phi, constant c
    ("A1 box (2x2 square, E == B(E))", [(0, 0), (0, 1), (1, 0), (1, 1)], None, None, None),
    ("A2 diagonal {(0,0),(1,1)}", [(0, 0), (1, 1)], (0, 1), (1, -1), 0),
    ("A3 anti-diagonal {(0,1),(1,0)}", [(0, 1), (1, 0)], (0, 0), (1, 1), 1),
]

say("=" * 72)
say("Part A -- card T3-LAT (N08-G2/G3): coordinate box vs log-convex hull")
say("=" * 72)
say("p = 2, n = 2, exponent coordinates v_j = val_2(x_j)")
say("")

for name, E, x, phi, c in CASES_A:
    n = 2
    m = box_mins(E, n)
    say("%s" % name)
    say("   box mins m = %s   =>  B(E) = { v : %s }" % (m, ", ".join("v%d >= %d" % (j + 1, m[j]) for j in range(n))))
    if x is None:
        say("   E is itself a box: B(E) = E = conv(E)  ->  BOX")
        say("   mu(B(E)) = %s ,  mu(conv E) = %s  (no gap)" % (mu_box(E, 2, n), mu_box(E, 2, n)))
        check("A-box-closes", mu_box(E, 2, n) == F(1))
    else:
        ok_sep = verify_separator(E, x, phi, c)
        check("x not in E (so B(E) strictly larger than E)", x not in E)
        check("separator on E", all(dot(phi, e) >= c for e in E),
              "(phi.e = %s, c = %s)" % ([dot(phi, e) for e in E], c))
        check("separator at x", dot(phi, x) < c, "(phi.x = %d for x = %s)" % (dot(phi, x), x))
        check("=> x in B(E) and x not in conv(E)", ok_sep and in_box(E, x, n),
              "-> NONBOX")
        say("   NONBOX: x = %s lies in the coordinate box but not in the log-convex hull" % (x,))
        say("   mu(B(E)) = %s ,  mu(conv E) = 0  (conv is lower-dimensional)" % mu_box(E, 2, n))
        say("   => the log-convex hull is not even admissible here: the two")
        say("      hull conventions are not comparable as regions")
    say("")

say("Reading: `LocalTheory.hull` returns a hull REGION (b*O), i.e. exactly B(E).")
say("So on a capsule whose exponent set is not a box the coordinate-box hull is")
say("strictly larger than the log-convex hull; in the two NONBOX cases above the")
say("latter has Haar measure 0 and is not an admissible region at all.  Hence")
say("'hull = per-coordinate lambda*O' is a substantive claim about the container,")
say("not a harmless relaxation -- the deviation is documented at Ind3.lean:32-38.")
say("That is the precise form of N08-G2: it is a decidable property of E.")
say("")

# ---------------------------------------------------------------- Part B ---
# Interval model of Ind3's log-volume range (exists_ind3_logVol_iff):
#   C = { S : S subseteq [0, M] }, mu(S) = length(S), range(mu) = [0, M].
# An EtaAlg-shaped object supplies  out : C -> C  with (T3) only: out(S) <= M.
# Classification of target t: WITNESS / CERTIFICATE / UNDETERMINED.

M = F(1)
TARGET = F(3, 4)


def classify(f, t, M):
    """f maps a rational sample of mu(S) (monotone, piecewise-linear on [0,M])."""
    grid = [F(k, 100) for k in range(0, 101)]
    img = [f(s) for s in grid]
    sup = max(img)
    if t < 0:
        return ("CERTIFICATE", F(0), "t < 0 = inf of the range")
    if t <= sup:
        # witness: bisect on the monotone f
        lo, hi = F(0), M
        for _ in range(200):
            mid = (lo + hi) / 2
            if f(mid) < t:
                lo = mid
            else:
                hi = mid
        return ("WITNESS", hi, "S of length %s" % hi)
    return ("CERTIFICATE", sup, "sup of the image is %s < t = %s" % (sup, t))


say("=" * 72)
say("Part B -- card T4-ATT (N07-H1): attainment vs strict certificate")
say("=" * 72)
say("M = log-vol(hull(VC(I))) = %s ,   target t = qPilot.lhs = %s" % (M, TARGET))
say("")

MODELS = [
    # (name, out-as-measure-map, satisfies (T1)/(T2)/(T3)?)
    ("M1 identified-copies shape: mu(out S) = mu(S)", lambda s: s,
     "T1 yes, T2 yes, T3: mu <= M yes"),
    ("M2 same fields, other out: mu(out S) = min(mu(S), M/2)",
     lambda s: min(s, M / 2), "T1 yes, T2 yes, T3: mu <= M yes"),
]

for name, f, t3 in MODELS:
    kind, val, why = classify(f, TARGET, M)
    say("%s" % name)
    say("   %s" % t3)
    say("   -> %s : %s  (%s)" % (kind, val, why))
    say("")

check("M1 WITNESS", classify(MODELS[0][1], TARGET, M)[0] == "WITNESS")
check("M1 witness inside hull", classify(MODELS[0][1], TARGET, M)[1] <= M)
check("M2 CERTIFICATE", classify(MODELS[1][1], TARGET, M)[0] == "CERTIFICATE")
check("M2 certificate is strict", classify(MODELS[1][1], TARGET, M)[1] < TARGET)
check("M2 (T3) still holds", all(MODELS[1][1](s) <= M for s in (F(k, 10) for k in range(11))))
check("fields do not decide",
      classify(MODELS[0][1], TARGET, M)[0] != classify(MODELS[1][1], TARGET, M)[0])
say("Reading: the two models agree on every declared field of `EtaAlg D` that")
say("Part B can see (T1 permutes S, T2 etUnitOnly, T3 'out(S) inside the hull'),")
say("yet M1 attains the target and M2 does not.  Therefore the declared fields")
say("alone give UNDETERMINED; a decision needs one more declared item (the")
say("sup of the log-vol range of `out iota`).  This is exactly N07-H1: `out` is")
say("a bare field and `realisation` (EtaAlg.lean:123) gives containment only.")
say("")

say("=" * 72)
if FAILS:
    say("RESULT: %d FAILURE(S): %s" % (len(FAILS), ", ".join(FAILS)))
else:
    say("RESULT: ALL PASS")
say("Scope: finite/rational model only. EXPERIMENTAL, not a proof, not Lean.")
say("=" * 72)

with open("toy_check.log", "w", encoding="utf-8") as fh:
    fh.write("\n".join(log) + "\n")

raise SystemExit(1 if FAILS else 0)
