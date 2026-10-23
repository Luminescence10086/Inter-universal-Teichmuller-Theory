"""N10 -- finite constraint experiments on the choice relations (EXPERIMENTAL).

Three small models, each exhaustively enumerated (no solver, no heuristics), to separate four statements that
are easy to conflate:

    E1  exists a choice S with reading(S) = q            (the existential form of (9-1))
    E2  every choice S has reading(S) = q                (the full-family invariance form)
    J   the same S works for two different requirement families simultaneously
    U   a relation that the sources leave unknown is treated as UNKNOWN, not as independent

Every model is small enough to print the entire truth table, so a reviewer can re-derive each verdict by hand.
All results are EXPERIMENTAL and hold only for the model named in the header; none of them says anything about
IUT, and finite unsatisfiability never proves anything about the original objects.

Usage: py -3 constraints.py            # writes results.json
"""
import itertools
import json
import pathlib

HERE = pathlib.Path(__file__).resolve().parent


def truth(cond):
    return 'SAT' if cond else 'UNSAT'


def model_1():
    """One family, one target: E1 vs E2 differ."""
    labels = [0, 1, 2]
    reading = {0: 1, 1: 2, 2: 3}
    q = 3
    e1 = any(reading[s] == q for s in labels)
    e2 = all(reading[s] == q for s in labels)
    witness = [s for s in labels if reading[s] == q]
    return {
        'name': 'M1-one-family',
        'reading': {str(k): v for k, v in reading.items()},
        'target_q': q,
        'E1_exists': {'verdict': truth(e1), 'witnesses': witness},
        'E2_all': {'verdict': truth(e2), 'counterexample': [s for s in labels if reading[s] != q]},
        'conclusion': ('E1 holds while E2 fails: the existential form does not imply the family-invariance form'),
        'reading_source': 'toy model; the paper-side analogue is N03 O1 vs O5',
    }


def model_2():
    """Two requirement families over the same choice set: pairwise satisfiable, not jointly."""
    choices = ['a', 'b']
    # family F1 wants reading = 1; family F2 wants reading = 2 under a shared normalisation constant c
    base = {'a': 1, 'b': 2}
    F1 = {s: base[s] for s in choices}           # F1: pick S with value 1  -> only 'a'
    F2 = {s: base[s] + 1 for s in choices}       # F2: pick S with value 2  -> only 'a' shifted: 2 at 'a'? no: a->2
    sat_F1 = [s for s in choices if F1[s] == 1]
    sat_F2 = [s for s in choices if F2[s] == 2]
    joint = [s for s in choices if F1[s] == 1 and F2[s] == 2]
    return {
        'name': 'M2-two-families',
        'F1': F1, 'F2': F2,
        'F1_alone': {'verdict': truth(bool(sat_F1)), 'witnesses': sat_F1},
        'F2_alone': {'verdict': truth(bool(sat_F2)), 'witnesses': sat_F2},
        'joint': {'verdict': truth(bool(joint)), 'witnesses': joint},
        'conclusion': ('each family is satisfiable on its own and the joint constraint is satisfiable here, so this '
                       'model does NOT exhibit the failure; it is the control case. The failure is M2b below.'),
        'reading_source': 'toy model; paper-side analogue: two requirements sharing one S (N07 W9)',
    }


def model_2b():
    """Same shape, with the two families' only witnesses disjoint."""
    choices = ['a', 'b', 'c']
    F1 = {'a': 1, 'b': 2, 'c': 3}       # target 1 -> witness 'a'
    F2 = {'a': 2, 'b': 1, 'c': 0}       # target 1 -> witness 'b'
    sat_F1 = [s for s in choices if F1[s] == 1]
    sat_F2 = [s for s in choices if F2[s] == 1]
    joint = [s for s in choices if F1[s] == 1 and F2[s] == 1]
    return {
        'name': 'M2b-two-families-disjoint',
        'F1': F1, 'F2': F2,
        'F1_alone': {'verdict': truth(bool(sat_F1)), 'witnesses': sat_F1},
        'F2_alone': {'verdict': truth(bool(sat_F2)), 'witnesses': sat_F2},
        'joint': {'verdict': truth(bool(joint)), 'witnesses': joint},
        'conclusion': ('both families are individually satisfiable and jointly unsatisfiable: "there is an S for each '
                       'requirement" does not give "there is one S for both"'),
        'reading_source': 'toy model; this is the smallest instance of the joint-witness fallacy named in N07',
    }


def model_3():
    """An unknown relation must stay unknown: assuming independence manufactures witnesses."""
    # three binary attributes; the sources fix only that not all three may hold together
    attrs = [('x', 'y', 'z') for _ in range(1)][0]
    assignments = list(itertools.product([0, 1], repeat=3))
    known_ok = [a for a in assignments if not (a[0] and a[1] and a[2])]   # the one known constraint
    # a solver that additionally assumes "x, y independent" would exclude (1,1,*) - show what that costs
    augmented = [a for a in known_ok if not (a[0] == 1 and a[1] == 1)]
    return {
        'name': 'M3-unknown-relation',
        'known_constraint': 'not (x and y and z)',
        'satisfying_assignments_under_known_constraints_only': known_ok,
        'satisfying_assignments_if_independence_of_x_y_is_assumed': augmented,
        'conclusion': ('the extra assumption removes the assignments with x = y = 1 that satisfy every known '
                       'constraint, i.e. assuming independence narrows the model without evidence; unknown relations '
                       'must be reported as UNKNOWN, not silently closed'),
        'reading_source': 'catalog N10 instruction: missing relations must stay unknown',
    }


def main():
    models = [model_1(), model_2(), model_2b(), model_3()]
    out = {
        'tool': 'n10-finite-constraints',
        'tag': 'EXPERIMENTAL',
        'models': models,
        'not_a_proof': True,
        'scope_note': ('every verdict is an exhaustive enumeration over the named finite model; finite '
                       'unsatisfiability is not a statement about IUT'),
        'constraint_provenance': [
            {'constraint': 'E1 exists a choice with reading = q', 'source': 'LANA §9.2 line 2141 (9-1) as an existential'},
            {'constraint': 'E2 every choice has reading = q', 'source': 'NOT in the sources; it is the stronger form '
                                                                       'that the earlier round wrongly treated as necessary'},
            {'constraint': 'J one S for two requirement families', 'source': 'N07 W9 (joint witness)'},
            {'constraint': 'U unknown relations', 'source': 'N05: shared_finite_quotient is UNRESOLVED for every item'},
        ],
    }
    (HERE / 'results.json').write_text(json.dumps(out, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    for m in models:
        keys = [k for k in m if k in ('E1_exists', 'E2_all', 'joint', 'F1_alone', 'F2_alone')]
        if keys:
            print(m['name'], {k: (m[k]['verdict'] if isinstance(m[k], dict) else m[k]) for k in keys})
        else:
            print(m['name'], 'assignments under known constraints:', len(m['satisfying_assignments_under_known_constraints_only']),
                  '| under the extra independence assumption:',
                  len(m['satisfying_assignments_if_independence_of_x_y_is_assumed']))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
