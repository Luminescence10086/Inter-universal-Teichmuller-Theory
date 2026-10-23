"""Negative control: reintroduce the round-1 defect and require the cases to fail.

If ``probe_violations`` returns nothing (the pre-fix behaviour) the focused cases
must stop passing.  This is the "does the suite still catch the bug" side of the
delivery, measured separately from the bundle's PASS log.
"""
import sys

WT = "D:\\Inter-universal Teichm" + chr(0xFC) + "ller Theory\\.wt\\e1"
sys.path.insert(0, WT + "\\audit")
sys.path.insert(0, WT + "\\audit\\tests")

import mutation_harness as mh
import test_mutation_probe_exit as t

mh.probe_violations = lambda probe_results: []  # the defect this task fixes

failed, passed = [], []
for case_id in t.CASE_IDS:
    try:
        t.CASES[case_id]()
    except AssertionError as error:
        failed.append(case_id)
        print(f"FAIL as expected {case_id}: {str(error)[:160]}", flush=True)
    except Exception as error:  # noqa: BLE001
        failed.append(case_id)
        print(f"FAIL as expected {case_id}: raised {type(error).__name__}: "
              f"{str(error)[:160]}", flush=True)
    else:
        passed.append(case_id)
        print(f"PASS (unexpected, the defect was NOT caught) {case_id}", flush=True)

print(f"unexpectedly passing with the defect reintroduced: {passed}")
print(f"catching the defect: {len(failed)}/{len(t.CASE_IDS)} cases")
sys.exit(1 if passed else 0)
