"""Generate bridges/correspondence.json and validate every formal anchor against the exports.

A correspondence entry is only allowed to cite theorem ids that the repository has actually
exported. Run from the repository root:  python -B bridges/correspondence_gen.py Candidate-branch results (M1/M2/pilot-shadow) are marked separately: they are not in
this checkout's exports, so they are recorded as candidates and never as anchors.
"""
import hashlib
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]
EXPORTS = {
    'bridge': ROOT / 'bridge/verification/project-constants.json',
    'main': ROOT / 'verification/project-constants.json',
    'local': ROOT / 'local-field/verification/project-constants.json',
}
known = set()
for project, path in EXPORTS.items():
    if path.exists():
        for row in json.loads(path.read_text(encoding='utf-8')):
            if row.get('kind') == 'theorem':
                known.add(row['id'])
    else:
        raise SystemExit(f'missing export: {path}')

OBLIGATIONS = {
    'RI-01': ('finite_Ism_realization',
              'research/round3-realization-obligations.md:23-35'),
    'RI-02': ('Kummer_tensor_realization',
              'research/round3-realization-obligations.md:37-49'),
    'RI-03': ('specific_seed_realization',
              'research/round3-realization-obligations.md:51-63'),
    'RI-04': ('specific_Ind1_lift',
              'research/round3-realization-obligations.md:65-79'),
    'RI-05': ('specific_output_membership',
              'research/round3-realization-obligations.md:81-93'),
    'RI-06': ('small_ramification_log_lattice',
              'research/round3-realization-obligations.md:95-109'),
    'RI-07': ('coarse_valuation_bound',
              'research/round3-realization-obligations.md:111-123'),
    'RI-08': ('normalization_hull_compatibility',
              'research/round3-realization-obligations.md:125-137'),
}

ENTRIES = [
    dict(id='C-01', obligation='RI-04',
         iut_object='slot/label bookkeeping of the four coordinates (IUT II Ex.1.8(iv), Def.4.9(i))',
         formal=['IUTBridge.Slots.relabel_slotwise', 'IUTBridge.Slots.slotwise_commutes_of_invariant',
                 'IUTBridge.Slots.swap23_exchanges_high_slots',
                 'IUTAudit.LocalNumerics.swap23_tuple_and_theta'],
         definitions=['IUTBridge.Slots.relabel', 'IUTBridge.Slots.slotwise'],
         status='toy-coordinate-shadow',
         proves='a relabelling transports a slotwise scalar family into the conjugated family; '
                'the concrete swap 2<->3 moves exactly the high slots',
         gap='no Hodge theater, no Galois group G or open subgroup H, slots are Fin n; '
             'the label action is not an Ind1 procession automorphism',
         falsifier='if a real procession automorphism turned out not to act slotwise, the '
                   'conjugation formula would not apply'),
    dict(id='C-02', obligation='RI-07',
         iut_object='weighted average of local valuations comparing one side of the Theta-link',
         formal=['IUTBridge.WeightedLedger.weightedLedger_slotwise',
                 'IUTBridge.WeightedLedger.weightedLedger_invariant_iff',
                 'IUTBridge.Integration.slotwise_commutes_iff',
                 'IUTBridge.Integration.weightedLedger_combined_invariant_iff',
                 'IUTAudit.Scale.weighted_comparison_forces_bound'],
         status='exact-base-field-theorem',
         proves='the weighted ledger shifts by exactly sum_j w_j v(a_j), and is relabel-invariant '
                'for all tuples iff the weights are permutation-invariant; the combined '
                'relabel+scale criterion is an iff',
         gap='weights are arbitrary integers; nothing identifies them with log-volume weights, and '
             'the elements are Q_p scalars rather than Idele/Kummer data',
         falsifier='if the real comparison used non-integer or archimedean weights, the integer '
                   'ledger would not model it'),
    dict(id='C-03', obligation='RI-01',
         iut_object='admissibility of a Kummer isomorphism kappa jointly with an Ind1 action sigma',
         formal=['IUTBridge.Admissibility.not_rectangular_of_graph',
                 'IUTBridge.Admissibility.rectangular_subrelation_freezes_layer',
                 'IUTBridge.Admissibility.marginals_do_not_force_joint',
                 'IUTAudit.Transport.rectangular_iff_product',
                 'IUTAudit.Transport.coupled_choice_counterexample'],
         status='conditional-interface-only',
         proves='when the joint (automorphism, lattice layer) relation is a graph with at least two '
                'values, separate marginal admissibility cannot be composed; any rectangular '
                'sub-relation freezes the layer',
         gap='the relation is between Q_p-linear automorphisms and layers of the unit ball; no '
             'Ism group, no open-H lattice family, no Kummer element',
         falsifier='if the real allowed family were rectangular (e.g. a product of independent '
                   'choices), the obstruction would not apply to it'),
    dict(id='C-04', obligation='RI-06',
         iut_object='the layer discrimination z in p^n log_p(O_v^x) <-> n < ord_p(z)',
         formal=['IUTBridge.ScaleLedger.mem_layer_iff_le_valuation',
                 'IUTBridge.ScaleLedger.layer_image_shift',
                 'IUTBridge.ScaleLedger.valuation_shift',
                 'LocalFieldAudit.Filtration.mem_zpow_maximalIdealImage_iff_lt_valuation'],
         status='blocked-by-missing-log',
         proves='on the actual base field, the ideal/layer ladder and the valuation threshold are '
                'interchangeable, exactly and two-sidedly',
         gap='the object on the left of the real equivalence is log_p(O^x), whose image is not '
             'constructed; only the valuation side exists, so the real equivalence is not stated',
         falsifier='if log_p(O^x) were strictly smaller than the maximal ideal (small ramification, '
                   'e <= p-2 regime), the layer identity would need the sandwich instead'),
    dict(id='C-05', obligation='RI-01',
         iut_object='linearity of the finite-coordinate restriction of an Ism element',
         formal=['LocalFieldAudit.ContinuousLinearity.map_padic_smul',
                 'LocalFieldAudit.ContinuousLinearity.preserves_integerIdealImages'],
         status='exact-base-field-theorem',
         proves='a continuous additive map between Q_p modules is Q_p-linear, hence a restriction '
                'that is at least continuous and additive already lands in A(k)',
         gap='the real restriction map is not constructed; no finite H-invariant module, no '
             'unit-to-torsion-quotient map',
         falsifier='if the restriction were only additive and not continuous, the result would not '
                   'upgrade it'),
    dict(id='C-06', obligation='RI-05',
         iut_object='the possible-images family U_j and its hull (IUT III Cor.3.12, Rem.3.9.5)',
         formal=['IUTAudit.Orbit.envelope_minimal', 'IUTAudit.Orbit.envelope_minimal_closed',
                 'IUTAudit.Orbit.envelope_covers'],
         status='toy-generic-container',
         proves='for an arbitrary set and action, the envelope is the least closed container and is '
                'idempotent',
         gap='no committed identification with the real U_j: enlarging the container is allowed '
             'only if the added cost is controlled, which is not done here',
         falsifier='if the real U_j were not closed under the allowed operations, the envelope '
                   'would be a proper enlargement rather than the family'),
    dict(id='C-07', obligation='RI-08',
         iut_object='the holomorphic hull / projected hull and its integral structure R-tilde',
         formal=['IUTBridge.Admissibility.frozen_isRectangular'],
         status='toy-coordinate-shadow',
         proves='freezing the lattice layer makes independent marginal reasoning sound; the layer '
                'is then fixed rather than chosen',
         gap='no normalization, no tensor packet, no coordinate realization of O, no log-volume',
         falsifier='if the real hull normalization let the layer vary, the freezing theorem would '
                   'describe a different regime'),
    dict(id='C-08', obligation='RI-06',
         iut_object='the log-shell modulus (1/p)log(O^x) and its integral scaling',
         formal=['IUTBridge.ScaleLedger.cost_exact', 'IUTBridge.ScaleLedger.norm_shift'],
         status='blocked-by-missing-log',
         proves='moving the ladder container between two layers is the single dilation of signed '
                'exponent difference; norms scale exactly',
         gap='no measure/volume is defined, and the log image is absent, so this is an index '
             'identity, not a log-volume statement',
         falsifier='if a future cost estimate needed the measure rather than the index, this '
                   'identity alone would not supply it'),
]

validated = []
missing_all = []
for entry in ENTRIES:
    missing = [tid for tid in entry['formal'] if tid not in known]
    if missing:
        missing_all.append((entry['id'], missing))
    validated.append({**entry, 'anchors_missing': missing})

CANDIDATES = [
    dict(id='K-01', obligation='RI-07', branch='task/m1 → candidates/restricted-ledger',
         result='candidates/restricted-ledger/Candidates/RestrictedLedger.lean',
         theorems=['integer_span_criterion', 'weightedLedger_shift',
                   'restricted_ledger_criterion', 'equal_valuation_two_slot_example',
                   'full_domain_specialization'],
         value='turns the global weighted-invariance test into finitely many integer equations on a '
               'restricted admissible domain, with the finite-realisation hypothesis explicit',
         gap='no real IUT admissible region is constructed, so the certificate stays a criterion'),
    dict(id='K-02', obligation='RI-05', branch='task/m2 → candidates/orbit-quotient',
         result='candidates/orbit-quotient/Candidates/OrbitQuotient.lean',
         theorems=['hull_thresholds', 'hull_minimal', 'box_cardinality',
                   'enlargement_integer_budget', 'two_three_four'],
         value='exact finite envelope: hull thresholds are orbit minima, boxes have cardinality '
               'p^(sum (N - k_j)), and U vs H are proved apart (2/3/4 at p=2,N=1,n=2,k=(0,1))',
         gap='ZMod(p^N) quotient boxes only; no normalization, no log-volume, Γ is a finite family'),
    dict(id='K-03', obligation='RI-03', branch='explore/pilot → candidates/pilot-shadow',
         result='candidates/pilot-shadow/Candidates/PilotShadow.lean',
         theorems=['orbit_mem_iff', 'orbit_card', 'hull_eq', 'hull_strict_one_coordinate',
                   'swap23_moves_profile', 'excess_is_uniform'],
         value='the valuation vector of the (b1,b1,b2,b1) pattern as an actual object: 4-element '
               'orbit, constant hull at min(v1,v2), excess exactly one slot, and the label action '
               'moves the pattern while the hull ignores the slot',
         gap='integers standing in for valuations; no places, no pilot, no Theta-link'),
]

payload = {
    'schema': 1,
    'tool': 'ad-hoc generator (see research/exploration/correspondence.md for the command)',
    'purpose': ('Map each formal object of this repository to the real-interface obligation it '
                'would have to refine. Statuses describe the CORRESPONDENCE, not the truth of any '
                'IUT statement. Nothing here closes a gap.'),
    'obligations': [{'id': key, 'name': name, 'source_note': note}
                    for key, (name, note) in OBLIGATIONS.items()],
    'anchors_validated_against': {project: str(path.relative_to(ROOT))
                                 for project, path in EXPORTS.items()},
    'anchor_count': len(known),
    'entries': validated,
    'candidate_results': CANDIDATES,
    'anchors_all_present': not missing_all,
    'iut_object_constructed': False,
    'iut_cor312_proved': False,
    'abc_proved': False,
}
out = ROOT / 'bridges/correspondence.json'
out.write_text(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + '\n',
               encoding='utf-8')
print(f'wrote {out.relative_to(ROOT)} : {len(validated)} correspondence entries, '
      f'{len(CANDIDATES)} candidate results, {len(known)} known theorem ids')
if missing_all:
    print('MISSING ANCHORS:', missing_all)
