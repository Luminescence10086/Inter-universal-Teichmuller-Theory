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

# Evidence tiers for "is the IUT object actually recorded in local evidence?":
# E1 = definition recorded and statable; E2 = construction locators only, no data list;
# E3 = role recorded but definition absent; E4 = wholly absent (only negative
# characterisations). Quoted from research/exploration/definitions-inventory.md, which
# records the exact note line for every row.
TIERS = {
    'C-01': ('E1', 'Ism and the open-H lattice conditions are recorded and statable; the '
                   'coordinate action itself is our own construct'),
    'C-02': ('E2', 'the comparison shape is recorded, but log-volume weights are not given as '
                   'data; our weights are hand-chosen integers'),
    'C-03': ('E1', 'Ism is recorded; the joint admissibility relation between its elements is '
                   'not, so the relation here is ours'),
    'C-04': ('E1', 'the layer discriminator is recorded; log_p(O^x) provenance additionally '
                   'needs the missing logarithm'),
    'C-05': ('E1', 'A(k) is recorded as an acknowledged over-approximation, not as Ism'),
    'C-06': ('E3', 'the possible-images family role is recorded but the dependent index type '
                   'was never extracted'),
    'C-07': ('E2', 'the hull is characterised only ("least lambda_0 O-type region"); the class '
                   'of allowed regions is not recorded'),
    'C-08': ('E1', 'the log-shell role is recorded and statable; the log image is the gap'),
}

COMPANION = {
    'definitions_inventory': 'research/exploration/definitions-inventory.md',
    'log_kummer_feasibility': 'research/exploration/log-kummer-feasibility.md',
    'synthesis': 'research/exploration/correspondence.md',
}

# Identifications that would look like progress and would be false. Each is stated so a
# reader can check whether a future claim has quietly made it.
FORBIDDEN = [
    dict(id='F-01',
         reading='our Q_p-linear / A(k) automorphisms ARE Ism elements',
         why='it is close and already proved: dozens of real base-field theorems would silently '
             'become claims about the IUT Ism group, and the acknowledged over-approximation '
             'A(k) would collapse into an identification',
         would_misread=['IUTBridge.Admissibility.latticeAdmissible_not_rectangular',
                        'LocalFieldAudit.ContinuousLinearity.map_padic_smul',
                        'IUTBridge.Slots.slotwise_commutes_of_invariant'],
         evidence='research/exploration/definitions-inventory.md (E1 row for Ism); '
                  'research/round3-semantic-audit.md:55; research/round2-source-audit.md:41'),
    dict(id='F-02',
         reading='mono-analytic structure IS holomorphic structure',
         why='the source requires their separation precisely to make the comparison nontrivial; '
             'identifying them deletes the content of the link',
         would_misread=['IUTBridge.Slots.relabel_slotwise'],
         evidence='research/exploration/definitions-inventory.md (E3 row)'),
    dict(id='F-03',
         reading='Theta-link IS a Reindexing / set-theoretic transport',
         why='APT deliberately forbids a set-theoretic identification; Reindexing is a bijection, '
             'i.e. the wrong shape, not an incomplete version of the right one',
         would_misread=['IUTAudit.Transport.transport_projection',
                        'IUTAudit.Transport.transport_comp'],
         evidence='research/exploration/definitions-inventory.md (E4 row); GAP.md:9'),
]

# Ranked by cost/blocker as of this round; each names what it would unblock.
NEXT_TARGETS = [
    dict(rank=0, target='instance : NonarchimedeanRing Q_[p]',
         reason='cheapest unblocking step found this round: it gates HasSum.mul_of_nonarchimedean, '
                'which both log multiplicativity and the Teichmuller homomorphism law need',
         must_keep=['do not add the instance by assuming log exists',
                    'keep it an instance derivation, not a new axiom'],
         unblocks='p-adic log multiplicativity path; Teichmuller hom law'),
    dict(rank=1, target='Ind1-Ind3 as relation-valued allowed operations + a projection equation',
         reason='no library blocker; the toy projection formula already exists as '
                'IUTBridge.Slots.relabel_slotwise',
         must_keep=['Ind3 is a relation, not a group action',
                    'Allowed12 is strictly smaller than all of A(k)',
                    'CompositionClosed is a target to prove, never a hypothesis'],
         unblocks='RI-04 (part of the RI-01/RI-02 assumptions)'),
    dict(rank=2, target='SeededFamily instantiation for the possible-images family',
         reason='the container shape in IUTAudit.Transport.SeededFamily is already right; one '
                'actual Kummer choice c is missing',
         must_keep=['do not widen the family to admit a witness',
                    'membership must be in the original U_j, not in an over-approximation'],
         unblocks='RI-05, the ledger own priority bridge'),
    dict(rank=3, target='log-shell / log_p(O^x): the unblocked half only',
         reason='the base-field discriminator is already a theorem; pass log as an explicit '
                'parameter and prove only what does not need its image',
         must_keep=['log image provenance needs the missing p-adic logarithm',
                    'small ramification (e_v = 105, 35) means 1/e_v != 1: the layer index does '
                    'not transfer unchanged'],
         unblocks='part of RI-06; the image identity itself stays blocked'),
]

# Library-level feasibility, from research/exploration/log-kummer-feasibility.md and from
# probes re-run by the ledger's own author (see independent_checks).
FEASIBILITY = {
    'report': 'research/exploration/log-kummer-feasibility.md',
    'items': [
        dict(item='Q_p^x = Z x Z_p^x', verdict='partial',
             present=['PadicInt.unitCoeff_spec', 'Padic.valuation_mul', 'Padic.valuation_inv'],
             missing='only the bundled MulEquiv; factorization already exists elementwise'),
        dict(item='Z_p^x decomposition', verdict='partial',
             present=['PadicInt.residueField', 'PadicInt.norm_le_pow_iff_mem_span_pow'],
             missing='Teichmuller / rootsOfUnity absent from NumberTheory/Padics/**, although '
                     'hensels_lemma and IsCyclic (ZMod p)^x give the raw material'),
        dict(item='p-adic log / exp', verdict='absent',
             present=['PadicInt.dividedPowers', 'padicValNat_factorial_lt_of_ne_zero',
                      'Padic.nonarchimedean', 'CompleteSpace (Q_p)'],
             missing='any log/exp; and the instance NonarchimedeanRing Q_p, which blocks the '
                     'multiplicativity rearrangement HasSum.mul_of_nonarchimedean'),
        dict(item='Kummer theory (local)', verdict='partial',
             present=['isCyclic_tfae', 'autEquivRootsOfUnity', 'autEquivZmod'],
             missing='nothing about Q_p^x/(Q_p^x)^n; no H1 / KummerTheory / IsKummerExtension'),
        dict(item='ramification / normalization', verdict='exists',
             present=['Ideal.ramificationIdx', 'Ideal.ramificationIdx\'',
                      'Ideal.ramificationIdx\'_eq_ramificationIdx', 'valuation_liesOver'],
             missing='the completion-level restatement: valuation_liesOver is stated for '
                     'height-one spectra of Dedekind domains, not for adicCompletion'),
    ],
    'largest_gap': 'the p-adic logarithm (and its enabling NonarchimedeanRing Q_p): the only '
                   'item where the mathematics, not the interface, is missing',
    'cheapest_next_step': {
        'target': 'instance : NonarchimedeanRing Q_[p]',
        'why': 'it unblocks HasSum.mul_of_nonarchimedean, which gates both log multiplicativity '
               'and the Teichmuller homomorphism law',
        'cost': 'tens of lines from the already-firing IsUltrametricDist / NonarchimedeanAddGroup',
    },
    'cost_verdicts': {
        'Q_p^x decomposition': 'hours', 'Z_p^x residue half': 'hours',
        'Z_p^x Teichmuller half': 'days (plus a separate p = 2 case)',
        'p-adic log': 'weeks 3-6', 'exp': 'additional 2-4 weeks', 'Lubin-Tate': 'implausible',
        'Kummer instantiation': 'days', 'Kummer pairing': 'implausible',
        'ramification lift to Filtration.lean': 'days (2-4)',
    },
    'does_not_establish': 'nothing about IUT, Theta-links or the pilot; "absent" means "not found '
                          'by an import-complete probe plus a source grep", which cannot '
                          'distinguish absence from a deprecation rename',
}

# Probes this ledger's author re-ran independently rather than trusting the report.
INDEPENDENT_CHECKS = [
    dict(claim='PadicInt.unitCoeff_spec exists', result='confirmed',
         command="lake env lean --json ../.agent-notes/probe_feas2.lean"),
    dict(claim='PadicInt.residueField : ResidueField Z_p =+* ZMod p exists',
         result='confirmed (first probe reported it unknown because of a missing import; '
                'import-complete probe confirms it)',
         command='same probe, plus RingHoms.lean:349 grep'),
    dict(claim='Ideal.ramificationIdx and the legacy bridge exist', result='confirmed',
         command='same probe'),
    dict(claim='valuation_liesOver is a fraction-field statement in '
               'IsDedekindDomain.HeightOneSpectrum', result='confirmed by source at '
                                                          'NumberTheory/RamificationInertia/'
                                                          'Valuation.lean:57',
         command='grep of the Mathlib tree'),
    dict(claim='NonarchimedeanRing Q_[p] does not synthesize', result='confirmed',
         command="lake env lean --json ../.agent-notes/probe_feas3.lean -> failed to synthesize"),
    dict(claim='NormedAlgebra Q Q_[p] does not synthesize', result='NOT independently '
                                                                  'confirmed (identifier needs '
                                                                  'another import); reported by '
                                                                  'the feasibility track only',
         command='-'),
]

METHOD_NOTE = ('An "unknown constant" from an under-imported probe proves nothing about absence: '
               'this happened twice in this repository (a name probe in round 6, and this '
               'ledger author\'s own first probe of PadicInt.residueField). Absence claims must '
               'be import-complete plus source-grep, and even then only mean "not found now".')

validated = []
missing_all = []
for entry in ENTRIES:
    missing = [tid for tid in entry['formal'] if tid not in known]
    if missing:
        missing_all.append((entry['id'], missing))
    validated.append({**entry,
                      'evidence_tier': TIERS[entry['id']][0],
                      'evidence_note': TIERS[entry['id']][1],
                      'anchors_missing': missing})

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
                   'swap23_moves_profile', 'excess_is_uniform',
                   'relabel_toPadic', 'swap23_eq_labelAction'],
         value='the valuation vector of the (b1,b1,b2,b1) pattern as an actual object: 4-element '
               'orbit characterised exactly, hull constant at min(v1,v2) (proved without v1 != v2, '
               'stronger than requested), excess exactly slot 2, the label action moves the pattern '
               'while the hull forgets the slot, and relabel_toPadic/iswap23_eq_labelAction tie the '
               'integer action to IUTBridge.Slots.relabel/swap23 by rfl',
         gap='integers standing in for valuations; no places, no pilot, no Theta-link. Verified '
             'independently: CLI zero diagnostics, 10 axiom lines all within '
             '{propext, Classical.choice, Quot.sound}, no sorry/admit/opaque/axiom'),
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
    'forbidden_identifications': FORBIDDEN,
    'next_targets': NEXT_TARGETS,
    'evidence_tier_legend': {
        'E1': 'definition recorded in local evidence and statable',
        'E2': 'construction locators only; no data list recorded',
        'E3': 'role recorded, definition absent',
        'E4': 'wholly absent; only negative characterisations',
    },
    'companion_evidence': {k: v for k, v in COMPANION.items() if (ROOT / v).exists()},
    'feasibility': FEASIBILITY,
    'independent_checks': INDEPENDENT_CHECKS,
    'method_note': METHOD_NOTE,
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
