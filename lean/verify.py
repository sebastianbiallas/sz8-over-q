#!/usr/bin/env python3
"""Check generated sources, build Sz8.Monodromy and then all of Sz8, and audit the proof dependencies."""
import json
from pathlib import Path
import re
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_NAMES = {"Sz8.Monodromy." + name for name in (
    # Modular factorizations.
    "modular_certificate_11", "modular_certificate_31",
    "factorization_11", "factorization_31", "irreducible_11", "irreducible_31",
    "squarefree_11", "squarefree_31", "degrees_11", "degrees_31",
    # Continuation.
    "inputs_agree", "continuation_step_one", "paper_one_root_during_step", "paper_real_segment",
    # The specialization f(X, -7/5) over Q and its Galois group.
    "paperSpecialization_monic_natDegree", "natDegree_dvd_card_gal",
    "seven_dvd_card_gal", "thirteen_dvd_card_gal", "ninetyOne_dvd_card_gal",
    "card_gal_ge_ninetyOne", "paperSpecialization_irreducible", "paperSpecialization_separable",
    "sixtyFive_dvd_card_gal", "fourHundredFiftyFive_dvd_card_gal",
    # The continuation family and the specialization are the same polynomial.
    "paperFamily_eq_sparse", "paperFamily_specialization",
    "paperFamily_specialization_separable",
    # Root covering and certified transport (Mathlib covering-space monodromy).
    "MonicFamily.isCoveringMapOn_proj", "MonicFamily.monodromy_root_mem_ball",
    "MonicFamily.monodromy_eq_of_ball", "MonicFamily.monodromy_trans",
    "paperFamily_monic", "paper_isCoveringMap",
    # Recorded meridian permutations: orders and fixed points.
    "σ₁_pow_three", "σ₁_fixed", "σ₂_pow_three", "σ₂_fixed", "σ₁σ₂_pow_thirteen", "σ₁σ₂_fixed",
    # Rouché step certificates, Kronecker-packed replay, and one real 65-root step.
    "GaussPoly.discCheck_sound", "GaussPoly.discCheck_of_packedCheck", "stepCertified_of_checks", "regular_of_discs", "paperFamily_eq_famPoly", "step0_certified",
    "step_monodromy", "junction",
    # The product check (Taylor shift as one correlation) and its step certificates.
    "GaussPoly.conv_coeff", "GaussPoly.discCheck_of_convCheck", "stepCertified_of_conv",
    "StepDatum.cert_of_conv",
    # Chains of certified steps, mirror certificates, and the two certified meridians.
    "junctionB_of_junctionG", "Chain.chain_root", "Chain.loop_monodromy", "StepDatum.Cert.conj",
    "Meridian1.zero_regular", "Meridian1.monodromy_γ₁", "Meridian1.meridian_monodromy",
    # Stabilizer-chain order certificates for the recorded permutation group, the
    # Sylow/word certificates behind the order-91 step, and the normalizer search.
    "card_closure_sigma", "commutator_eq", "card_commutator_sigma",
    "Nstab01", "eq_of_ninetyOne_dvd", "mem_of_fixes01", "normalizer_eq")} | {
    # Sz8.Galois: the topology behind meridian generation — the generation half of Seifert-van
    # Kampen, the lift index, the two-puncture generation theorem, the descent (grid) argument and
    # the node-filling theorem.
    "Sz8.Galois.vanKampen_generation", "Sz8.Galois.liftIndex_mul", "Sz8.Galois.liftIndex_inv",
    "Sz8.Galois.liftIndex_circleLoop", "Sz8.Galois.zpowers_eq_top_of_abs_liftIndex",
    "Sz8.Galois.Circuit.circuit_liftIndex", "Sz8.Galois.Circuit.circuit_zpowers_eq_top",
    "Sz8.Galois.Retract.map_incl_injective", "Sz8.Galois.Retract.zpowers_eq_top_of_map_incl",
    "Sz8.Galois.PolyIndex.liftIndex_loopC", "Sz8.Galois.TwoPunctures.polylines_generate",
    "Sz8.Galois.Descent.kernel_descent", "Sz8.Galois.Filling.Setup.range_eq_closure",
    # M2 at the nodes: the fixed Sylvester minor and its transfer from residue witnesses mod p.
    "Sz8.Galois.FixedMinor.B_ne_zero_iff", "Sz8.Galois.FixedMinor.rootMultiplicity_of_B_ne_zero",
    "Sz8.Galois.FixedMinor.node_multiplicity", "Sz8.Galois.PackedWitness.witness_of_packed",
    "Sz8.Galois.NodeAlgebra.resultant_mul_derivative",
    "Sz8.Galois.NodeAlgebra.resultant_quadratic_derivative",
    # The integer model F̃ = 13^182 f, and M2 at every root of S̃ with no remaining hypotheses.
    "Sz8.Galois.FLink.P_eq_Ftil", "Sz8.Galois.FLink.resultant_Ftil", "Sz8.Galois.FLink.B_Ftil",
    "Sz8.Galois.NodeM2.node_M2", "Sz8.Galois.NodeLocal.local_monodromy_trivial",
    # The resultant identity and the node separation it gives.
    "Sz8.Galois.ResAlg.res_eq", "Sz8.Galois.ResEval.identity", "Sz8.Galois.NodeSep.derivative_ne_of_root",
    "Sz8.Galois.NodeSep.q_ne_of_root", "Sz8.Galois.Nodes.regular_compl", "Sz8.Galois.Nodes.nodesS_card",
    "Sz8.Galois.Nodes.nodes_eq_nodesS", "Sz8.Galois.Nodes.node_local",
    # Geometric Galois group normal in the arithmetic one: general descent and relative normality.
    "Sz8.Galois.GaloisDescent.res_range_normal",
    "Sz8.Galois.GaloisDescent.geometric_normal_in_arithmetic_of_rel",
    "Sz8.Galois.RelNormal.mem_adjoin", "Sz8.Galois.RelNormal.relNormal",
    # Analytic bridge, first pieces: Lemma L (polynomial growth) and holomorphic root branches.
    "Sz8.Galois.PolyGrowth.eq_polynomial_of_growth", "Sz8.Galois.RootAnalytic.differentiableAt_of_root",
    "Sz8.Galois.RootAnalytic.analyticOnNhd_of_root",
    # Germ field, (S), (R) and the bridge assembly.
    "Sz8.Galois.Germs.splits_rootGerm", "Sz8.Galois.Germs.rootGerm_injective",
    "Sz8.Galois.Germs.polyGerm_le", "Sz8.Galois.Continuation.continue_along",
    "Sz8.Galois.Continuation.continue_monodromy", "Sz8.Galois.Relations.relations_monodromy",
    "Sz8.Galois.Bridge.mem_image_iff", "Sz8.Galois.Bridge.bridge",
    # (O), first checkpoint: the orbit polynomial on the regular locus.
    "Sz8.Galois.Orbit.monodromy_eq_comp",
    "Sz8.Galois.Orbit.orbitPolyOf_indep",
    "Sz8.Galois.Orbit.orbitPoly_local",
    "Sz8.Galois.Orbit.orbitCoeff_analyticAt",
    "Sz8.Galois.Orbit.orbitCoeff_analyticOnNhd",
    "Sz8.Galois.Orbit.exists_separating",
    "Sz8.Galois.Orbit.regular_compl_finite",
    "Sz8.Galois.Orbit.regular_isPathConnected",
    # (O), second checkpoint: polynomial coefficients and the assembled orbit polynomial.
    "Sz8.Galois.OrbitPoly.norm_coeff_prod_le",
    "Sz8.Galois.OrbitPoly.norm_orbitCoeff_le",
    "Sz8.Galois.OrbitPoly.exists_root_growth",
    "Sz8.Galois.OrbitPoly.exists_orbitCoeff_poly",
    "Sz8.Galois.OrbitPoly.orbitPhi_spec",
    # (O) closed: the analytic bridge and the generic theorem are sorry-free.
    "Sz8.Galois.Converse.orbitPhi_germ",
    "Sz8.Galois.Converse.converse",
    "Sz8.Galois.monodromy_eq_geometric_galois",
    "Sz8.Galois.generic_galois",
    # Cubic identification, infinity input: stabilizer bounds and the first Newton edge.
    "Sz8.Galois.Stab13.card_stabilizer_pair_le",
    "Sz8.Galois.Stab13.card_stabilizer_set_le",
    "Sz8.Galois.Stab13.stab_le",
    "Sz8.Galois.Stab13.orbit_stable",
    "Sz8.Galois.Stab13.orbit_cover",
    "Sz8.Galois.FirstEdge.units_map_residue",
    "Sz8.Galois.FirstEdge.exists_primitive_ratio",
    "Sz8.Galois.FirstEdge.specialize_zero",
    "Sz8.Galois.FirstEdge.Fτ_eval",
    "Sz8.Galois.FirstEdge.Fτ_monic",
    # Specialization into the decomposition group: general theorem and the family.
    "Sz8.Galois.Specialize.exists_decomposition",
    "Sz8.Galois.Specialize.image_le_decomposition",
    "Sz8.Galois.Specialize.smul_eq_self_of_residue",
    "Sz8.Galois.SpecFamily.fQ_monic",
    "Sz8.Galois.SpecFamily.fQ_spec",
    "Sz8.Galois.specialization_le_decomposition",
    # Split witnesses bound the decomposition group.
    "Sz8.Galois.Specialize.smul_eq_self_of_split",
    "Sz8.Galois.decomposition_le_of_split_witness",
    # The relative invariant of N in G and its resolvent data.
    "Sz8.Galois.Resolvent.Θ_mul_mem",
    "Sz8.Galois.Resolvent.map_Θ",
    "Sz8.Galois.Resolvent.exists_pow_mul",
    "Sz8.Galois.Resolvent.disc_eq",
    "Sz8.Galois.Resolvent.Rs_monic",
    "Sz8.Galois.Resolvent.Rs_fibre",
    "Sz8.Galois.Resolvent.disc_eval_zero_ne",
    "Sz8.Galois.Resolvent.eq_of_pins",
    "Sz8.Galois.Resolvent.Z1_natDegree",
    "Sz8.Galois.Resolvent.Z2_natDegree",
    "Sz8.Galois.Resolvent.Z3_natDegree",
    # (R2) the degree bound at infinity.
    "Sz8.Galois.DegreeBound.isIntegralElem_root",
    "Sz8.Galois.DegreeBound.isIntegralElem_Θ",
    "Sz8.Galois.DegreeBound.natDegree_le_of_isIntegralElem",
    "Sz8.Galois.sym_natDegree_le",
    # (R1) integer polynomials.
    "Sz8.Galois.IntModel.terms_ok",
    "Sz8.Galois.IntModel.fZ_monic",
    "Sz8.Galois.IntModel.fZ_eval",
    "Sz8.Galois.IntModel.int_of_isIntegral",
    "Sz8.Galois.IntModel.isIntegralElem_Θ",
    "Sz8.Galois.Resolvent.exists_perm_pow_mul",
    "Sz8.Galois.sigma1_not_mem_N",
    "Sz8.Galois.sym_int",
    # The germ link: consumer for (R3) and non-vacuity.
    "Sz8.Galois.map_symOf",
    "Sz8.Galois.sym_eval_of_link",
    "Sz8.Galois.exists_disc_roots",
    # Germ link, steps 1-3: labelled bridge, labelled descent, labelled meridians.
    "Sz8.Galois.meridian_monodromy_labelled",
    "Sz8.Galois.generic_galois_labelled",
    # Germ link, steps 4-6: germs to functions, disc roots analytic, identity theorem.
    "Sz8.Galois.GermEval.eventually_eval_eq_zero",
    "Sz8.Galois.GermEval.analyticAt_eval₂",
    "Sz8.Galois.disc_root_unique",
    "Sz8.Galois.disc_root_analyticAt",
    "Sz8.Galois.germ_link",
    # (R3) preparation: pinning points and the invariant through the chain of N.
    "Sz8.Galois.Pinning.pins_of_inverse",
    "Sz8.Galois.Pinning.pins",
    "Sz8.Galois.Pinning.r_small",
    "Sz8.Galois.NSum.sum_lclosure",
    "Sz8.Galois.NSum.sum_mono_grouped",
    "Sz8.Galois.Θ_eq_grouped",
    # (R3) root enclosures: exact evaluation, product over disc roots, data at t = 1/2048.
    "Sz8.Galois.Enclose.encCheck_sound",
    "Sz8.Galois.EncData4.checks",
    "Sz8.Galois.norm_eval_eq_prod",
    "Sz8.Galois.enclose",
    "Sz8.Galois.enclose_disc_root",
    "Sz8.Galois.enclosures_point4",
    # (R3) values at the seven pinning points, and the final theorems (now sorry-free).
    "Sz8.Galois.Lipschitz.norm_Θ_sub_le",
    "Sz8.Galois.Lipschitz.norm_Θ_le",
    "Sz8.Galois.Lipschitz.norm_sym3_sub_le",
    "Sz8.Galois.ThetaEval.gc_thetaGI",
    "Sz8.Galois.PointBound.point_bound",
    "Sz8.Galois.ZList.aeval_Z",
    "Sz8.Galois.near_point",
    "Sz8.Galois.EncData0.checks",
    "Sz8.Galois.EncData1.checks",
    "Sz8.Galois.EncData2.checks",
    "Sz8.Galois.EncData3.checks",
    "Sz8.Galois.EncData5.checks",
    "Sz8.Galois.EncData6.checks",
    "Sz8.Galois.ThetaData0.symChecks",
    "Sz8.Galois.ThetaData1.symChecks",
    "Sz8.Galois.ThetaData2.symChecks",
    "Sz8.Galois.ThetaData3.symChecks",
    "Sz8.Galois.ThetaData4.symChecks",
    "Sz8.Galois.ThetaData5.symChecks",
    "Sz8.Galois.ThetaData6.symChecks",
    "Sz8.Galois.sym_near",
    "Sz8.Galois.resolvent_identity",
    "Sz8.Galois.decomposition_le_N",
    "Sz8.Galois.specialization_embeds",
    "Sz8.Galois.gal_specialization_eq_N",
    "Sz8.Galois.card_gal_specialization",
    # Toward N ≃ Sz(8): the field of order 8, Suzuki's generators, the ovoid.
    "Sz8.Galois.Suzuki.θ8_sq",
    "Sz8.Galois.Suzuki.det_Tmat",
    "Sz8.Galois.Suzuki.det_Mmat",
    "Sz8.Galois.Suzuki.det_Wmat",
    "Sz8.Galois.Suzuki.ovoid_card",
    "Sz8.Galois.Suzuki.ovoid_stable",
    # N ≃ Sz(8): the ovoid action is injective (frame) with image N (sift + words).
    "Sz8.Galois.Suzuki.eq_scalar_of_frame",
    "Sz8.Galois.Suzuki.ψ_injective",
    "Sz8.Galois.Suzuki.siftOK",
    "Sz8.Galois.Suzuki.word1OK",
    "Sz8.Galois.Suzuki.word2OK",
    "Sz8.Galois.Suzuki.suzuki_le_presSub",
    "Sz8.Galois.Suzuki.φ_injective",
    "Sz8.Galois.Suzuki.range_φ",
    "Sz8.Galois.Suzuki.suzukiEquiv",
    "Sz8.Galois.N_equiv_suzuki",
    "Sz8.Galois.gal_specialization_equiv_suzuki"}
NEGATIVE_TESTS = 20


def check_no_sorry(output):
    """A library build must not report any declaration that uses `sorry`."""
    found = re.findall(r"([\w/.]+\.lean):(\d+):\d+: declaration uses `sorry`", output)
    if found:
        raise ValueError(f"Declarations using sorry: {found}")


def check_axioms(output):
    axioms = {}
    for name, deps in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output):
        if name in axioms:
            raise ValueError(f"Duplicate audit result: {name}")
        axioms[name] = sorted({a.strip() for a in deps.split(",") if a.strip()})
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        if name in axioms:
            raise ValueError(f"Duplicate audit result: {name}")
        axioms[name] = []
    if set(axioms) != EXPECTED_NAMES:
        raise ValueError(f"Unexpected/missing audit declarations: {set(axioms) ^ EXPECTED_NAMES}")
    for name, deps in axioms.items():
        extra = set(deps) - ALLOWED_AXIOMS
        if extra:
            raise ValueError(f"Unexpected proof dependencies for {name}: {extra}")
    passed = output.count("negative certificate test passed")
    if passed != NEGATIVE_TESTS:
        raise ValueError(f"Expected {NEGATIVE_TESTS} rejected certificates, saw {passed}")
    return axioms


def main():
    commands = [[sys.executable, "-m", "unittest", "test_verify.py", "test_export_provenance.py"],
                [sys.executable, "export_inputs.py", "--check"],
                [sys.executable, "export_step.py", "--check"],
                [sys.executable, "export_monodromy.py", "--check"],
                [sys.executable, "export_groups.py", "--check"],
                [sys.executable, "export_sylow.py", "--check"],
                [sys.executable, "export_normalizer.py", "--check"],
                [sys.executable, "export_continuation.py", "--check"],
                [sys.executable, "export_meridian.py", "emit", "--check"],
                [sys.executable, "export_galois.py", "--check"],
                [sys.executable, "tools/generate.py", "--check"],
                ["sh", "run-lake.sh", "build", "Sz8.Monodromy"],
                ["sh", "run-lake.sh", "build", "Sz8"],
                ["sh", "run-lake.sh", "env", "lean", "Audit.lean"]]
    report = {"success": False, "commands": [], "axioms": {},
              "trust": "Kernel-only: every audited theorem uses at most propext, Classical.choice, Quot.sound."}
    logs = []
    for command in commands:
        shown = ["python3" if part == sys.executable else part for part in command]
        print("Running:", " ".join(shown), flush=True)
        started = time.monotonic()
        result = subprocess.run(command, cwd=HERE, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        report["commands"].append({"command": shown, "exit_code": result.returncode,
                                   "seconds": round(time.monotonic() - started, 3)})
        logs.append("$ " + " ".join(shown) + "\n" + result.stdout)
        print(result.stdout, end="", flush=True)
        if result.returncode:
            break
        if command[1:3] == ["run-lake.sh", "build"]:
            try:
                check_no_sorry(result.stdout)
            except ValueError as error:
                report["audit_error"] = str(error)
                print(error, file=sys.stderr)
                break
        if command[-1] == "Audit.lean":
            try:
                report["axioms"] = check_axioms(result.stdout)
            except ValueError as error:
                report["audit_error"] = str(error)
                print(error, file=sys.stderr)
                break
            report["success"] = True
    (HERE / "verification.log").write_text("\n".join(logs))
    (HERE / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    if not report["success"]:
        raise SystemExit(1)
    print("All checks passed: Sz8 builds without sorry, and no audited theorem uses native "
          "evaluation or sorry.")


if __name__ == "__main__":
    main()
