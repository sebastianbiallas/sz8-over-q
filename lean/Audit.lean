import Sz8.Monodromy
import Sz8.Galois.VanKampen
import Sz8.Galois.LiftIndex
import Sz8.Galois.Circuit
import Sz8.Galois.Retract
import Sz8.Galois.TwoPunctures
import Sz8.Galois.Descent
import Sz8.Galois.Filling
import Sz8.Galois.ModTransfer
import Sz8.Galois.PackedWitness
import Sz8.Galois.NodeAlgebra
import Sz8.Galois.NodeM2
import Sz8.Galois.NodeLocal
import Sz8.Galois.Identity
import Sz8.Galois.GaloisDescent
import Sz8.Galois.RelNormal
import Sz8.Galois.PolyGrowth
import Sz8.Galois.RootAnalytic
import Sz8.Galois.Bridge
import Sz8.Galois.Orbit
import Sz8.Galois.OrbitPoly
import Sz8.Galois.Converse
import Sz8.Galois.MainTheorem
import Sz8.Galois.Stab13
import Sz8.Galois.FirstEdge
import Sz8.Galois.Specialize
import Sz8.Galois.SpecFamily
import Sz8.Galois.Resolvent
import Sz8.Galois.DegreeBound
import Sz8.Galois.IntModel
import Sz8.Galois.GermEval
import Sz8.Galois.NSum
import Sz8.Galois.Pinning
import Sz8.Galois.Enclose
import Sz8.Galois.Lipschitz
import Sz8.Galois.ThetaEval
import Sz8.Galois.PointBound
import Sz8.Galois.ZList
import Sz8.Galois.Suzuki
import Sz8.Galois.SuzukiGalois
import Sz8.Galois.EncData0
import Sz8.Galois.ThetaData0
import Sz8.Galois.EncData1
import Sz8.Galois.ThetaData1
import Sz8.Galois.EncData2
import Sz8.Galois.ThetaData2
import Sz8.Galois.EncData3
import Sz8.Galois.ThetaData3
import Sz8.Galois.EncData4
import Sz8.Galois.ThetaData4
import Sz8.Galois.EncData5
import Sz8.Galois.ThetaData5
import Sz8.Galois.EncData6
import Sz8.Galois.ThetaData6

#print axioms Sz8.Monodromy.modular_certificate_11
#print axioms Sz8.Monodromy.modular_certificate_31
#print axioms Sz8.Monodromy.factorization_11
#print axioms Sz8.Monodromy.factorization_31
#print axioms Sz8.Monodromy.irreducible_11
#print axioms Sz8.Monodromy.irreducible_31
#print axioms Sz8.Monodromy.squarefree_11
#print axioms Sz8.Monodromy.squarefree_31
#print axioms Sz8.Monodromy.degrees_11
#print axioms Sz8.Monodromy.degrees_31
#print axioms Sz8.Monodromy.inputs_agree
#print axioms Sz8.Monodromy.continuation_step_one
#print axioms Sz8.Monodromy.paper_one_root_during_step
#print axioms Sz8.Monodromy.paper_real_segment
#print axioms Sz8.Monodromy.paperSpecialization_monic_natDegree
#print axioms Sz8.Monodromy.natDegree_dvd_card_gal
#print axioms Sz8.Monodromy.seven_dvd_card_gal
#print axioms Sz8.Monodromy.thirteen_dvd_card_gal
#print axioms Sz8.Monodromy.ninetyOne_dvd_card_gal
#print axioms Sz8.Monodromy.card_gal_ge_ninetyOne
#print axioms Sz8.Monodromy.paperSpecialization_irreducible
#print axioms Sz8.Monodromy.paperSpecialization_separable
#print axioms Sz8.Monodromy.sixtyFive_dvd_card_gal
#print axioms Sz8.Monodromy.fourHundredFiftyFive_dvd_card_gal
#print axioms Sz8.Monodromy.paperFamily_eq_sparse
#print axioms Sz8.Monodromy.paperFamily_specialization
#print axioms Sz8.Monodromy.paperFamily_specialization_separable
#print axioms Sz8.Monodromy.MonicFamily.isCoveringMapOn_proj
#print axioms Sz8.Monodromy.MonicFamily.monodromy_root_mem_ball
#print axioms Sz8.Monodromy.MonicFamily.monodromy_eq_of_ball
#print axioms Sz8.Monodromy.MonicFamily.monodromy_trans
#print axioms Sz8.Monodromy.paperFamily_monic
#print axioms Sz8.Monodromy.paper_isCoveringMap
#print axioms Sz8.Monodromy.σ₁_pow_three
#print axioms Sz8.Monodromy.σ₁_fixed
#print axioms Sz8.Monodromy.σ₂_pow_three
#print axioms Sz8.Monodromy.σ₂_fixed
#print axioms Sz8.Monodromy.σ₁σ₂_pow_thirteen
#print axioms Sz8.Monodromy.σ₁σ₂_fixed
#print axioms Sz8.Monodromy.GaussPoly.discCheck_sound
#print axioms Sz8.Monodromy.GaussPoly.discCheck_of_packedCheck
#print axioms Sz8.Monodromy.stepCertified_of_checks
#print axioms Sz8.Monodromy.regular_of_discs
#print axioms Sz8.Monodromy.paperFamily_eq_famPoly
#print axioms Sz8.Monodromy.step0_certified
#print axioms Sz8.Monodromy.step_monodromy
#print axioms Sz8.Monodromy.junction
#print axioms Sz8.Monodromy.GaussPoly.conv_coeff
#print axioms Sz8.Monodromy.GaussPoly.discCheck_of_convCheck
#print axioms Sz8.Monodromy.stepCertified_of_conv
#print axioms Sz8.Monodromy.StepDatum.cert_of_conv
#print axioms Sz8.Monodromy.junctionB_of_junctionG
#print axioms Sz8.Monodromy.Chain.chain_root
#print axioms Sz8.Monodromy.Chain.loop_monodromy
#print axioms Sz8.Monodromy.StepDatum.Cert.conj
#print axioms Sz8.Monodromy.Meridian1.zero_regular
#print axioms Sz8.Monodromy.Meridian1.monodromy_γ₁
#print axioms Sz8.Monodromy.Meridian1.meridian_monodromy
#print axioms Sz8.Monodromy.card_closure_sigma
#print axioms Sz8.Monodromy.commutator_eq
#print axioms Sz8.Monodromy.card_commutator_sigma
#print axioms Sz8.Monodromy.Nstab01
#print axioms Sz8.Monodromy.eq_of_ninetyOne_dvd
#print axioms Sz8.Monodromy.mem_of_fixes01
#print axioms Sz8.Monodromy.normalizer_eq

/-! Negative certificate tests: the kernel checker must reject corrupted or
reducible data. verify.py requires every success message below. -/
-- The topology behind meridian generation: the generation half of Seifert-van Kampen.
#print axioms Sz8.Galois.vanKampen_generation

-- The lift index: composition and reversal laws, and index 1 for the positively oriented circle.
#print axioms Sz8.Galois.liftIndex_mul
#print axioms Sz8.Galois.liftIndex_inv
#print axioms Sz8.Galois.liftIndex_circleLoop
#print axioms Sz8.Galois.zpowers_eq_top_of_abs_liftIndex
-- The recorded 145-edge circuit of the first meridian has index 1 about zeta_3, and generates.
#print axioms Sz8.Galois.Circuit.circuit_liftIndex
#print axioms Sz8.Galois.Circuit.circuit_zpowers_eq_top
-- A punctured convex set containing the unit disc about the puncture: the inclusion into the
-- punctured plane is injective on fundamental groups, so generation pulls back.
#print axioms Sz8.Galois.Retract.map_incl_injective
#print axioms Sz8.Galois.Retract.zpowers_eq_top_of_map_incl
-- A certified left-nested polyline has index 1 (segment-wise lift, no regrouping),
-- and the two recorded complex polylines generate pi_1 of the twice-punctured plane.
#print axioms Sz8.Galois.PolyIndex.liftIndex_loopC
#print axioms Sz8.Galois.TwoPunctures.polylines_generate

section NegativeTests
open Sz8.Monodromy Sz8.Monodromy.ListPoly

private def firstCert31 : RabinCert :=
  certs31.headD { low := [], qB := [], B := [], Ms := [], qs := [] }

-- Wrong polynomial: one coefficient of the degree-13 factor changed.
example : checkRabin 31 { firstCert31 with low := firstCert31.low.set 0 16 } = false := by
  decide +kernel
#eval IO.println "negative certificate test passed"

-- Wrong Frobenius data: one coefficient of X^31 mod P changed.
example : checkRabin 31 { firstCert31 with B := firstCert31.B.set 0 3 } = false := by
  decide +kernel
#eval IO.println "negative certificate test passed"

/-- (irreducible cubic) * (irreducible quartic) over F_11, with honest FLINT data. -/
private def cubicQuartic : RabinCert :=
  { low := [1, 0, 4, 5, 1, 5, 8]
    qB := [4, 7, 4, 3, 1]
    B := [7, 4, 2, 4, 10, 7, 9]
    Ms := [[7, 4, 2, 4, 10, 7, 9], [9, 10, 4, 0, 6, 10, 2], [4, 10, 2, 9, 3, 8, 2],
      [10, 10, 0, 6, 6, 6], [7, 8, 6, 1, 8, 9, 10], [3, 3, 3, 2, 6, 2]]
    qs := [[], [7, 2, 1, 7, 6, 4], [4, 8, 2, 0, 4, 7], [7, 10, 1, 4, 8, 7], [8, 3, 0, 5, 10],
      [2, 4, 0, 3, 3, 2]] }

-- Its multiplication certificates replay, but X^(11^7) is not X modulo it.
example : chainOK 11 (cubicQuartic.low ++ [1]) cubicQuartic.B [1] cubicQuartic.Ms
    cubicQuartic.qs = true := by decide +kernel
example : frobCheck 11 ([1] :: cubicQuartic.Ms) 7 [0, 1] = false := by decide +kernel
example : checkRabin 11 cubicQuartic = false := by decide +kernel
#eval IO.println "negative certificate test passed"

/-- X (X-1) ... (X-6) over F_11, with honest FLINT data. -/
private def sevenLinear : RabinCert :=
  { low := [0, 5, 7, 7, 2, 10, 1]
    qB := [2, 6, 2, 10, 1]
    B := [0, 1]
    Ms := [[0, 1], [0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1],
      [0, 0, 0, 0, 0, 0, 1]]
    qs := [[], [], [], [], [], []] }

-- It divides X^(11^7) - X, so only the root check can reject it; it does.
example : frobCheck 11 ([1] :: sevenLinear.Ms) 7 [0, 1] = true := by decide +kernel
example : checkRabin 11 sevenLinear = false := by decide +kernel
#eval IO.println "negative certificate test passed"

-- Degrees outside the declared prime list are rejected.
example : checkCerts 11 [13] certs11 = false := by decide +kernel
#eval IO.println "negative certificate test passed"

-- A wrong junction map is rejected: swapping two labels of the base step.
example : junctionB Meridian1.s0 Meridian1.s0 [1, 0] = false := by decide +kernel
#eval IO.println "negative certificate test passed"

-- The same wrong junction map is rejected by the gap-inclusion check.
example : junctionG Meridian1.s0 Meridian1.s0 [1, 0] = false := by decide +kernel
#eval IO.println "negative certificate test passed"

-- An inflated gap is rejected: the gap of disc 0 of the base step, plus one.
example : gapsOK Meridian1.s0sl.flatten (Meridian1.s0g.set 0 (Meridian1.s0g.getD 0 0 + 1)) = false := by
  decide +kernel
#eval IO.println "negative certificate test passed"

-- An overlong step is rejected: base discs 0–4 with the parameter radius quadrupled.
example : sliceCheck 40 20 2645 (0, 0) (4 * 2634246607) Meridian1.s0d0 = false := by decide +kernel
#eval IO.println "negative certificate test passed"

-- The same overlong step is rejected by the product check.
example : convSlice 40 20 4096 (0, 0) (4 * 2634246607) Meridian1.s0d0 = false := by decide +kernel
#eval IO.println "negative certificate test passed"

-- Too narrow digits are rejected by the a-priori bound (3000 bits; about 4084 are needed).
example : convPre 40 20 3000 (0, 0) 65353455 Meridian1.s0sl.flatten = false := by decide +kernel
#eval IO.println "negative certificate test passed"

-- A shrunken orbit is rejected: the orbit list must be closed under the generators.
example : (Ggens0.all fun s => Gorb0.dropLast.all fun o => decide (s o ∈ Gorb0.dropLast))
    = false := by decide +kernel
#eval IO.println "negative certificate test passed"

-- A corrupted transversal word is rejected.
example : ((Gtvw0.set 1 ((Gtvw0.getD 1 (1, [])).1, [])).all fun z =>
    decide (z.1 = wordProd Ggens0 z.2)) = false := by decide +kernel
#eval IO.println "negative certificate test passed"

/-- The level-0 Schreier check of the chain for `G`, as a Boolean. -/
private def schreierBool (cert : List (ℕ × Fin 65 × ℕ × ℕ)) : Bool :=
  cert.all fun z => decide (getAt Gtv0 Gorb0 (Ggens0.getD z.1 1 z.2.1) *
    (Gtv1.getD z.2.2.1 1 * Gtv2.getD z.2.2.2 1) = Ggens0.getD z.1 1 * getAt Gtv0 Gorb0 z.2.1)

-- A wrong sift witness for a Schreier generator is rejected: entry 7 needs the transversal
-- element of index 1 at the next level, not the identity.
example : schreierBool (Gcert0.set 7 (0, 55, 0, 0)) = false := by decide +kernel
#eval IO.println "negative certificate test passed"

/-- The pair-table check of `Sz8.Monodromy.NinetyOneCerts`, as a Boolean. -/
private def tabBool (T : List (Fin 65 × Fin 65 × ℕ × ℕ)) : Bool :=
  T.all fun z => decide (z.1 = z.2.1 ∨
    (z.2.2.1 < Wdata.length ∧ z.2.2.2 < RepData.length ∧
      tabQ z (tabW z z.1) = tabW z z.1 ∧ tabQ z (tabW z z.2.1) = tabW z z.2.1))

-- A wrong table entry is rejected: the pair `(0, 2)` is moved by `Wdata` entry 0 onto the
-- representative pair of `RepData` entry 1, not that of entry 0.
example : tabBool [((0 : Fin 65), (2 : Fin 65), (0 : ℕ), (0 : ℕ))] = false := by
  decide +kernel
#eval IO.println "negative certificate test passed"

-- A wrong conjugation power is rejected: `Wdata` entry 3 sends `Pc` to `Pc ^ 12`, not to `Pc`.
example : (([(Wp3, 0, 0, 0, 1)] : List (Equiv.Perm (Fin 65) × ℕ × ℕ × ℕ × ℕ)).all fun z =>
    decide (z.1⁻¹ * Pc * z.1 = Pc ^ z.2.2.2.2)) = false := by decide +kernel
#eval IO.println "negative certificate test passed"

-- A truncated word is rejected: the recorded word for the first representative is needed in
-- full to reach the first generator of `N`.
example : decide (Nc1 = wordProd [Pc, Pc⁻¹, Rq0, Rq0⁻¹]
    (List.dropLast (List.getD RepData 0 rdflt).2.2.2.2.1)) = false := by decide +kernel
#eval IO.println "negative certificate test passed"

/-- The orbit labelling of `Sz8.Monodromy.NormalizerCerts`, with the label of point `2` changed. -/
private def orbBad (z : Fin 65) : ℕ := ((orbP + 64) >>> (3 * z.val)) % 8

-- A corrupted orbit labelling is rejected: it is no longer constant on the orbits of the
-- two-point stabiliser.
example : (Ggens2.all fun g => (List.finRange 65).all fun z =>
    decide (orbBad (g z) = orbBad z)) = false := by decide +kernel
#eval IO.println "negative certificate test passed"

private def wiOf (T : List (ℕ × List ℕ)) (z : Fin 65) : ℕ := (T.getD z.val (0, [])).1
private def wwOf (T : List (ℕ × List ℕ)) (z : Fin 65) : List ℕ := (T.getD z.val (0, [])).2

-- A corrupted word table is rejected: point `5` is the base of the fourth orbit, not the first.
example : ((List.finRange 65).all fun z => decide (z = wordProd Ggens2
    (wwOf (Wtab.set 5 (0, [])) z) (Xp.getD (wiOf (Wtab.set 5 (0, [])) z) 0))) = false := by
  decide +kernel
#eval IO.println "negative certificate test passed"

-- A missing search witness is rejected: the first row of the first level needs the pair
-- `(2, 1)` to rule out its candidate image.
example : (((Lv0_0.set 0 ((0 : Fin 65), (0 : Fin 65), (0 : Fin 65))).all fun r =>
    decide (r.1 = (2 : Fin 65)) ||
      rowOK wi ww orbAt tv1 AB0 [r.1, 0, 0, 0, 0, 1, 0] 0 Gorb1 1 r.2.1 r.2.2)) = false := by
  decide +kernel
#eval IO.println "negative certificate test passed"

end NegativeTests
#print axioms Sz8.Galois.Descent.kernel_descent
#print axioms Sz8.Galois.Filling.Setup.range_eq_closure
#print axioms Sz8.Galois.FixedMinor.B_ne_zero_iff
#print axioms Sz8.Galois.FixedMinor.rootMultiplicity_of_B_ne_zero
#print axioms Sz8.Galois.FixedMinor.node_multiplicity
#print axioms Sz8.Galois.PackedWitness.witness_of_packed
#print axioms Sz8.Galois.NodeAlgebra.resultant_mul_derivative
#print axioms Sz8.Galois.NodeAlgebra.resultant_quadratic_derivative
#print axioms Sz8.Galois.FLink.P_eq_Ftil
#print axioms Sz8.Galois.FLink.resultant_Ftil
#print axioms Sz8.Galois.FLink.B_Ftil
#print axioms Sz8.Galois.NodeM2.node_M2
#print axioms Sz8.Galois.NodeLocal.local_monodromy_trivial
#print axioms Sz8.Galois.ResAlg.res_eq
#print axioms Sz8.Galois.ResEval.identity
#print axioms Sz8.Galois.NodeSep.derivative_ne_of_root
#print axioms Sz8.Galois.NodeSep.q_ne_of_root
#print axioms Sz8.Galois.Nodes.regular_compl
#print axioms Sz8.Galois.Nodes.nodesS_card
#print axioms Sz8.Galois.Nodes.nodes_eq_nodesS
#print axioms Sz8.Galois.Nodes.node_local
#print axioms Sz8.Galois.GaloisDescent.res_range_normal
#print axioms Sz8.Galois.GaloisDescent.geometric_normal_in_arithmetic_of_rel
#print axioms Sz8.Galois.RelNormal.mem_adjoin
#print axioms Sz8.Galois.RelNormal.relNormal
#print axioms Sz8.Galois.PolyGrowth.eq_polynomial_of_growth
#print axioms Sz8.Galois.RootAnalytic.differentiableAt_of_root
#print axioms Sz8.Galois.RootAnalytic.analyticOnNhd_of_root
#print axioms Sz8.Galois.Germs.splits_rootGerm
#print axioms Sz8.Galois.Germs.rootGerm_injective
#print axioms Sz8.Galois.Germs.polyGerm_le
#print axioms Sz8.Galois.Continuation.continue_along
#print axioms Sz8.Galois.Continuation.continue_monodromy
#print axioms Sz8.Galois.Relations.relations_monodromy
#print axioms Sz8.Galois.Bridge.mem_image_iff
#print axioms Sz8.Galois.Bridge.bridge
#print axioms Sz8.Galois.Orbit.monodromy_eq_comp
#print axioms Sz8.Galois.Orbit.orbitPolyOf_indep
#print axioms Sz8.Galois.Orbit.orbitPoly_local
#print axioms Sz8.Galois.Orbit.orbitCoeff_analyticAt
#print axioms Sz8.Galois.Orbit.orbitCoeff_analyticOnNhd
#print axioms Sz8.Galois.Orbit.exists_separating
#print axioms Sz8.Galois.Orbit.regular_compl_finite
#print axioms Sz8.Galois.Orbit.regular_isPathConnected
#print axioms Sz8.Galois.OrbitPoly.norm_coeff_prod_le
#print axioms Sz8.Galois.OrbitPoly.norm_orbitCoeff_le
#print axioms Sz8.Galois.OrbitPoly.exists_root_growth
#print axioms Sz8.Galois.OrbitPoly.exists_orbitCoeff_poly
#print axioms Sz8.Galois.OrbitPoly.orbitPhi_spec
#print axioms Sz8.Galois.Converse.orbitPhi_germ
#print axioms Sz8.Galois.Converse.converse
#print axioms Sz8.Galois.monodromy_eq_geometric_galois
#print axioms Sz8.Galois.generic_galois
#print axioms Sz8.Galois.Stab13.card_stabilizer_pair_le
#print axioms Sz8.Galois.Stab13.card_stabilizer_set_le
#print axioms Sz8.Galois.Stab13.stab_le
#print axioms Sz8.Galois.Stab13.orbit_stable
#print axioms Sz8.Galois.Stab13.orbit_cover
#print axioms Sz8.Galois.FirstEdge.units_map_residue
#print axioms Sz8.Galois.FirstEdge.exists_primitive_ratio
#print axioms Sz8.Galois.FirstEdge.specialize_zero
#print axioms Sz8.Galois.FirstEdge.Fτ_eval
#print axioms Sz8.Galois.FirstEdge.Fτ_monic
#print axioms Sz8.Galois.Specialize.exists_decomposition
#print axioms Sz8.Galois.Specialize.image_le_decomposition
#print axioms Sz8.Galois.Specialize.smul_eq_self_of_residue
#print axioms Sz8.Galois.SpecFamily.fQ_monic
#print axioms Sz8.Galois.SpecFamily.fQ_spec
#print axioms Sz8.Galois.specialization_le_decomposition
#print axioms Sz8.Galois.Specialize.smul_eq_self_of_split
#print axioms Sz8.Galois.decomposition_le_of_split_witness
#print axioms Sz8.Galois.Resolvent.Θ_mul_mem
#print axioms Sz8.Galois.Resolvent.map_Θ
#print axioms Sz8.Galois.Resolvent.exists_pow_mul
#print axioms Sz8.Galois.Resolvent.disc_eq
#print axioms Sz8.Galois.Resolvent.Rs_monic
#print axioms Sz8.Galois.Resolvent.Rs_fibre
#print axioms Sz8.Galois.Resolvent.disc_eval_zero_ne
#print axioms Sz8.Galois.Resolvent.eq_of_pins
#print axioms Sz8.Galois.Resolvent.Z1_natDegree
#print axioms Sz8.Galois.Resolvent.Z2_natDegree
#print axioms Sz8.Galois.Resolvent.Z3_natDegree
#print axioms Sz8.Galois.DegreeBound.isIntegralElem_root
#print axioms Sz8.Galois.DegreeBound.isIntegralElem_Θ
#print axioms Sz8.Galois.DegreeBound.natDegree_le_of_isIntegralElem
#print axioms Sz8.Galois.sym_natDegree_le
#print axioms Sz8.Galois.IntModel.terms_ok
#print axioms Sz8.Galois.IntModel.fZ_monic
#print axioms Sz8.Galois.IntModel.fZ_eval
#print axioms Sz8.Galois.IntModel.int_of_isIntegral
#print axioms Sz8.Galois.IntModel.isIntegralElem_Θ
#print axioms Sz8.Galois.Resolvent.exists_perm_pow_mul
#print axioms Sz8.Galois.sigma1_not_mem_N
#print axioms Sz8.Galois.sym_int
#print axioms Sz8.Galois.map_symOf
#print axioms Sz8.Galois.sym_eval_of_link
#print axioms Sz8.Galois.exists_disc_roots
#print axioms Sz8.Galois.meridian_monodromy_labelled
#print axioms Sz8.Galois.generic_galois_labelled
#print axioms Sz8.Galois.GermEval.eventually_eval_eq_zero
#print axioms Sz8.Galois.GermEval.analyticAt_eval₂
#print axioms Sz8.Galois.disc_root_unique
#print axioms Sz8.Galois.disc_root_analyticAt
#print axioms Sz8.Galois.germ_link
#print axioms Sz8.Galois.Pinning.pins_of_inverse
#print axioms Sz8.Galois.Pinning.pins
#print axioms Sz8.Galois.Pinning.r_small
#print axioms Sz8.Galois.NSum.sum_lclosure
#print axioms Sz8.Galois.NSum.sum_mono_grouped
#print axioms Sz8.Galois.Θ_eq_grouped
#print axioms Sz8.Galois.Enclose.encCheck_sound
#print axioms Sz8.Galois.EncData4.checks
#print axioms Sz8.Galois.norm_eval_eq_prod
#print axioms Sz8.Galois.enclose
#print axioms Sz8.Galois.enclose_disc_root
#print axioms Sz8.Galois.enclosures_point4
#print axioms Sz8.Galois.Lipschitz.norm_Θ_sub_le
#print axioms Sz8.Galois.Lipschitz.norm_Θ_le
#print axioms Sz8.Galois.Lipschitz.norm_sym3_sub_le
#print axioms Sz8.Galois.ThetaEval.gc_thetaGI
#print axioms Sz8.Galois.PointBound.point_bound
#print axioms Sz8.Galois.ZList.aeval_Z
#print axioms Sz8.Galois.near_point
#print axioms Sz8.Galois.EncData0.checks
#print axioms Sz8.Galois.EncData1.checks
#print axioms Sz8.Galois.EncData2.checks
#print axioms Sz8.Galois.EncData3.checks
#print axioms Sz8.Galois.EncData5.checks
#print axioms Sz8.Galois.EncData6.checks
#print axioms Sz8.Galois.ThetaData0.symChecks
#print axioms Sz8.Galois.ThetaData1.symChecks
#print axioms Sz8.Galois.ThetaData2.symChecks
#print axioms Sz8.Galois.ThetaData3.symChecks
#print axioms Sz8.Galois.ThetaData4.symChecks
#print axioms Sz8.Galois.ThetaData5.symChecks
#print axioms Sz8.Galois.ThetaData6.symChecks
#print axioms Sz8.Galois.sym_near
#print axioms Sz8.Galois.resolvent_identity
#print axioms Sz8.Galois.decomposition_le_N
#print axioms Sz8.Galois.specialization_embeds
#print axioms Sz8.Galois.gal_specialization_eq_N
#print axioms Sz8.Galois.card_gal_specialization
#print axioms Sz8.Galois.Suzuki.θ8_sq
#print axioms Sz8.Galois.Suzuki.det_Tmat
#print axioms Sz8.Galois.Suzuki.det_Mmat
#print axioms Sz8.Galois.Suzuki.det_Wmat
#print axioms Sz8.Galois.Suzuki.ovoid_card
#print axioms Sz8.Galois.Suzuki.ovoid_stable
#print axioms Sz8.Galois.Suzuki.eq_scalar_of_frame
#print axioms Sz8.Galois.Suzuki.ψ_injective
#print axioms Sz8.Galois.Suzuki.siftOK
#print axioms Sz8.Galois.Suzuki.word1OK
#print axioms Sz8.Galois.Suzuki.word2OK
#print axioms Sz8.Galois.Suzuki.suzuki_le_presSub
#print axioms Sz8.Galois.Suzuki.φ_injective
#print axioms Sz8.Galois.Suzuki.range_φ
#print axioms Sz8.Galois.Suzuki.suzukiEquiv
#print axioms Sz8.Galois.N_equiv_suzuki
#print axioms Sz8.Galois.gal_specialization_equiv_suzuki
