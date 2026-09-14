import Sz8.Galois.LiftIndex
import Sz8.Monodromy.Meridian.Chain

open Sz8.Monodromy Sz8.Monodromy.GaussPoly Complex

namespace Sz8.Galois.Circuit

/-!
# Circuit certificate: the recorded circuit has index one

The first certified meridian is a tail, a closed 145-edge circuit about `ζ₃`, and the exact reverse
of the tail (waypoints `0..504`, `504..649`, `649..1153`). This file proves the circuit's index is
`1`, and hence that it generates the fundamental group of the plane punctured at `ζ₃`.

No logarithm is ever evaluated. The circuit, translated by `-ζ₃`, is cut at vertices 25 and 96 —
just past the only two edges that cross the horizontal line through `ζ₃` — into three arcs. The
first and last avoid the negative real axis and are lifted by the principal `log`; the middle one
avoids the positive real axis and is lifted by `log (-z) + πi`. That branch agrees with `log` above
the real axis and exceeds it by `2πi` below, so the index is decided by the *signs* of vertices 25
and 96 (`liftIndex_three_arcs`).

Every sign is an integer inequality on the recorded waypoints (scale `2^40`): the ordinate test
`y > √3/2` is `y > 0 ∧ 4y² > 3·2^80`, and no vertex can lie *on* the line since `√3` is irrational.
Each edge is certified to lie in an open half-plane inside the relevant slit plane by its two
endpoints. The whole check is one `decide +kernel` over a 146-entry literal that is itself proved
equal to the recorded data; it costs about 2 s and 150 MB above the import baseline.
-/

/-- The closed circuit of the first certified meridian: waypoints 504 to 649 of the recorded
polyline, at scale `2^40`. -/
def circ : List (ℤ × ℤ) := [
  (-548924671704, 950765420919), (-548888033381, 950793534493), (-548812970903, 950851131958), (-548737391040, 950909126427),
  (-548662160268, 950966853029), (-548587466108, 951024167874), (-548580401339, 951029588861), (-548550370518, 951068725789),
  (-548506124076, 951126388875), (-548465564838, 951179246704), (-548416917402, 951242645276), (-548367481397, 951307071532),
  (-548316233397, 951373859226), (-548315878251, 951374716625), (-548281284178, 951458234106), (-548244527975, 951546971428),
  (-548206087684, 951639774500), (-548167078469, 951733951076), (-548150170486, 951774770557), (-548144131509, 951820641143),
  (-548135233875, 951888225382), (-548124561903, 951969287061), (-548113889930, 952050348740), (-548103044966, 952132724419),
  (-548093529520, 952205001410), (-548095239550, 952217990379), (-548106772915, 952305594983), (-548118666697, 952395937230),
  (-548130932160, 952489102671), (-548143782683, 952586712085), (-548150170486, 952635232263), (-548161228758, 952661929294),
  (-548189160593, 952729362708), (-548222485890, 952809817091), (-548255128135, 952888622442), (-548288299507, 952968705219),
  (-548316233397, 953036143595), (-548327319996, 953050591932), (-548382986118, 953123137435), (-548436332819, 953192660209),
  (-548488586100, 953260758011), (-548541686401, 953329959671), (-548580401339, 953380413960), (-548602776328, 953397582893),
  (-548679810303, 953456693141), (-548740399640, 953503184975), (-548813071515, 953558948066), (-548885743390, 953614711157),
  (-548924671704, 953644581902), (-548966852163, 953662053620), (-549035572497, 953690518514), (-549116215374, 953723921888),
  (-549195205356, 953756640610), (-549274195338, 953789359331), (-549325583035, 953810644812), (-549358293138, 953814951179),
  (-549448357749, 953826808410), (-549538422360, 953838665641), (-549628486971, 953850522872), (-549718551582, 953862380103),
  (-549755813888, 953867285779), (-549803991831, 953860943032), (-549898376520, 953848517052), (-549992087973, 953836179705),
  (-550064223845, 953826682837), (-550133354055, 953817581672), (-550186044741, 953810644812), (-550214078115, 953799033008),
  (-550289360822, 953767849890), (-550364643529, 953736666772), (-550439926236, 953705483654), (-550516429267, 953673795061),
  (-550586956072, 953644581902), (-550595445100, 953638068041), (-550666278718, 953583715494), (-550737112336, 953529362947),
  (-550809094159, 953474129352), (-550884509500, 953416261126), (-550931226437, 953380413960), (-550957056356, 953346751755),
  (-551021358454, 953262951629), (-551071229324, 953197958645), (-551118237102, 953136696916), (-551163286223, 953077987759),
  (-551195394379, 953036143595), (-551209094273, 953003069125), (-551241473763, 952924898122), (-551273703697, 952847088178),
  (-551305703739, 952769833241), (-551337047894, 952694161759), (-551361457290, 952635232263), (-551364044725, 952615578744),
  (-551375069723, 952531835570), (-551386094721, 952448092396), (-551397298433, 952362991755), (-551408667962, 952276631607),
  (-551418098256, 952205001410), (-551415926754, 952188507217), (-551404011869, 952098004680), (-551394771025, 952027813496),
  (-551383687400, 951943625003), (-551372603774, 951859436510), (-551361520149, 951775248017), (-551361457290, 951774770557),
  (-551344074563, 951732804941), (-551309477112, 951649279305), (-551274641190, 951565177949), (-551240519281, 951482800374),
  (-551206397372, 951400422800), (-551195394379, 951373859226), (-551167238382, 951337165616), (-551114131431, 951267955289),
  (-551061269771, 951199064633), (-551008785167, 951130665366), (-550956542981, 951062582024), (-550931226437, 951029588861),
  (-550895387796, 951002088904), (-550827790084, 950950219355), (-550761577887, 950899412949), (-550695365689, 950848606543),
  (-550629153491, 950797800137), (-550586956072, 950765420919), (-550558701732, 950753717588), (-550481595995, 950721779346),
  (-550404490258, 950689841104), (-550327384521, 950657902862), (-550250278784, 950625964620), (-550186044741, 950599358008),
  (-550171906230, 950597496638), (-550089161583, 950586603099), (-550006416936, 950575709559), (-549922331007, 950564639437),
  (-549837000590, 950553405474), (-549755813888, 950542717042), (-549751538322, 950543279931), (-549664824709, 950554695995),
  (-549575401297, 950566468810), (-549483183403, 950578609526), (-549388083700, 950591129639), (-549325583035, 950599358008),
  (-549290620197, 950613840090), (-549217594337, 950644088392), (-549150653966, 950671816001), (-549072099865, 950704354175),
  (-548995155846, 950736225431), (-548924671704, 950765420919)]

/-- The literal is the recorded data, not a transcription of it. -/
theorem circ_eq : circ = (Meridian1.chain.wps.drop 504).take 146 := by decide +kernel

def imPosB (w : ℤ × ℤ) : Bool := decide (0 < w.2 ∧ 3 * 2 ^ 80 < 4 * w.2 ^ 2)
def imNegB (w : ℤ × ℤ) : Bool := decide (w.2 ≤ 0 ∨ 4 * w.2 ^ 2 < 3 * 2 ^ 80)
def rePosB (w : ℤ × ℤ) : Bool := decide (0 < 2 * w.1 + 2 ^ 40)
def reNegB (w : ℤ × ℤ) : Bool := decide (2 * w.1 + 2 ^ 40 < 0)

def vtx (i : ℕ) : ℤ × ℤ := circ.getD i (0, 0)

def slitB (i : ℕ) : Bool :=
  (imPosB (vtx i) && imPosB (vtx (i + 1))) || (imNegB (vtx i) && imNegB (vtx (i + 1))) ||
    (rePosB (vtx i) && rePosB (vtx (i + 1)))
def negSlitB (i : ℕ) : Bool :=
  (imPosB (vtx i) && imPosB (vtx (i + 1))) || (imNegB (vtx i) && imNegB (vtx (i + 1))) ||
    (reNegB (vtx i) && reNegB (vtx (i + 1)))

theorem cert : ((List.range 25).all fun i => slitB i) && ((List.range 71).all fun i => negSlitB (25 + i))
    && ((List.range 49).all fun i => slitB (96 + i)) && imPosB (vtx 25) && imNegB (vtx 96)
    && decide (vtx 145 = vtx 0) = true := by decide +kernel

theorem sqrt3_half_lt {y : ℤ} (hy : 0 < y) (h : 3 * 2 ^ 80 < 4 * y ^ 2) :
    Real.sqrt 3 / 2 < (y : ℝ) / 2 ^ 40 := by
  have hy' : (0 : ℝ) < (y : ℝ) / 2 ^ 39 := by positivity
  have h' : (3 : ℝ) < ((y : ℝ) / 2 ^ 39) ^ 2 := by
    rw [div_pow, lt_div_iff₀ (by positivity)]
    have : ((3 * 2 ^ 80 : ℤ) : ℝ) < ((4 * y ^ 2 : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at this; nlinarith
  have := (Real.sqrt_lt' hy').2 h'
  calc Real.sqrt 3 / 2 < (y : ℝ) / 2 ^ 39 / 2 := by linarith
    _ = (y : ℝ) / 2 ^ 40 := by ring

theorem lt_sqrt3_half {y : ℤ} (h : y ≤ 0 ∨ 4 * y ^ 2 < 3 * 2 ^ 80) :
    (y : ℝ) / 2 ^ 40 < Real.sqrt 3 / 2 := by
  have h3 : 0 < Real.sqrt 3 := by positivity
  rcases h with h | h
  · have : (y : ℝ) ≤ 0 := by exact_mod_cast h
    have : (y : ℝ) / 2 ^ 40 ≤ 0 := div_nonpos_of_nonpos_of_nonneg this (by positivity)
    linarith
  · rcases le_or_gt y 0 with hy | hy
    · have : (y : ℝ) ≤ 0 := by exact_mod_cast hy
      have : (y : ℝ) / 2 ^ 40 ≤ 0 := div_nonpos_of_nonpos_of_nonneg this (by positivity)
      linarith
    · have h' : ((y : ℝ) / 2 ^ 39) ^ 2 < 3 := by
        rw [div_pow, div_lt_iff₀ (by positivity)]
        have : ((4 * y ^ 2 : ℤ) : ℝ) < ((3 * 2 ^ 80 : ℤ) : ℝ) := by exact_mod_cast h
        push_cast at this; nlinarith
      have := (Real.lt_sqrt (by positivity)).2 h'
      calc (y : ℝ) / 2 ^ 40 = (y : ℝ) / 2 ^ 39 / 2 := by ring
        _ < Real.sqrt 3 / 2 := by linarith

/-- `ζ₃ = (-1 + √3 i)/2`. -/
noncomputable def zeta3 : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

/-- Vertex `i` of the circuit, translated so that `ζ₃` is at the origin. -/
noncomputable def pt (i : ℕ) : ℂ := ptC 40 (vtx i) - zeta3

theorem ptC_eq (w : ℤ × ℤ) :
    ptC 40 w = ((w.1 : ℝ) / 2 ^ 40 : ℝ) + ((w.2 : ℝ) / 2 ^ 40 : ℝ) * I := by
  simp only [ptC, gc]; push_cast; ring

theorem pt_re (i : ℕ) : (pt i).re = ((vtx i).1 : ℝ) / 2 ^ 40 + 1 / 2 := by
  rw [pt, ptC_eq]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zeta3]
  ring

theorem pt_im (i : ℕ) : (pt i).im = ((vtx i).2 : ℝ) / 2 ^ 40 - Real.sqrt 3 / 2 := by
  rw [pt, ptC_eq]
  simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, zeta3]
  ring

theorem pt_im_pos {i : ℕ} (h : imPosB (vtx i) = true) : 0 < (pt i).im := by
  simp only [imPosB, decide_eq_true_eq] at h
  rw [pt_im]; linarith [sqrt3_half_lt h.1 h.2]

theorem pt_im_neg {i : ℕ} (h : imNegB (vtx i) = true) : (pt i).im < 0 := by
  simp only [imNegB, decide_eq_true_eq] at h
  rw [pt_im]; linarith [lt_sqrt3_half h]

theorem pt_re_pos {i : ℕ} (h : rePosB (vtx i) = true) : 0 < (pt i).re := by
  simp only [rePosB, decide_eq_true_eq] at h
  have : (0 : ℝ) < 2 * ((vtx i).1 : ℝ) + 2 ^ 40 := by exact_mod_cast h
  rw [pt_re]; have : (0 : ℝ) < ((vtx i).1 : ℝ) / 2 ^ 40 + 1 / 2 := by
    rw [show ((vtx i).1 : ℝ) / 2 ^ 40 + 1 / 2 = (2 * ((vtx i).1 : ℝ) + 2 ^ 40) / 2 ^ 41 by ring]
    positivity
  exact this

theorem pt_re_neg {i : ℕ} (h : reNegB (vtx i) = true) : (pt i).re < 0 := by
  simp only [reNegB, decide_eq_true_eq] at h
  have h' : 2 * ((vtx i).1 : ℝ) + 2 ^ 40 < 0 := by exact_mod_cast h
  rw [pt_re, show ((vtx i).1 : ℝ) / 2 ^ 40 + 1 / 2 = (2 * ((vtx i).1 : ℝ) + 2 ^ 40) / 2 ^ 41 by ring]
  exact div_neg_of_neg_of_pos h' (by positivity)

/-! ### Segments and polylines -/

theorem pos_between {x y t : ℝ} (hx : 0 < x) (hy : 0 < y) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 < x + t * (y - x) := by
  rcases lt_or_eq_of_le h1 with h | h
  · nlinarith [mul_nonneg h0 hy.le, mul_pos (sub_pos.2 h) hx]
  · subst h; linarith

theorem neg_between {x y t : ℝ} (hx : x < 0) (hy : y < 0) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    x + t * (y - x) < 0 := by
  have := pos_between (neg_pos.2 hx) (neg_pos.2 hy) h0 h1
  linarith

theorem seg_re (a b : ℂ) (u : unitInterval) :
    (MonicFamily.segment a b u).re = a.re + (u : ℝ) * (b.re - a.re) := by
  simp [MonicFamily.segment]

theorem seg_im (a b : ℂ) (u : unitInterval) :
    (MonicFamily.segment a b u).im = a.im + (u : ℝ) * (b.im - a.im) := by
  simp [MonicFamily.segment]

theorem seg_mem_slit {i : ℕ} (h : slitB i = true) (u : unitInterval) :
    MonicFamily.segment (pt i) (pt (i + 1)) u ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  simp only [slitB, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with (⟨ha, hb⟩ | ⟨ha, hb⟩) | ⟨ha, hb⟩
  · exact Or.inr (by rw [seg_im]; exact (pos_between (pt_im_pos ha) (pt_im_pos hb) u.2.1 u.2.2).ne')
  · exact Or.inr (by rw [seg_im]; exact (neg_between (pt_im_neg ha) (pt_im_neg hb) u.2.1 u.2.2).ne)
  · exact Or.inl (by rw [seg_re]; exact pos_between (pt_re_pos ha) (pt_re_pos hb) u.2.1 u.2.2)

theorem seg_mem_negSlit {i : ℕ} (h : negSlitB i = true) (u : unitInterval) :
    -MonicFamily.segment (pt i) (pt (i + 1)) u ∈ slitPlane := by
  rw [mem_slitPlane_iff, Complex.neg_re, Complex.neg_im, seg_re, seg_im]
  simp only [negSlitB, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with (⟨ha, hb⟩ | ⟨ha, hb⟩) | ⟨ha, hb⟩
  · have := pos_between (pt_im_pos ha) (pt_im_pos hb) u.2.1 u.2.2
    exact Or.inr (neg_ne_zero.2 this.ne')
  · have := neg_between (pt_im_neg ha) (pt_im_neg hb) u.2.1 u.2.2
    exact Or.inr (neg_ne_zero.2 this.ne)
  · have := neg_between (pt_re_neg ha) (pt_re_neg hb) u.2.1 u.2.2
    exact Or.inl (by linarith)

/-- The polyline through the circuit vertices `a, a + 1, …, a + m`. -/
noncomputable def poly (a : ℕ) : (m : ℕ) → Path (pt a) (pt (a + m))
  | 0 => Path.refl _
  | m + 1 => (poly a m).trans (MonicFamily.segment (pt (a + m)) (pt (a + m + 1)))

theorem poly_mem {S : Set ℂ} (a : ℕ) : ∀ m, pt a ∈ S →
    (∀ k < m, ∀ u, MonicFamily.segment (pt (a + k)) (pt (a + k + 1)) u ∈ S) →
    ∀ u, poly a m u ∈ S
  | 0, h0, _, u => by simpa [poly] using h0
  | m + 1, h0, h, u => by
    have hu : poly a (m + 1) u ∈ Set.range
        ((poly a m).trans (MonicFamily.segment (pt (a + m)) (pt (a + m + 1)))) := ⟨u, rfl⟩
    rw [Path.trans_range] at hu
    rcases hu with ⟨v, hv⟩ | ⟨v, hv⟩
    · rw [← hv]; exact poly_mem a m h0 (fun k hk => h k (by omega)) v
    · rw [← hv]; exact h m (by omega) v

/-! ### The three arcs and the index -/

theorem cert_parts : (∀ i < 25, slitB i = true) ∧ (∀ i < 71, negSlitB (25 + i) = true) ∧
    (∀ i < 49, slitB (96 + i) = true) ∧ imPosB (vtx 25) = true ∧ imNegB (vtx 96) = true ∧
    vtx 145 = vtx 0 := by
  have h := cert
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem ne_zero_of_slit {z : ℂ} (h : z ∈ slitPlane) : z ≠ 0 := slitPlane_ne_zero h

theorem ne_zero_of_negSlit {z : ℂ} (h : -z ∈ slitPlane) : z ≠ 0 :=
  fun hz => slitPlane_ne_zero h (by simp [hz])

/-- A path in `ℂ` avoiding `0`, as a path in the punctured plane. -/
noncomputable def toCStar {z w : ℂ} (γ : Path z w) (h : ∀ u, γ u ≠ 0) :
    Path (⟨z, γ.source ▸ h 0⟩ : CStar) ⟨w, γ.target ▸ h 1⟩ where
  toFun u := ⟨γ u, h u⟩
  continuous_toFun := γ.continuous.subtype_mk _
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

theorem hA : ∀ u, poly 0 25 u ∈ slitPlane :=
  poly_mem 0 25 (by simpa using seg_mem_slit (cert_parts.1 0 (by norm_num)) 0)
    (fun k hk u => by simpa using seg_mem_slit (cert_parts.1 k hk) u)

theorem hB : ∀ u, poly 25 71 u ∈ {z | -z ∈ slitPlane} :=
  poly_mem 25 71 (by simpa using seg_mem_negSlit (cert_parts.2.1 0 (by norm_num)) 0)
    (fun k hk u => by simpa using seg_mem_negSlit (cert_parts.2.1 k hk) u)

theorem hD : ∀ u, poly 96 49 u ∈ slitPlane :=
  poly_mem 96 49 (by simpa using seg_mem_slit (cert_parts.2.2.1 0 (by norm_num)) 0)
    (fun k hk u => by simpa using seg_mem_slit (cert_parts.2.2.1 k hk) u)

theorem pt_closed : pt 0 = pt 145 := by simp only [pt, cert_parts.2.2.2.2.2]

noncomputable def arcA := toCStar (poly 0 25) fun u => ne_zero_of_slit (hA u)
noncomputable def arcB := toCStar (poly 25 71) fun u => ne_zero_of_negSlit (hB u)
noncomputable def arcD :=
  toCStar ((poly 96 49).cast rfl pt_closed) fun u => ne_zero_of_slit (hD u)

/-- The recorded circuit, translated by `-ζ₃`, as a loop in the punctured plane. -/
noncomputable def circuitLoop := (arcA.trans arcB).trans arcD

/-- The base point: the circuit's first vertex, translated by `-ζ₃`. -/
noncomputable def base0 : CStar := ⟨pt 0, ne_zero_of_slit (by simpa using hA 0)⟩

/-- **The recorded 145-edge circuit has index `1` about `ζ₃`.** -/
theorem circuit_liftIndex :
    liftIndex (⟨log (pt 0), expMap_log base0⟩ : expMap ⁻¹' {base0})
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk circuitLoop)) = 1 :=
  liftIndex_three_arcs arcA arcB arcD (fun u => hA u) (fun u => hB u) (fun u => hD u)
    (pt_im_pos cert_parts.2.2.2.1) (pt_im_neg cert_parts.2.2.2.2.1)

/-- Consequently the recorded circuit generates the fundamental group of the plane punctured at
`ζ₃` (after translation), in the form the generation assembly consumes. -/
theorem circuit_zpowers_eq_top :
    Subgroup.zpowers (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk circuitLoop) :
      FundamentalGroup CStar base0) = ⊤ :=
  zpowers_eq_top_of_abs_liftIndex _ (by rw [circuit_liftIndex]; rfl)

end Sz8.Galois.Circuit
