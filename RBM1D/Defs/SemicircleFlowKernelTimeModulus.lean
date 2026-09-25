import RBM1D.Defs.SemicircleFlowResolvent

/-! # Time modulus for the closed-flow semicircle resolvent kernel -/

namespace RBM

/-- Closed-flow semicircle resolvent kernel. -/
noncomputable def semicircleFlowKernel (u x : ℝ) : ℂ :=
  (((Real.sqrt u * x : ℝ) : ℂ) - Complex.I * ((1-u : ℝ) : ℂ))⁻¹

private noncomputable def semicircleFlowKernelDen (u x : ℝ) : ℂ :=
  ((Real.sqrt u * x : ℝ) : ℂ) - Complex.I * ((1-u : ℝ) : ℂ)

private theorem abs_sqrt_sub_sqrt_le_local {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt |a-b| := by
  rcases le_total b a with h | h
  · have hs : Real.sqrt b ≤ Real.sqrt a := Real.sqrt_le_sqrt h
    rw [abs_of_nonneg (sub_nonneg.mpr hs), abs_of_nonneg (sub_nonneg.mpr h)]
    have hsq : (Real.sqrt a - Real.sqrt b) ^ 2 ≤ a - b := by
      have haa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
      have hbb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
      have hab : Real.sqrt b * Real.sqrt b ≤ Real.sqrt a * Real.sqrt b :=
        mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg b)
      nlinarith [haa, hbb, hab]
    have hroot := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (sub_nonneg.mpr hs)] at hroot
  · have hs : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt h
    rw [abs_sub_comm, abs_sub_comm a b,
      abs_of_nonneg (sub_nonneg.mpr hs), abs_of_nonneg (sub_nonneg.mpr h)]
    have hsq : (Real.sqrt b - Real.sqrt a) ^ 2 ≤ b - a := by
      have haa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
      have hbb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
      have hab : Real.sqrt a * Real.sqrt a ≤ Real.sqrt b * Real.sqrt a :=
        mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg a)
      nlinarith [haa, hbb, hab]
    have hroot := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (sub_nonneg.mpr hs)] at hroot

private theorem semicircleFlowKernelDen_re (u x : ℝ) :
    (semicircleFlowKernelDen u x).re = Real.sqrt u * x := by
  simp [semicircleFlowKernelDen]

private theorem semicircleFlowKernelDen_im (u x : ℝ) :
    (semicircleFlowKernelDen u x).im = -(1-u) := by
  simp [semicircleFlowKernelDen]

private theorem semicircleFlowKernelDen_normSq (u x : ℝ) (hu : 0 ≤ u) :
    Complex.normSq (semicircleFlowKernelDen u x) = u*x^2 + (1-u)^2 := by
  rw [Complex.normSq_apply, semicircleFlowKernelDen_re, semicircleFlowKernelDen_im]
  calc
    _ = (Real.sqrt u)^2 * x^2 + (1-u)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt hu]

private theorem semicircleFlowKernel_re (u x : ℝ) (hu : 0 ≤ u) :
    (semicircleFlowKernel u x).re = Real.sqrt u * x / (u*x^2+(1-u)^2) := by
  change ((semicircleFlowKernelDen u x)⁻¹).re = _
  rw [Complex.inv_re, semicircleFlowKernelDen_re,
    semicircleFlowKernelDen_normSq u x hu]

/-- The closed-flow kernel varies by at most `12 sqrt |u-v|` in time on the
semicircle spectral support. -/
theorem semicircleFlowKernel_time_modulus
    (u v x : ℝ) (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    (hu : u ≤ 1 / 2) (hv : v ≤ 1 / 2) (hx : |x| ≤ 2) :
    ‖semicircleFlowKernel u x - semicircleFlowKernel v x‖
      ≤ 12 * Real.sqrt |u - v| := by
  let δ : ℝ := |u-v|
  have hδ0 : 0 ≤ δ := abs_nonneg _
  have hδle : δ ≤ 1/2 := by
    dsimp [δ]
    rw [abs_le]
    constructor <;> linarith
  have hδsqrt : δ ≤ Real.sqrt δ := by
    have hsle : Real.sqrt δ ≤ 1 := by
      calc
        Real.sqrt δ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
        _ = 1 := Real.sqrt_one
    have hsquare := Real.sq_sqrt hδ0
    have hs0 : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
    nlinarith
  have hsqrt : |Real.sqrt u - Real.sqrt v| ≤ Real.sqrt δ := by
    simpa [δ] using abs_sqrt_sub_sqrt_le_local hu0 hv0
  have htime : |u-v| ≤ Real.sqrt δ := by simpa [δ] using hδsqrt
  have hdenDiff :
      ‖semicircleFlowKernelDen u x - semicircleFlowKernelDen v x‖ ≤
        3 * Real.sqrt δ := by
    have hreal :
        ‖(((Real.sqrt u - Real.sqrt v) * x : ℝ) : ℂ)‖ ≤
          2 * Real.sqrt δ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
      calc
        |Real.sqrt u - Real.sqrt v| * |x| ≤ Real.sqrt δ * 2 :=
          mul_le_mul hsqrt hx (abs_nonneg _) (Real.sqrt_nonneg _)
        _ = 2 * Real.sqrt δ := by ring
    have himag : ‖(Complex.I * ((u-v : ℝ) : ℂ))‖ ≤ Real.sqrt δ := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact htime
    have hdiff : semicircleFlowKernelDen u x - semicircleFlowKernelDen v x =
        (((Real.sqrt u - Real.sqrt v) * x : ℝ) : ℂ) +
          Complex.I * ((u-v : ℝ) : ℂ) := by
      simp only [semicircleFlowKernelDen]
      push_cast
      ring
    rw [hdiff]
    calc
      _ ≤ ‖(((Real.sqrt u - Real.sqrt v) * x : ℝ) : ℂ)‖ +
            ‖Complex.I * ((u-v : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 * Real.sqrt δ + Real.sqrt δ := add_le_add hreal himag
      _ = 3 * Real.sqrt δ := by ring
  have hdenU := semicircleFlowResolvent_denominator_gap u x hu
  have hdenV := semicircleFlowResolvent_denominator_gap v x hv
  have hnormU : (1/2 : ℝ) ≤ ‖semicircleFlowKernelDen u x‖ := by
    simpa [semicircleFlowKernelDen] using (show (1/2 : ℝ) ≤ 1-u by linarith).trans hdenU
  have hnormV : (1/2 : ℝ) ≤ ‖semicircleFlowKernelDen v x‖ := by
    simpa [semicircleFlowKernelDen] using (show (1/2 : ℝ) ≤ 1-v by linarith).trans hdenV
  have hneU : semicircleFlowKernelDen u x ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hnormU
    norm_num at hnormU
  have hneV : semicircleFlowKernelDen v x ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hnormV
    norm_num at hnormV
  have hinvU : ‖(semicircleFlowKernelDen u x)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have hpos : (0 : ℝ) < ‖semicircleFlowKernelDen u x‖ :=
      lt_of_lt_of_le (by norm_num) hnormU
    calc
      ‖semicircleFlowKernelDen u x‖⁻¹ ≤ (1/2 : ℝ)⁻¹ :=
        (inv_le_inv₀ hpos (by norm_num)).2 hnormU
      _ = 2 := by norm_num
  have hinvV : ‖(semicircleFlowKernelDen v x)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have hpos : (0 : ℝ) < ‖semicircleFlowKernelDen v x‖ :=
      lt_of_lt_of_le (by norm_num) hnormV
    calc
      ‖semicircleFlowKernelDen v x‖⁻¹ ≤ (1/2 : ℝ)⁻¹ :=
        (inv_le_inv₀ hpos (by norm_num)).2 hnormV
      _ = 2 := by norm_num
  have hsub : semicircleFlowKernel u x - semicircleFlowKernel v x =
      (semicircleFlowKernelDen v x - semicircleFlowKernelDen u x) *
        (semicircleFlowKernelDen u x)⁻¹ * (semicircleFlowKernelDen v x)⁻¹ := by
    change (semicircleFlowKernelDen u x)⁻¹ - (semicircleFlowKernelDen v x)⁻¹ = _
    field_simp [hneU, hneV]
  rw [hsub, norm_mul, norm_mul]
  calc
      ‖semicircleFlowKernelDen v x - semicircleFlowKernelDen u x‖ *
        ‖(semicircleFlowKernelDen u x)⁻¹‖ *
        ‖(semicircleFlowKernelDen v x)⁻¹‖ ≤
      (3 * Real.sqrt δ) * 2 * 2 := by
        have hdiffrev :
            ‖semicircleFlowKernelDen v x - semicircleFlowKernelDen u x‖ ≤
              3 * Real.sqrt δ := by simpa only [norm_sub_rev] using hdenDiff
        gcongr
    _ = 12 * Real.sqrt |u - v| := by dsimp [δ]; ring

/-- The closed-flow kernel is nonconstant between the two time endpoints, even at `x=0`. -/
theorem semicircleFlowKernel_zero_ne_half_at_zero :
    semicircleFlowKernel 0 0 ≠ semicircleFlowKernel (1/2) 0 := by
  change ((((Real.sqrt 0 * 0 : ℝ) : ℂ) - Complex.I * ((1-(0:ℝ) : ℝ) : ℂ))⁻¹) ≠
    ((((Real.sqrt (1 / 2:ℝ) * 0 : ℝ) : ℂ) -
      Complex.I * ((1-(1 / 2:ℝ) : ℝ) : ℂ))⁻¹)
  rw [semicircleFlowResolvent_half_at_zero]
  norm_num

#print axioms semicircleFlowKernel
#print axioms semicircleFlowKernel_time_modulus
#print axioms semicircleFlowKernel_zero_ne_half_at_zero

end RBM
