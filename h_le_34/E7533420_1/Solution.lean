import Lean.Elab.Command
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Factorial
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.Wilson
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Tactic

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

/-! Standalone proof for E7533420_1.
Target: Lean 4.34.0; Mathlib 5ed2965256430c3649e86755f9576b54eca72435.
All certificate data and auxiliary proofs are included in this file. -/

set_option Elab.async false
set_option linter.all false
/- Source module: GraphCert.CubicCore. -/
elab "without_editor_info " c:command : command =>
  Lean.Elab.withEnableInfoTree false (Lean.Elab.Command.elabCommand c)

/-
Explicit cubic reciprocity and finite graph-certificate infrastructure.
Target: Lean 4.34.0 and Mathlib 5ed2965256430c3649e86755f9576b54eca72435.
The global product formula is proved for all nonzero Eisenstein integers.
The later graph and finite-computation lemmas support the compact certificates.
Generic cubic graph foundation. Equation-specific applications are external.
All graph identities, reciprocity, and local computations are included below.
It imports Mathlib only and uses no additional axioms or unchecked computations.
-/

set_option backward.isDefEq.respectTransparency false

/- The Gauss/Jacobi-sum part of cubic reciprocity. These theorems alone
   are not the global product formula needed by the seven certificates. -/

namespace CubicSpecial
open MulChar AddChar

without_editor_info theorem gauss_cube {F R : Type*} [Field F] [Fintype F]
    [CommRing R] [IsDomain R] {χ : MulChar F R} {ψ : AddChar F R}
    (hχ : orderOf χ = 3) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ^ 3 = Fintype.card F * jacobiSum χ χ := by
  have hc : χ ^ 3 = 1 := hχ ▸ pow_orderOf_eq_one χ
  have hn : χ (-1) = 1 := val_neg_one_eq_one_of_odd_order (by decide : Odd 3) hc
  have h := gaussSum_pow_eq_prod_jacobiSum (χ := χ) (by omega) hψ
  simpa [hχ, hn, Finset.prod_Ico_succ_top] using h

without_editor_info theorem gauss_frobenius_iter {F R : Type*} [CommRing F] [Fintype F]
    [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (χ : MulChar F R) (ψ : AddChar F R) (n : ℕ) :
    gaussSum χ ψ ^ (p ^ n) = gaussSum (χ ^ (p ^ n)) (ψ ^ (p ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_mul, ih, gaussSum_frob, ← pow_mul, ← pow_mul]

without_editor_info theorem gauss_frobenius_cubic {F R : Type*} [CommRing F] [Fintype F]
    [CommRing R] (p n : ℕ) [Fact p.Prime] [CharP R p]
    {χ : MulChar F R} (ψ : AddChar F R) (hχ : orderOf χ = 3)
    (hn : p ^ n % 3 = 1) (hp : IsUnit ((p : F) ^ n)) :
    gaussSum χ ψ ^ (p ^ n) = χ ((p : F) ^ n) ^ 2 * gaussSum χ ψ := by
  have hpow : χ ^ (p ^ n) = χ := by
    rw [← pow_mod_orderOf, hχ, hn, pow_one]
  have hinv : χ⁻¹ = χ ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ']
    simpa only [hχ] using pow_orderOf_eq_one χ
  rw [gauss_frobenius_iter, hpow, pow_mulShift]
  rw [Nat.cast_pow, ← hp.unit_spec, gaussSum_mulShift_eq, hinv, pow_apply_coe]

without_editor_info theorem jacobi_power {F R : Type*} [Field F] [Fintype F]
    [Field R] (p n : ℕ) [Fact p.Prime] [CharP R p]
    {χ : MulChar F R} {ψ : AddChar F R} (hχ : orderOf χ = 3)
    (hψ : ψ.IsPrimitive) (hn : p ^ n % 3 = 1)
    (hp : IsUnit ((p : F) ^ n)) (hc : (Fintype.card F : R) ≠ 0) :
    (Fintype.card F * jacobiSum χ χ) ^ ((p ^ n - 1) / 3) =
      χ ((p : F) ^ n) ^ 2 := by
  have hχ0 : χ ≠ 1 := by intro h; simp [h] at hχ
  have hg : gaussSum χ ψ ≠ 0 := gaussSum_ne_zero_of_nontrivial hc hχ0 hψ
  have he : 3 * ((p ^ n - 1) / 3) + 1 = p ^ n := by omega
  apply mul_right_cancel₀ hg
  rw [← gauss_cube hχ hψ, ← pow_mul, ← pow_succ, he]
  exact gauss_frobenius_cubic p n ψ hχ hn hp

without_editor_info theorem jacobi_cubic_residue {F E : Type*} [Field F] [Fintype F]
    [Field E] [Fintype E] {χ : MulChar F E} (hχ : orderOf χ = 3)
    (hchar : ringChar E ≠ ringChar F) (hcard : Fintype.card E % 3 = 1) :
    (Fintype.card F * jacobiSum χ χ) ^ ((Fintype.card E - 1) / 3) =
      χ (Fintype.card E) ^ 2 := by
  let ψ := FiniteField.primitiveChar F E hchar
  let L := CyclotomicField ψ.n E
  let ι : E →+* L := algebraMap E L
  let χ' := χ.ringHomComp ι
  have hχ' : orderOf χ' = 3 :=
    (orderOf_injective (ringHomCompHom ι) (injective_ringHomComp ι.injective) χ).trans hχ
  obtain ⟨n, hp, hc⟩ := FiniteField.card E (ringChar E)
  have hpFact : Fact (ringChar E).Prime := ⟨hp⟩
  have hL : ringChar L = ringChar E := (Algebra.ringChar_eq E L).symm
  have hCharPL : CharP L (ringChar E) :=
    hL ▸ (inferInstance : CharP L (ringChar L))
  have hpn : IsUnit (((ringChar E : ℕ) : F) ^ (n : ℕ)) := by
    apply IsUnit.pow
    apply isUnit_iff_ne_zero.mpr
    intro hz
    exact hchar (CharP.ringChar_of_prime_eq_zero hp hz).symm
  have hnonzero : (Fintype.card F : L) ≠ 0 := by
    obtain ⟨m, hq, hqcard⟩ := FiniteField.card F (ringChar F)
    rw [hqcard, Nat.cast_pow]
    apply pow_ne_zero
    intro hz
    exact hchar (hL.symm.trans (CharP.ringChar_of_prime_eq_zero hq hz))
  apply ι.injective
  rw [map_pow, map_mul, map_natCast, ← jacobiSum_ringHomComp, map_pow]
  change (Fintype.card F * jacobiSum χ' χ') ^ ((Fintype.card E - 1) / 3) =
    χ' (Fintype.card E) ^ 2
  rw [hc, Nat.cast_pow]
  exact jacobi_power (ringChar E) n hχ' ψ.prim (hc ▸ hcard) hpn hnonzero

end CubicSpecial



namespace CubicSpecial
open NumberField
open scoped Cyclotomic

abbrev Eisenstein := QuadraticAlgebra ℤ (-1) (-1)

section
variable {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {3} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

without_editor_info noncomputable def eisensteinMap : Eisenstein →ₐ[ℤ] 𝓞 K :=
  QuadraticAlgebra.lift ⟨hζ.toInteger, by
    have h := IsCyclotomicExtension.Rat.Three.eta_sq hζ
    change hζ.toInteger ^ 2 = -hζ.toInteger - 1 at h
    simpa only [neg_smul, one_smul, pow_two, sub_eq_add_neg, add_comm] using h⟩

without_editor_info theorem exists_eisenstein_coordinates (z : 𝓞 K) :
    ∃ a b : ℤ, z = a + b * hζ.toInteger := by
  let pb := hζ.integralPowerBasis
  have hd : pb.dim = 2 := by
    change hζ.integralPowerBasis.dim = 2
    rw [hζ.integralPowerBasis_dim]
    decide
  have hs := pb.basis.sum_repr z
  simp only [PowerBasis.coe_basis] at hs
  have hs' : (∑ i : Fin 2, pb.basis.repr z (Fin.cast hd.symm i) •
      pb.gen ^ (i : ℕ)) = z := by
    simpa using (Equiv.sum_comp (finCongr hd.symm)
      (fun i : Fin pb.dim => pb.basis.repr z i • pb.gen ^ (i : ℕ))).trans hs
  refine ⟨pb.basis.repr z (Fin.cast hd.symm 0),
    pb.basis.repr z (Fin.cast hd.symm 1), ?_⟩
  simpa [Fin.sum_univ_two, pb, Algebra.smul_def] using hs'.symm

without_editor_info theorem eisensteinMap_surjective : Function.Surjective (eisensteinMap hζ) := by
  intro z
  obtain ⟨a, b, rfl⟩ := exists_eisenstein_coordinates hζ z
  exact ⟨⟨a,b⟩, by simp [eisensteinMap, QuadraticAlgebra.lift, Algebra.smul_def]⟩

without_editor_info theorem eisensteinMap_injective : Function.Injective (eisensteinMap hζ) := by
  apply (injective_iff_map_eq_zero (eisensteinMap hζ)).mpr
  intro z hz
  let pb := hζ.integralPowerBasis
  have hd : pb.dim = 2 := by
    change hζ.integralPowerBasis.dim = 2
    rw [hζ.integralPowerBasis_dim]
    decide
  let b := pb.basis.reindex (finCongr hd)
  have hb0 : b 0 = 1 := by simp [b, PowerBasis.coe_basis]
  have hb1 : b 1 = hζ.toInteger := by simp [b, PowerBasis.coe_basis, pb]
  have hs : (∑ i : Fin 2, (![z.re, z.im] i) • b i) = 0 := by
    simpa [Fin.sum_univ_two, hb0, hb1, eisensteinMap,
      QuadraticAlgebra.lift, Algebra.smul_def] using hz
  have hi := Fintype.linearIndependent_iff.mp b.linearIndependent _ hs
  ext
  · exact hi 0
  · exact hi 1

without_editor_info noncomputable def eisensteinEquiv : Eisenstein ≃ₐ[ℤ] 𝓞 K :=
  AlgEquiv.ofBijective (eisensteinMap hζ)
    ⟨eisensteinMap_injective hζ, eisensteinMap_surjective hζ⟩

include hζ in
without_editor_info theorem eisenstein_isPrincipalIdealRing : IsPrincipalIdealRing Eisenstein := by
  have hp := IsCyclotomicExtension.Rat.three_pid K
  exact IsPrincipalIdealRing.of_surjective (eisensteinEquiv hζ).symm.toRingHom
    (eisensteinEquiv hζ).symm.surjective

end

private noncomputable def concreteMap :=
  eisensteinMap (IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ))

private theorem concreteMap_injective : Function.Injective concreteMap :=
  eisensteinMap_injective (IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ))

without_editor_info instance : IsDomain Eisenstein :=
  Function.Injective.isDomain concreteMap
    (eisensteinMap_injective (IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ)))

without_editor_info instance : IsPrincipalIdealRing Eisenstein :=
  eisenstein_isPrincipalIdealRing
    (IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ))

without_editor_info theorem eisenstein_norm_nonneg (z : Eisenstein) : 0 ≤ QuadraticAlgebra.norm z := by
  simp only [QuadraticAlgebra.norm_def]
  nlinarith [sq_nonneg (2 * z.re - z.im), sq_nonneg z.im]

without_editor_info theorem eisenstein_norm_eq_zero (z : Eisenstein) :
    QuadraticAlgebra.norm z = 0 ↔ z = 0 := by
  constructor
  · intro h
    simp only [QuadraticAlgebra.norm_def] at h
    have hb : z.im = 0 := by nlinarith [sq_nonneg (2 * z.re - z.im), sq_nonneg z.im]
    have ha : z.re = 0 := by nlinarith [sq_nonneg z.re]
    ext <;> assumption
  · rintro rfl; exact QuadraticAlgebra.norm_zero

abbrev ω : Eisenstein := QuadraticAlgebra.omega

without_editor_info theorem omega_primitive : IsPrimitiveRoot ω 3 := by
  apply IsPrimitiveRoot.of_map_of_injective (f := concreteMap) ?_ concreteMap_injective
  simpa [concreteMap, eisensteinMap, QuadraticAlgebra.lift,
    QuadraticAlgebra.omega] using
    (IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ)).toInteger_isPrimitiveRoot

without_editor_info theorem star_omega : star ω = ω ^ 2 := by
  ext <;> norm_num [QuadraticAlgebra.omega, pow_two]

without_editor_info theorem cubic_char_star {F : Type*} [Field F] [Fintype F]
    {χ : MulChar F Eisenstein} (hχ : orderOf χ = 3) :
    χ.ringHomComp (starRingEnd Eisenstein) = χ⁻¹ := by
  have hc : χ ^ 3 = 1 := hχ ▸ pow_orderOf_eq_one χ
  have hi : χ⁻¹ = χ ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ']; exact hc
  rw [hi]
  apply MulChar.ext
  intro x
  obtain ⟨k, _, hk⟩ := MulChar.exists_apply_eq_pow hc omega_primitive x.ne_zero
  simp only [MulChar.ringHomComp_apply, starRingEnd_apply,
    MulChar.pow_apply_coe, hk, star_pow, star_omega, ← pow_mul]
  rw [Nat.mul_comm]

without_editor_info theorem jacobi_primary {F : Type*} [Field F] [Fintype F]
    {χ : MulChar F Eisenstein} (hχ : orderOf χ = 3) :
    (3 : Eisenstein) ∣ jacobiSum χ χ + 1 := by
  have hc : χ ^ 3 = 1 := hχ ▸ pow_orderOf_eq_one χ
  have hd : 3 ∣ Fintype.card F - 1 := hχ ▸ χ.orderOf_dvd_card_sub_one
  obtain ⟨z, _, hz⟩ := exists_jacobiSum_eq_neg_one_add (by decide : 2 < 3)
    hc hc hd omega_primitive
  refine ⟨-z * ω, ?_⟩
  have hw : (ω - 1) ^ 2 = -3 * ω := by
    decide
  rw [hz, hw]; ring

without_editor_info theorem jacobi_norm {F : Type*} [Field F] [Fintype F]
    {χ : MulChar F Eisenstein} (hχ : orderOf χ = 3) :
    QuadraticAlgebra.norm (jacobiSum χ χ) = Fintype.card F := by
  let K := FractionRing Eisenstein
  let f := algebraMap Eisenstein K
  have hf : Function.Injective f := IsFractionRing.injective Eisenstein K
  have hn : χ ≠ 1 := by intro h; simp [h] at hχ
  have hnn : χ * χ ≠ 1 := by
    rw [← pow_two]
    exact pow_ne_one_of_lt_orderOf (by decide) (by omega)
  have hchar : ringChar K ≠ ringChar F := by
    obtain ⟨n, hp, _⟩ := FiniteField.card F (ringChar F)
    rw [ringChar.eq_zero]
    exact hp.ne_zero.symm
  have h := jacobiSum_mul_jacobiSum_inv hchar
    ((MulChar.ringHomComp_ne_one_iff hf).mpr hn)
    ((MulChar.ringHomComp_ne_one_iff hf).mpr hn)
    (χ := χ.ringHomComp f) (φ := χ.ringHomComp f)
    (by rw [← MulChar.ringHomComp_mul]; exact (MulChar.ringHomComp_ne_one_iff hf).mpr hnn)
  have he : jacobiSum χ χ * star (jacobiSum χ χ) = (Fintype.card F : Eisenstein) := by
    have hs : star (jacobiSum χ χ) = jacobiSum χ⁻¹ χ⁻¹ := by
      rw [← cubic_char_star hχ, jacobiSum_ringHomComp]
      rfl
    rw [hs]
    apply hf
    simpa only [map_mul, map_natCast, ← jacobiSum_ringHomComp,
      MulChar.ringHomComp_inv] using h
  have he' : ((QuadraticAlgebra.norm (jacobiSum χ χ) : ℤ) : Eisenstein) =
      (Fintype.card F : Eisenstein) := by
    change algebraMap ℤ Eisenstein (QuadraticAlgebra.norm (jacobiSum χ χ)) = _
    rwa [QuadraticAlgebra.algebraMap_norm_eq_mul_star]
  exact_mod_cast he'

end CubicSpecial



namespace CubicSpecial
open MulChar Polynomial

without_editor_info def powerChar (F : Type*) [Field F] (n : ℕ) (hn : n ≠ 0) : MulChar F F where
  toFun x := x ^ n
  map_one' := one_pow n
  map_mul' := fun x y => mul_pow x y n
  map_nonunit' := by
    intro x hx
    have hx' : x = 0 := by simpa [isUnit_iff_ne_zero] using hx
    simp [hx', hn]

without_editor_info theorem sum_polynomial_eq_zero {F : Type*} [Field F] [Fintype F]
    (f : F[X]) (h : f.natDegree < Fintype.card F - 1) :
    ∑ x : F, f.eval x = 0 := by
  classical
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← Finset.mul_sum, FiniteField.sum_pow_lt_card_sub_one F i
    (by have := Finset.mem_range.mp hi; omega), mul_zero]

without_editor_info theorem jacobi_reduction_zero {F R : Type*} [Field F] [Fintype F]
    [CommRing R] (f : R →+* F) (χ : MulChar F R)
    (hq : Fintype.card F % 3 = 1)
    (he : ∀ x, f (χ x) = x ^ ((Fintype.card F - 1) / 3)) :
    f (jacobiSum χ χ) = 0 := by
  let d := (Fintype.card F - 1) / 3
  have hd : 2 * d < Fintype.card F - 1 := by
    have := Fintype.one_lt_card (α := F)
    dsimp [d]; omega
  have h := sum_polynomial_eq_zero
    ((Polynomial.X : F[X]) ^ d * (1 - Polynomial.X) ^ d) (by
      apply lt_of_le_of_lt Polynomial.natDegree_mul_le ?_
      simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]
      have hle : (1 - Polynomial.X : F[X]).natDegree ≤ 1 := by
        apply (Polynomial.natDegree_sub_le _ _).trans
        simp
      nlinarith)
  simpa [jacobiSum, map_sum, map_mul, he, d] using h

without_editor_info theorem exists_cubic_residue_char {F R : Type*} [Field F] [Fintype F]
    [CommRing R] [IsDomain R] (f : R →+* F) {μ : R}
    (hμ : IsPrimitiveRoot μ 3) (hμf : IsPrimitiveRoot (f μ) 3)
    (hq : Fintype.card F % 3 = 1) :
    ∃ χ : MulChar F R, orderOf χ = 3 ∧
      ∀ x, f (χ x) = x ^ ((Fintype.card F - 1) / 3) := by
  classical
  let d := (Fintype.card F - 1) / 3
  have hqpos := Fintype.one_lt_card (α := F)
  have hd : d ≠ 0 := by dsimp [d]; omega
  have h3d : d * 3 = Fintype.card F - 1 := by dsimp [d]; omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hgd : ((g : F) ^ d) ^ 3 = 1 := by
    rw [← pow_mul, h3d]
    exact FiniteField.pow_card_sub_one_eq_one _ g.ne_zero
  obtain ⟨k, _, hk⟩ := hμf.eq_pow_of_pow_eq_one hgd
  have hunit : IsUnit (μ ^ k) := (hμ.isUnit (by decide)).pow k
  let v : Rˣ := hunit.unit
  have hv : (v : R) = μ ^ k := hunit.unit_spec
  have hv3 : v ^ 3 = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one, hv, ← pow_mul]
    rw [Nat.mul_comm, pow_mul, hμ.pow_eq_one, one_pow]
  have hvq : v ∈ rootsOfUnity (Fintype.card Fˣ) R := by
    apply (mem_rootsOfUnity _ _).mpr
    rw [Fintype.card_units, ← h3d, Nat.mul_comm, pow_mul, hv3, one_pow]
  let χ := MulChar.ofRootOfUnity hvq hg
  have hχg : χ (g : F) = v := MulChar.ofRootOfUnity_spec hvq hg
  have hχpow : χ ^ 3 = 1 := by
    apply (MulChar.eq_iff hg _ _).mpr
    simpa only [MulChar.pow_apply_coe, MulChar.one_apply_coe, hχg,
      ← Units.val_pow_eq_pow_val, hv3, Units.val_one]
  have hcomp : χ.ringHomComp f = powerChar F d hd := by
    apply (MulChar.eq_iff hg _ _).mpr
    change f (χ (g : F)) = (g : F) ^ d
    rw [hχg, hv, map_pow]
    exact hk
  have hne : χ ≠ 1 := by
    intro heq
    have hgd1 : (g : F) ^ d = 1 := by
      have h := DFunLike.congr_fun hcomp (g : F)
      simpa [heq, powerChar] using h.symm
    have ho : orderOf g = Fintype.card F - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
        Fintype.card_units]
    have hdvd : Fintype.card F - 1 ∣ d := by
      rw [← ho]
      exact orderOf_dvd_of_pow_eq_one (Units.ext hgd1)
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hdvd
    omega
  have hthree : Fact (Nat.Prime 3) := ⟨by decide⟩
  refine ⟨χ, orderOf_eq_prime hχpow hne, fun x => ?_⟩
  exact DFunLike.congr_fun hcomp x

end CubicSpecial

namespace CubicSpecial

without_editor_info theorem norm_one_primary_unit (z : Eisenstein)
    (hn : QuadraticAlgebra.norm z = 1) (h3 : (3 : Eisenstein) ∣ z - 1) : z = 1 := by
  have hn' := hn
  simp only [QuadraticAlgebra.norm_def] at hn'
  have ha : -1 ≤ z.re ∧ z.re ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (2 * z.im - z.re)]
  have hb : -1 ≤ z.im ∧ z.im ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (2 * z.re - z.im)]
  have h3' : (3 : ℤ) ∣ z.re - 1 ∧ (3 : ℤ) ∣ z.im := by
    change algebraMap ℤ Eisenstein 3 ∣ z - 1 at h3
    simpa only [QuadraticAlgebra.algebraMap_dvd_iff, QuadraticAlgebra.re_sub,
      QuadraticAlgebra.im_sub, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
      sub_zero] using h3
  ext
  · change z.re = 1; omega
  · change z.im = 0; omega

without_editor_info theorem jacobi_eq_primary {F : Type*} [Field F] [Fintype F]
    (f : Eisenstein →+* F) (π : Eisenstein)
    (hπ : (3 : Eisenstein) ∣ π + 1)
    (hN : QuadraticAlgebra.norm π = Fintype.card F)
    (hk : ∀ z, f z = 0 ↔ π ∣ z)
    (hq : Fintype.card F % 3 = 1)
    {χ : MulChar F Eisenstein} (hχ : orderOf χ = 3)
    (he : ∀ x, f (χ x) = x ^ ((Fintype.card F - 1) / 3)) :
    jacobiSum χ χ = π := by
  obtain ⟨w, hw⟩ := (hk _).mp (jacobi_reduction_zero f χ hq he)
  have hjn := jacobi_norm hχ
  have hnpos : (0 : ℤ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hwN : QuadraticAlgebra.norm w = 1 := by
    rw [hw, map_mul, hN] at hjn
    nlinarith
  have hjp := jacobi_primary hχ
  obtain ⟨a, ha⟩ := hπ
  obtain ⟨b, hb⟩ := hjp
  have hwp : (3 : Eisenstein) ∣ w - 1 := by
    refine ⟨a * w - b, ?_⟩
    calc w - 1 = (π + 1) * w - (jacobiSum χ χ + 1) := by rw [hw]; ring
      _ = 3 * (a * w - b) := by rw [ha, hb]; ring
  rw [norm_one_primary_unit w hwN hwp, mul_one] at hw
  exact hw

end CubicSpecial

namespace CubicSpecial
open scoped QuadraticAlgebra

abbrev Residue (π : Eisenstein) := Eisenstein ⧸ Ideal.span {π}

without_editor_info theorem residue_card (π : Eisenstein) :
    Nat.card (Residue π) = (QuadraticAlgebra.norm π).natAbs := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton,
    Algebra.norm_apply]
  congr 1
  exact QuadraticAlgebra.det_toLinearMap_eq_norm π

without_editor_info noncomputable instance residue_field (π : Eisenstein) [hπ : Fact (Prime π)] :
    Field (Residue π) := by
  have hm : (Ideal.span {π}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hπ.out.irreducible
  exact Ideal.Quotient.field (Ideal.span {π})

without_editor_info instance residue_finite (π : Eisenstein) [hπ : Fact (Prime π)] : Finite (Residue π) := by
  apply Nat.finite_of_card_ne_zero
  rw [residue_card, Int.natAbs_ne_zero]
  exact fun h => hπ.out.ne_zero ((eisenstein_norm_eq_zero π).mp h)

without_editor_info noncomputable instance residue_fintype (π : Eisenstein) [Fact (Prime π)] :
    Fintype (Residue π) := Fintype.ofFinite _

without_editor_info def reduction (π : Eisenstein) : Eisenstein →+* Residue π :=
  Ideal.Quotient.mk (Ideal.span {π})

without_editor_info theorem reduction_zero (π z : Eisenstein) : reduction π z = 0 ↔ π ∣ z := by
  rw [reduction, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

without_editor_info theorem residue_omega_primitive (π : Eisenstein) [Fact (Prime π)]
    (h3 : ¬ π ∣ 3) : IsPrimitiveRoot (reduction π ω) 3 := by
  have hpow : (reduction π ω) ^ 3 = 1 := by
    rw [← map_pow, omega_primitive.pow_eq_one, map_one]
  have hne : reduction π ω ≠ 1 := by
    intro h
    have hdiv : π ∣ ω - 1 := (reduction_zero π _).mp (by rw [map_sub, map_one, h, sub_self])
    apply h3
    have hw : (3 : Eisenstein) = -(ω ^ 2) * (ω - 1) ^ 2 := by decide
    rw [hw]
    exact dvd_mul_of_dvd_right (dvd_pow hdiv (by decide : 2 ≠ 0)) _
  have hthree : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hpow hne)

without_editor_info theorem exists_prime_character (π : Eisenstein) [Fact (Prime π)]
    (h3 : ¬ π ∣ 3) (hp : (3 : Eisenstein) ∣ π + 1) :
    ∃ χ : MulChar (Residue π) Eisenstein, orderOf χ = 3 ∧
      (∀ x, reduction π (χ x) = x ^ ((Fintype.card (Residue π) - 1) / 3)) ∧
      jacobiSum χ χ = π := by
  have hω := residue_omega_primitive π h3
  have hd : 3 ∣ Fintype.card (Residue π) - 1 := hω.dvd_of_pow_eq_one _
    (FiniteField.pow_card_sub_one_eq_one _ (hω.ne_zero (by decide)))
  have hq : Fintype.card (Residue π) % 3 = 1 := by
    have := Fintype.one_lt_card (α := Residue π)
    omega
  obtain ⟨χ, hχ, he⟩ := exists_cubic_residue_char (reduction π) omega_primitive hω hq
  refine ⟨χ, hχ, he, jacobi_eq_primary (reduction π) π hp ?_ (reduction_zero π) hq hχ he⟩
  have h := residue_card π
  rw [Nat.card_eq_fintype_card] at h
  rw [h, Int.natCast_natAbs, abs_of_nonneg (eisenstein_norm_nonneg π)]

end CubicSpecial


namespace CubicSpecial

without_editor_info def CubicValue (a : Eisenstein) : Prop := a = 0 ∨ a ^ 3 = 1

without_editor_info theorem cubic_value_pow {a : Eisenstein} (h : CubicValue a) (n : ℕ) :
    CubicValue (a ^ n) := by
  rcases h with rfl | h
  · cases n <;> simp [CubicValue]
  · right; rw [← pow_mul, Nat.mul_comm, pow_mul, h, one_pow]

without_editor_info theorem char_cubic_value {F : Type*} [Field F] [Fintype F]
    {χ : MulChar F Eisenstein} (hχ : orderOf χ = 3) (x : F) : CubicValue (χ x) := by
  by_cases hx : x = 0
  · left; rw [hx]; exact χ.map_zero
  · right
    have h := DFunLike.congr_fun (hχ ▸ pow_orderOf_eq_one χ : χ ^ 3 = 1) x
    simpa only [MulChar.pow_apply' χ (by decide : 3 ≠ 0),
      MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)] using h

without_editor_info theorem cubic_value_injective {F : Type*} [Field F]
    (f : Eisenstein →+* F) (hω : IsPrimitiveRoot (f ω) 3)
    {a b : Eisenstein} (ha : CubicValue a) (hb : CubicValue b)
    (he : f a = f b) : a = b := by
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · rfl
  · have h := congrArg f hb
    rw [map_pow, ← he, map_zero, zero_pow (by decide : 3 ≠ 0), map_one] at h
    exact False.elim (zero_ne_one h)
  · have h := congrArg f ha
    rw [map_pow, he, map_zero, zero_pow (by decide : 3 ≠ 0), map_one] at h
    exact False.elim (zero_ne_one h)
  · obtain ⟨i, hi, rfl⟩ := omega_primitive.eq_pow_of_pow_eq_one ha
    obtain ⟨j, hj, rfl⟩ := omega_primitive.eq_pow_of_pow_eq_one hb
    simp only [map_pow] at he
    rw [hω.pow_inj hi hj he]

without_editor_info theorem mapped_char_order {F E : Type*} [Field F] [Fintype F] [Field E]
    (f : Eisenstein →+* E) (hω : IsPrimitiveRoot (f ω) 3)
    {χ : MulChar F Eisenstein} (hχ : orderOf χ = 3) :
    orderOf (χ.ringHomComp f) = 3 := by
  have hp : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply orderOf_eq_prime
  · rw [MulChar.ringHomComp_pow]
    simp only [show χ ^ 3 = 1 from hχ ▸ pow_orderOf_eq_one χ, MulChar.ringHomComp_one]
  · intro h
    have hc : χ = 1 := by
      apply MulChar.ext
      intro x
      apply cubic_value_injective f hω (char_cubic_value hχ _) (by right; simp)
      simpa only [MulChar.ringHomComp_apply, MulChar.one_apply_coe, map_one] using
        DFunLike.congr_fun h (x : F)
    simp [hc] at hχ

without_editor_info theorem jacobi_reciprocity_relation {F E : Type*} [Field F] [Fintype F]
    [Field E] [Fintype E] (g : Eisenstein →+* E)
    (hω : IsPrimitiveRoot (g ω) 3)
    {χ : MulChar F Eisenstein} {ψ : MulChar E Eisenstein}
    (hχ : orderOf χ = 3) (hψ : orderOf ψ = 3)
    (hchar : ringChar E ≠ ringChar F)
    (he : ∀ x, g (ψ x) = x ^ ((Fintype.card E - 1) / 3)) :
    ψ (g (Fintype.card F * jacobiSum χ χ)) = χ (Fintype.card E) ^ 2 := by
  have hd : 3 ∣ Fintype.card E - 1 := hψ ▸ ψ.orderOf_dvd_card_sub_one
  have hq : Fintype.card E % 3 = 1 := by
    have := Fintype.one_lt_card (α := E); omega
  have h := jacobi_cubic_residue (mapped_char_order g hω hχ) hchar hq
  apply cubic_value_injective g hω (char_cubic_value hψ _)
    (cubic_value_pow (char_cubic_value hχ _) 2)
  simpa only [he, map_mul, map_natCast, jacobiSum_ringHomComp, map_pow, mul_pow,
    MulChar.ringHomComp_apply] using h

without_editor_info theorem cubic_two_relations {a b c d : Eisenstein}
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1)
    (h₁ : c ^ 2 * d = (a * b) ^ 2)
    (h₂ : a ^ 2 * b = (c * d) ^ 2) : a = c := by
  have hane : a ≠ 0 := by intro h; simp [h] at ha
  have hbne : b ≠ 0 := by intro h; simp [h] at hb
  have hbd : b * d = 1 := by
    apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 hane) hbne)
    linear_combination -d * h₁ - h₂
  have hsq : c ^ 2 = a ^ 2 := by
    linear_combination b * h₁ - c ^ 2 * hbd + a ^ 2 * hb
  calc a = (a ^ 2) ^ 2 := by rw [← pow_mul, show 2 * 2 = 3 + 1 by decide, pow_succ, ha, one_mul]
    _ = (c ^ 2) ^ 2 := by rw [hsq]
    _ = c := by rw [← pow_mul, show 2 * 2 = 3 + 1 by decide, pow_succ, hc, one_mul]

without_editor_info theorem finite_field_card_cast_ne_zero (F E : Type*) [Field F] [Fintype F]
    [Field E] [Fintype E] (hchar : ringChar F ≠ ringChar E) :
    (Fintype.card E : F) ≠ 0 := by
  obtain ⟨n, hp, hc⟩ := FiniteField.card E (ringChar E)
  rw [hc, Nat.cast_pow]
  apply pow_ne_zero
  exact fun h => hchar (CharP.ringChar_of_prime_eq_zero hp h)

without_editor_info theorem char_cube {F : Type*} [Field F] [Fintype F]
    {χ : MulChar F Eisenstein} (hχ : orderOf χ = 3) {x : F} (hx : x ≠ 0) :
    χ x ^ 3 = 1 := by
  apply (char_cubic_value hχ x).resolve_left
  exact (MulChar.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr hx))

without_editor_info theorem jacobi_mul_star {F : Type*} [Field F] [Fintype F]
    {χ : MulChar F Eisenstein} (hχ : orderOf χ = 3) :
    (Fintype.card F : Eisenstein) = jacobiSum χ χ * star (jacobiSum χ χ) := by
  rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, jacobi_norm hχ]
  rfl

without_editor_info theorem jacobi_reciprocity {F E : Type*} [Field F] [Fintype F]
    [Field E] [Fintype E] (f : Eisenstein →+* F) (g : Eisenstein →+* E)
    (hωf : IsPrimitiveRoot (f ω) 3) (hωg : IsPrimitiveRoot (g ω) 3)
    {χ : MulChar F Eisenstein} {ψ : MulChar E Eisenstein}
    (hχ : orderOf χ = 3) (hψ : orderOf ψ = 3)
    (hchar : ringChar E ≠ ringChar F)
    (hef : ∀ x, f (χ x) = x ^ ((Fintype.card F - 1) / 3))
    (heg : ∀ x, g (ψ x) = x ^ ((Fintype.card E - 1) / 3)) :
    χ (f (jacobiSum ψ ψ)) = ψ (g (jacobiSum χ χ)) := by
  have hNχ := jacobi_mul_star hχ
  have hNψ := jacobi_mul_star hψ
  have hnf : f (jacobiSum ψ ψ) ≠ 0 ∧ f (star (jacobiSum ψ ψ)) ≠ 0 := by
    apply mul_ne_zero_iff.mp
    rw [← map_mul, ← hNψ, map_natCast]
    exact finite_field_card_cast_ne_zero F E hchar.symm
  have hng : g (jacobiSum χ χ) ≠ 0 ∧ g (star (jacobiSum χ χ)) ≠ 0 := by
    apply mul_ne_zero_iff.mp
    rw [← map_mul, ← hNχ, map_natCast]
    exact finite_field_card_cast_ne_zero E F hchar
  apply cubic_two_relations (char_cube hχ hnf.1) (char_cube hχ hnf.2)
    (char_cube hψ hng.1) (d := ψ (g (star (jacobiSum χ χ))))
  · have h := jacobi_reciprocity_relation g hωg hχ hψ hchar heg
    have h' : ψ (g ((Fintype.card F : Eisenstein) * jacobiSum χ χ)) =
        χ (f (Fintype.card E : Eisenstein)) ^ 2 := by
      simpa only [map_natCast] using h
    rw [hNχ, hNψ] at h'
    simp only [map_mul] at h'
    convert h' using 1 <;> ring
  · have h := jacobi_reciprocity_relation f hωf hψ hχ hchar.symm hef
    have h' : χ (f ((Fintype.card E : Eisenstein) * jacobiSum ψ ψ)) =
        ψ (g (Fintype.card F : Eisenstein)) ^ 2 := by
      simpa only [map_natCast] using h
    rw [hNχ, hNψ] at h'
    simp only [map_mul] at h'
    convert h' using 1 <;> ring

without_editor_info theorem cubic_reciprocity_distinct_characteristic
    (π ρ : Eisenstein) [Fact (Prime π)] [Fact (Prime ρ)]
    (hπ3 : ¬ π ∣ 3) (hρ3 : ¬ ρ ∣ 3)
    (hπ : (3 : Eisenstein) ∣ π + 1) (hρ : (3 : Eisenstein) ∣ ρ + 1)
    (hchar : ringChar (Residue ρ) ≠ ringChar (Residue π)) :
    ∃ χ : MulChar (Residue π) Eisenstein,
      ∃ ψ : MulChar (Residue ρ) Eisenstein,
        orderOf χ = 3 ∧ orderOf ψ = 3 ∧
        (∀ x, reduction π (χ x) = x ^ ((Fintype.card (Residue π) - 1) / 3)) ∧
        (∀ x, reduction ρ (ψ x) = x ^ ((Fintype.card (Residue ρ) - 1) / 3)) ∧
        χ (reduction π ρ) = ψ (reduction ρ π) := by
  obtain ⟨χ, hχ, heχ, hjχ⟩ := exists_prime_character π hπ3 hπ
  obtain ⟨ψ, hψ, heψ, hjψ⟩ := exists_prime_character ρ hρ3 hρ
  refine ⟨χ, ψ, hχ, hψ, heχ, heψ, ?_⟩
  have h := jacobi_reciprocity (reduction π) (reduction ρ)
    (residue_omega_primitive π hπ3) (residue_omega_primitive ρ hρ3)
    hχ hψ hchar heχ heψ
  simpa only [hjχ, hjψ] using h

end CubicSpecial


namespace CubicSpecial

without_editor_info theorem residue_card_mod_three (π : Eisenstein) [Fact (Prime π)]
    (h3 : ¬ π ∣ 3) : Fintype.card (Residue π) % 3 = 1 := by
  have hω := residue_omega_primitive π h3
  have hd := hω.dvd_of_pow_eq_one _
    (FiniteField.pow_card_sub_one_eq_one _ (hω.ne_zero (by decide)))
  have := Fintype.one_lt_card (α := Residue π)
  omega

without_editor_info noncomputable def primeCharacter (π : Eisenstein) [Fact (Prime π)] (h3 : ¬ π ∣ 3) :
    MulChar (Residue π) Eisenstein :=
  (exists_cubic_residue_char (reduction π) omega_primitive
    (residue_omega_primitive π h3) (residue_card_mod_three π h3)).choose

without_editor_info theorem primeCharacter_spec (π : Eisenstein) [Fact (Prime π)] (h3 : ¬ π ∣ 3) :
    orderOf (primeCharacter π h3) = 3 ∧
      ∀ x, reduction π (primeCharacter π h3 x) =
        x ^ ((Fintype.card (Residue π) - 1) / 3) :=
  (exists_cubic_residue_char (reduction π) omega_primitive
    (residue_omega_primitive π h3) (residue_card_mod_three π h3)).choose_spec

without_editor_info theorem primeCharacter_unique (π : Eisenstein) [Fact (Prime π)] (h3 : ¬ π ∣ 3)
    {χ : MulChar (Residue π) Eisenstein} (hχ : orderOf χ = 3)
    (he : ∀ x, reduction π (χ x) = x ^ ((Fintype.card (Residue π) - 1) / 3)) :
    χ = primeCharacter π h3 := by
  apply MulChar.ext
  intro x
  apply cubic_value_injective (reduction π) (residue_omega_primitive π h3)
    (char_cubic_value hχ _) (char_cubic_value (primeCharacter_spec π h3).1 _)
  rw [he, (primeCharacter_spec π h3).2]

without_editor_info noncomputable def cubicSymbol (π : Eisenstein) [Fact (Prime π)] (h3 : ¬ π ∣ 3)
    (a : Eisenstein) : Eisenstein := primeCharacter π h3 (reduction π a)

without_editor_info theorem cubicSymbol_mul (π : Eisenstein) [Fact (Prime π)] (h3 : ¬ π ∣ 3)
    (a b : Eisenstein) : cubicSymbol π h3 (a*b) = cubicSymbol π h3 a * cubicSymbol π h3 b := by
  simp [cubicSymbol, map_mul]

without_editor_info theorem cubicSymbol_eq_zero (π : Eisenstein) [Fact (Prime π)] (h3 : ¬ π ∣ 3)
    (a : Eisenstein) : cubicSymbol π h3 a = 0 ↔ π ∣ a := by
  rw [cubicSymbol, MulChar.apply_eq_zero_iff]
  simpa only [isUnit_iff_ne_zero, not_not] using reduction_zero π a

without_editor_info theorem cubicSymbol_cube (π : Eisenstein) [Fact (Prime π)] (h3 : ¬ π ∣ 3)
    {a : Eisenstein} (ha : ¬ π ∣ a) : cubicSymbol π h3 a ^ 3 = 1 :=
  char_cube (primeCharacter_spec π h3).1 (mt (reduction_zero π a).mp ha)

without_editor_info theorem cubicSymbol_neg_one (π : Eisenstein) [Fact (Prime π)] (h3 : ¬ π ∣ 3) :
    cubicSymbol π h3 (-1) = 1 := by
  simpa [cubicSymbol] using MulChar.val_neg_one_eq_one_of_odd_order (χ := primeCharacter π h3)
    (by decide : Odd 3) ((primeCharacter_spec π h3).1 ▸ pow_orderOf_eq_one _)

without_editor_info theorem primeCharacter_jacobi (π : Eisenstein) [Fact (Prime π)] (h3 : ¬ π ∣ 3)
    (hp : (3 : Eisenstein) ∣ π+1) : jacobiSum (primeCharacter π h3) (primeCharacter π h3) = π := by
  obtain ⟨χ,hχ,he,hj⟩ := exists_prime_character π h3 hp
  rwa [primeCharacter_unique π h3 hχ he] at hj

without_editor_info theorem cubicSymbol_reciprocity_distinct_characteristic
    (π ρ : Eisenstein) [Fact (Prime π)] [Fact (Prime ρ)]
    (hπ3 : ¬ π ∣ 3) (hρ3 : ¬ ρ ∣ 3)
    (hπ : (3 : Eisenstein) ∣ π+1) (hρ : (3 : Eisenstein) ∣ ρ+1)
    (hc : ringChar (Residue ρ) ≠ ringChar (Residue π)) :
    cubicSymbol π hπ3 ρ = cubicSymbol ρ hρ3 π := by
  obtain ⟨χ,ψ,hχ,hψ,heχ,heψ,h⟩ :=
    cubic_reciprocity_distinct_characteristic π ρ hπ3 hρ3 hπ hρ hc
  simpa only [primeCharacter_unique π hπ3 hχ heχ,
    primeCharacter_unique ρ hρ3 hψ heψ, cubicSymbol] using h

without_editor_info theorem norm_unit (u : Eisensteinˣ) : QuadraticAlgebra.norm (u : Eisenstein) = 1 := by
  have h := congrArg QuadraticAlgebra.norm (u.mul_inv : (u : Eisenstein) * ↑u⁻¹ = 1)
  rw [map_mul, map_one] at h
  have ha := eisenstein_norm_nonneg (u : Eisenstein)
  have hb := eisenstein_norm_nonneg (u⁻¹ : Eisensteinˣ)
  have : QuadraticAlgebra.norm (u : Eisenstein) ∣ 1 := ⟨_, h.symm⟩
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h with h | h
  · exact h
  · omega

without_editor_info theorem primary_associated_eq {a b : Eisenstein}
    (ha : (3 : Eisenstein) ∣ a+1) (hb : (3 : Eisenstein) ∣ b+1)
    (hab : Associated a b) : a = b := by
  obtain ⟨u,hu⟩ := hab
  obtain ⟨r,hr⟩ := ha
  obtain ⟨s,hs⟩ := hb
  have hunit : (u : Eisenstein) = 1 := by
    apply norm_one_primary_unit _ (norm_unit u)
    refine ⟨r * u - s, ?_⟩
    calc (u : Eisenstein)-1 = (a+1)*u-(b+1) := by rw [← hu]; ring
      _ = 3*(r*u-s) := by rw [hr,hs]; ring
  simpa [hunit] using hu

without_editor_info theorem star_dvd_of_dvd {a b : Eisenstein} (h : a ∣ b) : star a ∣ star b := by
  obtain ⟨c,hc⟩ := h
  exact ⟨star c, by simpa only [star_mul, mul_comm] using congrArg star hc⟩

without_editor_info theorem prime_star {a : Eisenstein} (ha : Prime a) : Prime (star a) := by
  refine ⟨by simpa using ha.ne_zero, ?_, ?_⟩
  · intro hu
    apply ha.not_unit
    simpa only [starRingEnd_apply, star_star] using hu.map (starRingEnd Eisenstein)
  · intro b c h
    have h' : a ∣ star b * star c := by
      simpa only [star_mul, star_star, mul_comm] using star_dvd_of_dvd h
    rcases ha.dvd_or_dvd h' with h | h
    · left; simpa only [star_star] using star_dvd_of_dvd h
    · right; simpa only [star_star] using star_dvd_of_dvd h

without_editor_info theorem primary_star {a : Eisenstein} (ha : (3 : Eisenstein) ∣ a+1) :
    (3 : Eisenstein) ∣ star a+1 := by
  simpa only [star_add, star_one, star_ofNat] using star_dvd_of_dvd ha

without_editor_info theorem residue_norm (π : Eisenstein) [Fact (Prime π)] :
    QuadraticAlgebra.norm π = Fintype.card (Residue π) := by
  rw [← Nat.card_eq_fintype_card, residue_card, Int.natCast_natAbs,
    abs_of_nonneg (eisenstein_norm_nonneg π)]

without_editor_info theorem same_characteristic_primary {π ρ : Eisenstein} [hπ : Fact (Prime π)]
    [hρ : Fact (Prime ρ)] (hp : (3 : Eisenstein) ∣ π+1)
    (hr : (3 : Eisenstein) ∣ ρ+1)
    (hc : ringChar (Residue ρ) = ringChar (Residue π)) : ρ = π ∨ ρ = star π := by
  have hd : ρ ∣ (ringChar (Residue π) : Eisenstein) := by
    apply (reduction_zero ρ _).mp
    rw [map_natCast, ← hc, CharP.cast_eq_zero]
  obtain ⟨n, _, hn⟩ := FiniteField.card (Residue π) (ringChar (Residue π))
  have hdN : ρ ∣ ((QuadraticAlgebra.norm π : ℤ) : Eisenstein) := by
    rw [residue_norm π, Int.cast_natCast, hn, Nat.cast_pow]
    exact dvd_pow hd (by exact_mod_cast n.pos.ne')
  change ρ ∣ algebraMap ℤ Eisenstein (QuadraticAlgebra.norm π) at hdN
  rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star] at hdN
  rcases hρ.out.dvd_or_dvd hdN with h | h
  · exact Or.inl (primary_associated_eq hr hp (hρ.out.associated_of_dvd hπ.out h))
  · exact Or.inr (primary_associated_eq hr (primary_star hp)
      (hρ.out.associated_of_dvd (prime_star hπ.out) h))

end CubicSpecial


namespace CubicSpecial
open scoped QuadraticAlgebra

without_editor_info theorem eisenstein_coordinates (z : Eisenstein) :
    z = (z.re : Eisenstein) + (z.im : Eisenstein) * ω := by
  ext <;> simp [QuadraticAlgebra.omega]

without_editor_info theorem star_coordinates (z : Eisenstein) :
    star z = z - (z.im : Eisenstein) * (2 * ω + 1) := by
  ext <;> simp [QuadraticAlgebra.omega] <;> ring

without_editor_info theorem split_residue_card (π : Eisenstein) [hπ : Fact (Prime π)]
    (hp : (3 : Eisenstein) ∣ π+1) (hne : π ≠ star π) :
    Fintype.card (Residue π) = ringChar (Residue π) := by
  let F := Residue π
  let f := reduction π
  let p := ringChar F
  obtain ⟨n,hprime,hn⟩ := FiniteField.card F p
  have hpFact : Fact p.Prime := ⟨hprime⟩
  let g := ZMod.castHom (dvd_refl p) F
  have hfπ : f π = 0 := (reduction_zero π π).mpr dvd_rfl
  have hb : (π.im : F) ≠ 0 := by
    intro hb
    have hbar : f (star π) = 0 := by
      rw [star_coordinates, map_sub, map_mul, map_intCast, hb, zero_mul, sub_zero, hfπ]
    exact hne (primary_associated_eq hp (primary_star hp)
      (hπ.out.associated_of_dvd (prime_star hπ.out) ((reduction_zero π _).mp hbar)))
  have hpzero : (π.re : F) + (π.im : F) * f ω = 0 := by
    simpa only [map_add, map_mul, map_intCast] using
      (congrArg f (eisenstein_coordinates π)).symm.trans hfπ
  let t : ZMod p := -(π.re : ZMod p) / (π.im : ZMod p)
  have ht : g t = f ω := by
    dsimp only [t]
    rw [map_div₀, map_neg, map_intCast, map_intCast]
    apply (div_eq_iff hb).mpr
    linear_combination -hpzero
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨w,hw⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨(w.re : ZMod p) + (w.im : ZMod p) * t, ?_⟩
    rw [map_add, map_mul, map_intCast, map_intCast, ht]
    change (w.re : F) + (w.im : F) * f ω = z
    rw [← map_intCast f, ← map_intCast f, ← map_mul, ← map_add,
      ← eisenstein_coordinates]
    exact hw
  have hc := Fintype.card_congr (Equiv.ofBijective g ⟨g.injective,hg⟩)
  simpa only [ZMod.card] using hc.symm

end CubicSpecial


namespace CubicSpecial
open scoped Nat

without_editor_info theorem wilson_cubic_binomial {p k : ℕ} [hp : Fact p.Prime]
    (hpk : p = 3*k+1) : ∃ z : ZMod p, z^3 = -((2*k).choose k : ZMod p) := by
  have hkpos : 0 < k := by have := hp.out.two_le; omega
  have hkeven : Even k := by
    have h := hp.out.even_sub_one (by omega)
    rw [hpk] at h
    rw [even_iff_two_dvd] at h ⊢
    omega
  have hfac := congrArg (fun n : ℕ => (n : ZMod p))
    (Nat.factorial_mul_descFactorial (show k ≤ p-1 by omega))
  simp only [Nat.cast_mul] at hfac
  rw [ZMod.cast_descFactorial (by omega), hkeven.neg_one_pow, one_mul,
    show p-1-k=2*k by omega, ZMod.wilsons_lemma] at hfac
  have hkne : (k.factorial : ZMod p) ≠ 0 := by
    intro h
    rw [h,mul_zero] at hfac
    exact (neg_ne_zero.mpr one_ne_zero) hfac.symm
  have hchoose := congrArg (fun n : ℕ => (n : ZMod p))
    (Nat.choose_mul_factorial_mul_factorial (show k ≤ 2*k by omega))
  simp only [Nat.cast_mul, show 2*k-k=k by omega] at hchoose
  refine ⟨(k.factorial : ZMod p)⁻¹, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 3 hkne)
  calc (k.factorial : ZMod p)^3 * ((k.factorial : ZMod p)⁻¹)^3 = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hkne, one_pow]
    _ = (k.factorial : ZMod p)^3 * -((2*k).choose k : ZMod p) := by
        linear_combination hfac + (k.factorial : ZMod p) * hchoose

without_editor_info theorem finite_sum_pow {F : Type*} [Field F] [Fintype F] (n : ℕ) (hn : n ≠ 0) :
    ∑ x : F, x^n = if Fintype.card F - 1 ∣ n then -1 else 0 := by
  classical
  let unitEmb : Fˣ ↪ F := ⟨fun x => x, Units.val_injective⟩
  have hm : Finset.univ.map unitEmb = Finset.univ \ {(0 : F)} := by
    ext x
    simpa only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk,
      true_and, Finset.mem_sdiff, Finset.mem_singleton, unitEmb] using! isUnit_iff_ne_zero
  calc
    (∑ x : F, x^n) = ∑ x ∈ Finset.univ \ {(0 : F)}, x^n := by
      rw [← Finset.sum_sdiff ({0} : Finset F).subset_univ, Finset.sum_singleton,
        zero_pow hn, add_zero]
    _ = ∑ x : Fˣ, (x : F)^n := by simp [unitEmb, ← hm, Finset.univ.sum_map unitEmb]
    _ = _ := FiniteField.sum_pow_units F n

without_editor_info theorem conjugate_power_sum {F : Type*} [Field F] [Fintype F] {k : ℕ}
    (hk : 0 < k) (heven : Even k) (hq : Fintype.card F = 3*k+1) :
    ∑ x : F, x^(2*k) * (1-x)^(2*k) = -((2*k).choose k : F) := by
  classical
  have hexpand (x : F) : (1-x)^(2*k) =
      ∑ i ∈ Finset.range (2*k+1), (-1)^i * ((2*k).choose i : F) * x^i := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro i hi
    rw [neg_pow, one_pow]
    ring
  have hsum : (∑ x : F, x^(2*k)*(1-x)^(2*k)) =
      ∑ i ∈ Finset.range (2*k+1), (-1)^i * ((2*k).choose i : F) * (∑ x : F, x^(2*k+i)) := by
    simp_rw [hexpand, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro x hx
    rw [pow_add]
    ring
  rw [hsum, Finset.sum_eq_single k]
  · rw [finite_sum_pow _ (by omega), hq,
      show 3*k+1-1=3*k by omega, show 2*k+k=3*k by omega,
      if_pos dvd_rfl, heven.neg_one_pow, one_mul, mul_neg_one]
  · intro i hi hik
    rw [finite_sum_pow _ (by omega), if_neg, mul_zero]
    rw [hq, show 3*k+1-1=3*k by omega]
    intro hd
    obtain ⟨j,hj⟩ := hd
    have hi' := Finset.mem_range.mp hi
    have hjpos : 0 < j := by nlinarith
    have hjlt : j < 2 := by nlinarith
    have : j=1 := by omega
    subst j
    omega
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by omega)))

end CubicSpecial


namespace CubicSpecial

without_editor_info theorem cubic_char_inverse_square {F : Type*} [Field F] [Fintype F]
    {χ : MulChar F Eisenstein} (hχ : orderOf χ = 3) : χ⁻¹ = χ^2 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ']
  simpa only [hχ] using pow_orderOf_eq_one χ

without_editor_info theorem star_jacobi_reduction {F : Type*} [Field F] [Fintype F]
    (f : Eisenstein →+* F) {χ : MulChar F Eisenstein} (hχ : orderOf χ=3)
    {k : ℕ} (hk : 0 < k) (heven : Even k) (hq : Fintype.card F = 3*k+1)
    (he : ∀ x, f (χ x) = x^k) :
    f (star (jacobiSum χ χ)) = -((2*k).choose k : F) := by
  have hs : star (jacobiSum χ χ) = jacobiSum (χ^2) (χ^2) := by
    rw [← cubic_char_inverse_square hχ, ← cubic_char_star hχ, jacobiSum_ringHomComp]
    rfl
  rw [hs]
  simpa only [jacobiSum, map_sum, map_mul,
    MulChar.pow_apply' χ (by decide : 2 ≠ 0), map_pow, he,
    ← pow_mul, Nat.mul_comm k 2] using conjugate_power_sum hk heven hq

without_editor_info theorem cubicSymbol_conjugate_eq_one (π : Eisenstein) [hπ : Fact (Prime π)]
    (h3 : ¬ π ∣ 3) (hp : (3 : Eisenstein) ∣ π+1) (hne : π ≠ star π) :
    cubicSymbol π h3 (star π) = 1 := by
  let F := Residue π
  let p := ringChar F
  let k := (p-1)/3
  have hcard : Fintype.card F = p := split_residue_card π hp hne
  have hpmod : p%3=1 := hcard ▸ residue_card_mod_three π h3
  obtain ⟨n,hprime,hn⟩ := FiniteField.card F p
  have hpFact : Fact p.Prime := ⟨hprime⟩
  have hpk : p=3*k+1 := by dsimp [k]; have := hprime.two_le; omega
  have hkpos : 0 < k := by have := hprime.two_le; omega
  have heven : Even k := by
    have h := hprime.even_sub_one (by omega)
    rw [even_iff_two_dvd] at h ⊢
    omega
  have he : ∀ x, reduction π (primeCharacter π h3 x) = x^k := by
    intro x
    have h := (primeCharacter_spec π h3).2 x
    change reduction π (primeCharacter π h3 x) = x ^ ((Fintype.card F-1)/3) at h
    rwa [hcard] at h
  have hred : reduction π (star π) = -((2*k).choose k : F) := by
    have h := star_jacobi_reduction (reduction π) (primeCharacter_spec π h3).1
      hkpos heven (hcard.trans hpk) he
    rwa [primeCharacter_jacobi π h3 hp] at h
  obtain ⟨z,hz⟩ := wilson_cubic_binomial hpk
  let g := ZMod.castHom (dvd_refl p) F
  have hcube : reduction π (star π) = (g z)^3 := by
    rw [← map_pow, hz, map_neg, map_natCast, hred]
  have hzn : g z ≠ 0 := by
    intro hzero
    have hdiv : π ∣ star π := (reduction_zero π _).mp (by simp [hcube,hzero])
    exact hne (primary_associated_eq hp (primary_star hp)
      (hπ.out.associated_of_dvd (prime_star hπ.out) hdiv))
  change primeCharacter π h3 (reduction π (star π)) = 1
  rw [hcube, map_pow]
  exact char_cube (primeCharacter_spec π h3).1 hzn

without_editor_info theorem cubicSymbol_reciprocity
    (π ρ : Eisenstein) [hπ : Fact (Prime π)] [hρ : Fact (Prime ρ)]
    (hπ3 : ¬ π ∣ 3) (hρ3 : ¬ ρ ∣ 3)
    (hp : (3 : Eisenstein) ∣ π+1) (hr : (3 : Eisenstein) ∣ ρ+1) :
    cubicSymbol π hπ3 ρ = cubicSymbol ρ hρ3 π := by
  by_cases hc : ringChar (Residue ρ) = ringChar (Residue π)
  · rcases same_characteristic_primary hp hr hc with heq | heq
    · cases heq; rfl
    · have hρπ : π = star ρ := by simp [heq]
      by_cases he : π=ρ
      · cases he; rfl
      have hpn : π ≠ star π := by simpa only [← heq] using he
      have hrn : ρ ≠ star ρ := by simpa only [← hρπ] using Ne.symm he
      calc cubicSymbol π hπ3 ρ = cubicSymbol π hπ3 (star π) := congrArg _ heq
        _ = 1 := cubicSymbol_conjugate_eq_one π hπ3 hp hpn
        _ = cubicSymbol ρ hρ3 (star ρ) := (cubicSymbol_conjugate_eq_one ρ hρ3 hr hrn).symm
        _ = cubicSymbol ρ hρ3 π := congrArg _ hρπ.symm
  · exact cubicSymbol_reciprocity_distinct_characteristic π ρ hπ3 hρ3 hp hr hc

end CubicSpecial


namespace CubicSpecial
open scoped QuadraticAlgebra

abbrev lambda : Eisenstein := 1-ω

without_editor_info theorem lambda_dvd_iff (z : Eisenstein) : lambda ∣ z ↔ (3 : ℤ) ∣ z.re+z.im := by
  constructor
  · rintro ⟨w,rfl⟩
    refine ⟨w.im, ?_⟩
    simp [lambda, QuadraticAlgebra.omega]
    ring
  · rintro ⟨k,hk⟩
    refine ⟨⟨z.re-k,k⟩, ?_⟩
    ext <;> simp [lambda, QuadraticAlgebra.omega] <;> omega

without_editor_info def modLambda : Eisenstein →+* ZMod 3 where
  toFun z := z.re+z.im
  map_zero' := by simp
  map_one' := by simp
  map_add' a b := by simp; ring
  map_mul' a b := by
    simp
    have h3 : (3 : ZMod 3)=0 := by decide
    linear_combination -(b.im : ZMod 3)*(a.im : ZMod 3)*h3

without_editor_info theorem modLambda_zero (z : Eisenstein) : modLambda z=0 ↔ lambda ∣ z := by
  rw [lambda_dvd_iff]
  simpa [modLambda] using ZMod.intCast_zmod_eq_zero_iff_dvd (z.re+z.im) 3

without_editor_info theorem lambda_prime : Prime lambda := by
  refine ⟨by decide, ?_, ?_⟩
  · intro hu
    have h := hu.map modLambda
    have hz : modLambda lambda=0 := (modLambda_zero _).mpr dvd_rfl
    rw [hz] at h
    exact not_isUnit_zero h
  · intro a b hab
    have h := (modLambda_zero _).mpr hab
    rw [map_mul, mul_eq_zero] at h
    exact h.imp (modLambda_zero a).mp (modLambda_zero b).mp

without_editor_info theorem three_eq_lambda_sq : (3 : Eisenstein) = -(ω^2)*lambda^2 := by decide

without_editor_info theorem lambda_dvd_three : lambda ∣ (3 : Eisenstein) := by
  rw [three_eq_lambda_sq]
  exact dvd_mul_of_dvd_right (dvd_pow_self _ (by decide : 2≠0)) _

without_editor_info theorem prime_dvd_three_iff {π : Eisenstein} (hp : Prime π) :
    π ∣ (3 : Eisenstein) ↔ Associated π lambda := by
  constructor
  · intro h
    rw [three_eq_lambda_sq] at h
    rcases hp.dvd_or_dvd h with hu | hLam
    · have hu' : IsUnit (-(ω^2)) := (omega_primitive.isUnit (by decide)).pow 2 |>.neg
      exact False.elim (hp.not_unit (isUnit_of_dvd_unit hu hu'))
    · exact hp.associated_of_dvd lambda_prime (hp.dvd_of_dvd_pow hLam)
  · intro h
    exact h.dvd.trans lambda_dvd_three

abbrev ModE (n : ℕ) := QuadraticAlgebra (ZMod n) (-1) (-1)

without_editor_info def coeffMod (n : ℕ) : Eisenstein →+* ModE n where
  toFun z := ⟨z.re,z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp

without_editor_info theorem coeffMod_zero (n : ℕ) (z : Eisenstein) :
    coeffMod n z=0 ↔ (n : Eisenstein) ∣ z := by
  change coeffMod n z=0 ↔ algebraMap ℤ Eisenstein (n:ℤ) ∣ z
  rw [QuadraticAlgebra.algebraMap_dvd_iff]
  simp only [QuadraticAlgebra.ext_iff, coeffMod, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

without_editor_info theorem coeffMod_omega (n : ℕ) : coeffMod n ω = (QuadraticAlgebra.omega : ModE n) := by
  ext <;> simp [coeffMod, QuadraticAlgebra.omega]

without_editor_info theorem primary_normalization_table : ∀ a b : ZMod 3, a+b≠0 →
    ∃ e : Fin 3, ∃ s : Fin 2,
      (-1 : ModE 3)^(s:ℕ) * QuadraticAlgebra.omega^(e:ℕ) * ⟨a,b⟩ + 1 = 0 := by
  decide +kernel

without_editor_info theorem exists_primary_associate {a : Eisenstein} (ha : ¬lambda ∣ a) :
    ∃ b : Eisenstein, Associated a b ∧ (3 : Eisenstein) ∣ b+1 := by
  have hmod : (a.re : ZMod 3)+(a.im : ZMod 3) ≠ 0 := by
    exact mt (modLambda_zero a).mp ha
  obtain ⟨e,s,hs⟩ := primary_normalization_table (a.re:ZMod 3) (a.im:ZMod 3) hmod
  let u : Eisenstein := (-1)^(s:ℕ)*ω^(e:ℕ)
  have hu : IsUnit u := (isUnit_neg_one.pow _).mul ((omega_primitive.isUnit (by decide)).pow _)
  refine ⟨u*a, associated_unit_mul_right a u hu, ?_⟩
  apply (coeffMod_zero 3 _).mp
  change coeffMod 3 ((-1)^(s:ℕ)*ω^(e:ℕ)*a+1)=0
  rw [map_add, map_mul, map_mul, map_pow, map_pow, map_neg, map_one, coeffMod_omega]
  exact hs

without_editor_info theorem primary_not_lambda_dvd {a : Eisenstein} (ha : (3 : Eisenstein) ∣ a+1) :
    ¬lambda ∣ a := by
  intro h
  have h' := lambda_dvd_three.trans ha
  have hd : lambda ∣ (1 : Eisenstein) := by simpa using dvd_sub h' h
  exact lambda_prime.not_unit (isUnit_of_dvd_one hd)

without_editor_info theorem primary_prime_away_three {π : Eisenstein} (hp : Prime π)
    (ha : (3 : Eisenstein) ∣ π+1) : ¬π ∣ (3 : Eisenstein) := by
  intro h
  exact primary_not_lambda_dvd ha ((prime_dvd_three_iff hp).mp h).symm.dvd

without_editor_info theorem unit_eq_signed_omega {a : Eisenstein} (ha : IsUnit a) :
    ∃ e : Fin 3, ∃ s : Fin 2, a=(-1)^(s:ℕ)*ω^(e:ℕ) := by
  obtain ⟨u,rfl⟩ := ha
  have hn := norm_unit u
  have hn' := hn
  simp only [QuadraticAlgebra.norm_def] at hn'
  have har : -1 ≤ (u:Eisenstein).re ∧ (u:Eisenstein).re ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (2*(u:Eisenstein).im-(u:Eisenstein).re)]
  have hai : -1 ≤ (u:Eisenstein).im ∧ (u:Eisenstein).im ≤ 1 := by
    constructor <;> nlinarith [sq_nonneg (2*(u:Eisenstein).re-(u:Eisenstein).im)]
  obtain ⟨har0,har1⟩ := har
  obtain ⟨hai0,hai1⟩ := hai
  interval_cases hr : (u:Eisenstein).re <;> interval_cases hi : (u:Eisenstein).im <;>
    (try simp only [hr,hi] at hn') <;> norm_num at hn' <;>
    first
    | (refine ⟨0,0,?_⟩; ext <;> simp [hr,hi]; done)
    | (refine ⟨0,1,?_⟩; ext <;> simp [hr,hi]; done)
    | (refine ⟨1,0,?_⟩; ext <;> simp [hr,hi,QuadraticAlgebra.omega]; done)
    | (refine ⟨1,1,?_⟩; ext <;> simp [hr,hi,QuadraticAlgebra.omega]; done)
    | (refine ⟨2,0,?_⟩; ext <;> simp [hr,hi,QuadraticAlgebra.omega,pow_two]; done)
    | (refine ⟨2,1,?_⟩; ext <;> simp [hr,hi,QuadraticAlgebra.omega,pow_two]; done)

end CubicSpecial


namespace CubicSpecial

without_editor_info theorem not_lambda_dvd_unit {a : Eisenstein} (ha : IsUnit a) : ¬lambda ∣ a :=
  fun h => lambda_prime.not_unit (isUnit_of_dvd_unit h ha)

without_editor_info theorem nonzero_of_not_lambda_dvd {a : Eisenstein} (ha : ¬lambda ∣ a) : a≠0 := by
  intro h; exact ha (h ▸ dvd_zero _)

without_editor_info theorem induction_away_lambda {P : Eisenstein → Prop}
    (hu : ∀ a, IsUnit a → P a)
    (hp : ∀ a, Prime a → (3 : Eisenstein) ∣ a+1 → P a)
    (hm : ∀ a b, ¬lambda ∣ a → ¬lambda ∣ b → P a → P b → P (a*b))
    (a : Eisenstein) (ha : ¬lambda ∣ a) : P a := by
  apply UniqueFactorizationMonoid.induction_on_prime (P := fun z => ¬lambda ∣ z → P z)
    a ?_ ?_ ?_ ha
  · exact fun h => False.elim (h (dvd_zero _))
  · intro u hu' _; exact hu u hu'
  · intro b p hb hprime ih hnot
    have hnP : ¬lambda ∣ p := fun h => hnot (dvd_mul_of_dvd_left h b)
    have hnB : ¬lambda ∣ b := fun h => hnot (dvd_mul_of_dvd_right h p)
    obtain ⟨q,hpq,hq⟩ := exists_primary_associate hnP
    have hqprime : Prime q := hpq.prime hprime
    obtain ⟨u,huq⟩ := hpq.symm
    have hPp : P p := by
      rw [← huq]
      exact hm q u (primary_not_lambda_dvd hq) (not_lambda_dvd_unit u.isUnit)
        (hp q hqprime hq) (hu u u.isUnit)
    exact hm p b hnP hnB hPp (ih hnB)

/- Algebraic properties to be checked for the explicit sum of local symbols.
No reciprocity or product formula is assumed in this structure. -/
structure CubicPairing where
  val : Eisenstein → Eisenstein → ZMod 3
  mul_left : ∀ a b c, a≠0 → b≠0 → c≠0 → val (a*b) c=val a c+val b c
  skew : ∀ a b, val a b = -val b a
  steinberg : ∀ a, a≠0 → 1-a≠0 → val a (1-a)=0

namespace CubicPairing
variable (B : CubicPairing)

without_editor_info theorem mul_right (a b c : Eisenstein) (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    B.val a (b*c) = B.val a b+B.val a c := by
  rw [B.skew a (b*c), B.mul_left b c a hb hc ha,
    B.skew b a, B.skew c a]
  ring

without_editor_info theorem one_left {a : Eisenstein} (ha : a≠0) : B.val 1 a=0 := by
  have h := B.mul_left 1 1 a one_ne_zero one_ne_zero ha
  simp only [one_mul] at h
  linear_combination -h

without_editor_info theorem diagonal (a : Eisenstein) : B.val a a=0 := by
  have h : ∀ z : ZMod 3, z = -z → z=0 := by decide +kernel
  exact h _ (B.skew a a)

without_editor_info theorem neg_one_left {a : Eisenstein} (ha : a≠0) : B.val (-1) a=0 := by
  have h := B.mul_left (-1) (-1) a (by decide) (by decide) ha
  rw [neg_one_mul, neg_neg, B.one_left ha] at h
  exact (by decide +kernel : ∀ z : ZMod 3, 0=z+z → z=0) _ h

without_editor_info theorem pow_left {a b : Eisenstein} (ha : a≠0) (hb : b≠0) (n : ℕ) :
    B.val (a^n) b = (n : ZMod 3)*B.val a b := by
  induction n with
  | zero => simp [B.one_left hb]
  | succ n ih =>
      rw [pow_succ, B.mul_left _ _ _ (pow_ne_zero n ha) ha hb, ih]
      push_cast; ring

without_editor_info theorem pow_right {a b : Eisenstein} (ha : a≠0) (hb : b≠0) (n : ℕ) :
    B.val a (b^n) = (n : ZMod 3)*B.val a b := by
  rw [B.skew, B.pow_left hb ha, B.skew b a]
  ring

variable (hw : ∀ a, a≠0 → B.val ω a=0)
include hw

without_editor_info theorem unit_left {u a : Eisenstein} (hu : IsUnit u) (ha : a≠0) : B.val u a=0 := by
  obtain ⟨e,s,rfl⟩ := unit_eq_signed_omega hu
  rw [B.mul_left _ _ _ (pow_ne_zero _ (by decide))
    (pow_ne_zero _ (omega_primitive.ne_zero (by decide))) ha,
    B.pow_left (by decide) ha, B.pow_left (omega_primitive.ne_zero (by decide)) ha,
    B.neg_one_left ha, hw a ha, mul_zero, mul_zero, add_zero]

without_editor_info theorem unit_right {a u : Eisenstein} (ha : a≠0) (hu : IsUnit u) : B.val a u=0 := by
  rw [B.skew, B.unit_left hw hu ha, neg_zero]

without_editor_info theorem associated_left {a b c : Eisenstein} (hab : Associated a b)
    (ha : a≠0) (hc : c≠0) : B.val a c=B.val b c := by
  obtain ⟨u,rfl⟩ := hab
  rw [B.mul_left _ _ _ ha u.ne_zero hc, B.unit_left hw u.isUnit hc, add_zero]

variable (hp : ∀ π ρ, Prime π → Prime ρ → (3 : Eisenstein) ∣ π+1 →
  (3 : Eisenstein) ∣ ρ+1 → B.val π ρ=0)
include hp

without_editor_info theorem away_lambda {a b : Eisenstein} (ha : ¬lambda ∣ a) (hb : ¬lambda ∣ b) :
    B.val a b=0 := by
  apply induction_away_lambda (P := fun a => ∀ b, ¬lambda ∣ b → B.val a b=0)
    (fun u hu b hb => B.unit_left hw hu (nonzero_of_not_lambda_dvd hb)) ?_ ?_ a ha b hb
  · intro π hπ hπprimary b hb
    apply induction_away_lambda (P := fun b => B.val π b=0)
      (fun u hu => B.unit_right hw hπ.ne_zero hu)
      (fun ρ hρ hρprimary => hp π ρ hπ hρ hπprimary hρprimary) ?_ b hb
    intro c d hc hd hBc hBd
    rw [B.mul_right _ _ _ hπ.ne_zero (nonzero_of_not_lambda_dvd hc)
      (nonzero_of_not_lambda_dvd hd), hBc,hBd,add_zero]
  · intro c d hc hd hBc hBd b hb
    rw [B.mul_left _ _ _ (nonzero_of_not_lambda_dvd hc) (nonzero_of_not_lambda_dvd hd)
      (nonzero_of_not_lambda_dvd hb), hBc b hb,hBd b hb,add_zero]

end CubicPairing

without_editor_info theorem not_lambda_cube_dvd_three : ¬lambda^3 ∣ (3 : Eisenstein) := by
  rintro ⟨t,ht⟩
  have h := congrArg QuadraticAlgebra.norm ht
  rw [map_mul, map_pow, show QuadraticAlgebra.norm lambda=3 by decide,
    show QuadraticAlgebra.norm (3 : Eisenstein)=9 by decide] at h
  omega

without_editor_info theorem lambda_sq_dvd_of_three_dvd {a : Eisenstein} (ha : (3 : Eisenstein) ∣ a) :
    lambda^2 ∣ a := by
  apply dvd_trans _ ha
  rw [three_eq_lambda_sq]
  exact dvd_mul_left _ _

without_editor_info theorem lambda_shift_four {a : Eisenstein} (ha : ¬lambda ∣ a)
    (h3 : lambda^3 ∣ 1-a) : ¬lambda^3 ∣ 1-4*a := by
  intro h4
  have hd : lambda^3 ∣ (1-4*a)-4*(1-a) := dvd_sub h4 (dvd_mul_of_dvd_right h3 4)
  have he : (1-4*a)-4*(1-a) = (-3 : Eisenstein) := by ring
  rw [he, dvd_neg] at hd
  exact not_lambda_cube_dvd_three hd

end CubicSpecial


namespace CubicSpecial

without_editor_info theorem induction_lambda_primary {P : Eisenstein → Prop}
    (hu : ∀ a, IsUnit a → P a) (hl : P lambda)
    (hp : ∀ a, Prime a → (3 : Eisenstein) ∣ a+1 → P a)
    (hm : ∀ a b, a≠0 → b≠0 → P a → P b → P (a*b))
    (a : Eisenstein) (ha : a≠0) : P a := by
  apply UniqueFactorizationMonoid.induction_on_prime (P := fun z => z≠0 → P z)
    a ?_ ?_ ?_ ha
  · exact fun h => False.elim (h rfl)
  · intro u hu' _; exact hu u hu'
  · intro b p hb hprime ih hnot
    have hPp : P p := by
      by_cases hld : lambda ∣ p
      · obtain ⟨u,huq⟩ := lambda_prime.associated_of_dvd hprime hld
        rw [← huq]
        exact hm lambda u lambda_prime.ne_zero u.ne_zero hl (hu u u.isUnit)
      · obtain ⟨q,hpq,hq⟩ := exists_primary_associate hld
        have hqprime := hpq.prime hprime
        obtain ⟨u,huq⟩ := hpq.symm
        rw [← huq]
        exact hm q u hqprime.ne_zero u.ne_zero (hp q hqprime hq) (hu u u.isUnit)
    exact hm p b hprime.ne_zero hb hPp (ih hb)

namespace CubicPairing
variable (B : CubicPairing)
variable (hw : ∀ a, a≠0 → B.val ω a=0)
variable (hp : ∀ π ρ, Prime π → Prime ρ → (3 : Eisenstein) ∣ π+1 →
  (3 : Eisenstein) ∣ ρ+1 → B.val π ρ=0)
include hw hp

without_editor_info theorem lambda_right_exact_two {a : Eisenstein} (ha : ¬lambda ∣ a)
    (h2 : lambda^2 ∣ 1-a) (h3 : ¬lambda^3 ∣ 1-a) : B.val a lambda=0 := by
  obtain ⟨c,hc⟩ := h2
  have hcn : ¬lambda ∣ c := by
    rintro ⟨d,hd⟩
    apply h3
    refine ⟨d, ?_⟩
    rw [hc,hd]
    ring
  have hne : 1-a≠0 := fun h => h3 (h ▸ dvd_zero _)
  have h := B.steinberg a (nonzero_of_not_lambda_dvd ha) hne
  rw [hc, B.mul_right _ _ _ (nonzero_of_not_lambda_dvd ha)
    (pow_ne_zero 2 lambda_prime.ne_zero) (nonzero_of_not_lambda_dvd hcn),
    B.pow_right (nonzero_of_not_lambda_dvd ha) lambda_prime.ne_zero,
    B.away_lambda hw hp ha hcn, add_zero] at h
  exact (by decide +kernel : ∀ z : ZMod 3, 2*z=0 → z=0) _ h

without_editor_info theorem lambda_right_near_one {a : Eisenstein} (ha : ¬lambda ∣ a)
    (hprimary : (3 : Eisenstein) ∣ a-1) : B.val a lambda=0 := by
  have h2 : lambda^2 ∣ 1-a := by
    have h := lambda_sq_dvd_of_three_dvd hprimary
    simpa only [neg_sub] using dvd_neg.mpr h
  by_cases h3 : lambda^3 ∣ 1-a
  · have hfour : B.val (4 : Eisenstein) lambda=0 := by
      apply B.lambda_right_exact_two hw hp
      · rw [lambda_dvd_iff]; decide
      · apply lambda_sq_dvd_of_three_dvd; exact ⟨-1,by decide⟩
      · rw [show (1 : Eisenstein)-4 = -3 by decide, dvd_neg]
        exact not_lambda_cube_dvd_three
    have hprod : B.val (4*a) lambda=0 := by
      apply B.lambda_right_exact_two hw hp
      · intro h
        rcases lambda_prime.dvd_or_dvd h with h | h
        · have hn : ¬lambda ∣ (4 : Eisenstein) := by rw [lambda_dvd_iff]; decide
          exact hn h
        · exact ha h
      · apply lambda_sq_dvd_of_three_dvd
        have h := dvd_mul_of_dvd_right hprimary (4 : Eisenstein)
        have hs := dvd_add h (dvd_refl (3 : Eisenstein))
        have he : 4*(a-1)+3=4*a-1 := by ring
        rw [he] at hs
        simpa only [neg_sub] using dvd_neg.mpr hs
      · exact lambda_shift_four ha h3
    rw [B.mul_left _ _ _ (by decide) (nonzero_of_not_lambda_dvd ha)
      lambda_prime.ne_zero, hfour, zero_add] at hprod
    exact hprod
  · exact B.lambda_right_exact_two hw hp ha h2 h3

without_editor_info theorem lambda_right_primary {a : Eisenstein} (ha : (3 : Eisenstein) ∣ a+1) :
    B.val a lambda=0 := by
  have hna : ¬lambda ∣ a := primary_not_lambda_dvd ha
  have hnneg : ¬lambda ∣ -a := by simpa only [dvd_neg] using hna
  have hne : (3 : Eisenstein) ∣ -a-1 := by
    simpa only [neg_add_rev, add_comm, sub_eq_add_neg] using dvd_neg.mpr ha
  have h := B.lambda_right_near_one hw hp hnneg hne
  have hmul := B.mul_left (-1) a lambda (by decide)
    (nonzero_of_not_lambda_dvd hna) lambda_prime.ne_zero
  rw [neg_one_mul, B.neg_one_left lambda_prime.ne_zero, zero_add] at hmul
  exact hmul.symm.trans h

without_editor_info theorem lambda_right {a : Eisenstein} (ha : a≠0) : B.val a lambda=0 := by
  apply induction_lambda_primary (P := fun a => B.val a lambda=0)
    (fun u hu => B.unit_left hw hu lambda_prime.ne_zero)
    (B.diagonal lambda) (fun π _ hπ => B.lambda_right_primary hw hp hπ) ?_ a ha
  intro c d hc hd hBc hBd
  rw [B.mul_left _ _ _ hc hd lambda_prime.ne_zero,hBc,hBd,add_zero]

/- A reduction of the global product formula to ordinary primary-prime
reciprocity and the root-of-unity supplement. The Steinberg relation removes
the need for a separately assumed ramified-prime supplement. -/
without_editor_info theorem zero_of_primary_reciprocity {a b : Eisenstein} (ha : a≠0) (hb : b≠0) :
    B.val a b=0 := by
  apply induction_lambda_primary (P := fun a => ∀ b, b≠0 → B.val a b=0)
    (fun u hu b hb => B.unit_left hw hu hb) ?_ ?_ ?_ a ha b hb
  · intro b hb
    rw [B.skew, B.lambda_right hw hp hb, neg_zero]
  · intro π hπ hprimary b hb
    apply induction_lambda_primary (P := fun b => B.val π b=0)
      (fun u hu => B.unit_right hw hπ.ne_zero hu)
      (B.lambda_right hw hp hπ.ne_zero)
      (fun ρ hρ hρprimary => hp π ρ hπ hρ hprimary hρprimary) ?_ b hb
    intro c d hc hd hBc hBd
    rw [B.mul_right _ _ _ hπ.ne_zero hc hd,hBc,hBd,add_zero]
  · intro c d hc hd hBc hBd b hb
    rw [B.mul_left _ _ _ hc hd hb,hBc b hb,hBd b hb,add_zero]

end CubicPairing
end CubicSpecial


namespace CubicSpecial

without_editor_info noncomputable def primeUnit (π : Eisenstein) [hp : Fact (Prime π)] (a : Eisenstein) :
    Eisenstein := if ha : a=0 then 0 else
      (FiniteMultiplicity.of_prime_left hp.out ha).exists_eq_pow_mul_and_not_dvd.choose

without_editor_info theorem primeUnit_spec (π : Eisenstein) [hp : Fact (Prime π)] {a : Eisenstein} (ha : a≠0) :
    a = π^multiplicity π a * primeUnit π a ∧ ¬π ∣ primeUnit π a := by
  simpa only [primeUnit, dif_neg ha] using
    (FiniteMultiplicity.of_prime_left hp.out ha).exists_eq_pow_mul_and_not_dvd.choose_spec

without_editor_info theorem primeUnit_nonzero (π : Eisenstein) [Fact (Prime π)] {a : Eisenstein} (ha : a≠0) :
    primeUnit π a≠0 := by
  intro h
  have h' := (primeUnit_spec π ha).1
  rw [h,mul_zero] at h'
  exact ha h'

without_editor_info theorem primeUnit_of_not_dvd (π : Eisenstein) [Fact (Prime π)] {a : Eisenstein}
    (ha : ¬π ∣ a) : primeUnit π a=a := by
  have hne : a≠0 := fun h => ha (h ▸ dvd_zero _)
  have h := (primeUnit_spec π hne).1
  rw [multiplicity_eq_zero_of_not_dvd ha, pow_zero,one_mul] at h
  exact h.symm

without_editor_info theorem primeUnit_mul (π : Eisenstein) [hp : Fact (Prime π)] {a b : Eisenstein}
    (ha : a≠0) (hb : b≠0) : primeUnit π (a*b)=primeUnit π a * primeUnit π b := by
  have hv := multiplicity_mul hp.out (FiniteMultiplicity.of_prime_left hp.out (mul_ne_zero ha hb))
  apply mul_left_cancel₀ (pow_ne_zero (multiplicity π (a*b)) hp.out.ne_zero)
  calc π^multiplicity π (a*b) * primeUnit π (a*b) = a*b := (primeUnit_spec π (mul_ne_zero ha hb)).1.symm
    _ = (π^multiplicity π a * primeUnit π a)*(π^multiplicity π b*primeUnit π b) :=
      congrArg₂ (·*·) (primeUnit_spec π ha).1 (primeUnit_spec π hb).1
    _ = π^multiplicity π (a*b)*(primeUnit π a*primeUnit π b) := by rw [hv,pow_add]; ring

without_editor_info def logOmega (a : Eisenstein) : ZMod 3 := if a=1 then 0 else if a=ω then 1 else 2

without_editor_info theorem logOmega_mul {a b : Eisenstein} (ha : a^3=1) (hb : b^3=1) :
    logOmega (a*b)=logOmega a+logOmega b := by
  obtain ⟨i,hi,rfl⟩ := omega_primitive.eq_pow_of_pow_eq_one ha
  obtain ⟨j,hj,rfl⟩ := omega_primitive.eq_pow_of_pow_eq_one hb
  interval_cases i <;> interval_cases j <;> decide +kernel

without_editor_info theorem logOmega_one : logOmega 1=0 := by decide

without_editor_info noncomputable def cubicLog (π : Eisenstein) [Fact (Prime π)] (h3 : ¬π ∣ 3) (a : Eisenstein) : ZMod 3 :=
  logOmega (cubicSymbol π h3 a)

without_editor_info theorem cubicLog_mul (π : Eisenstein) [Fact (Prime π)] (h3 : ¬π ∣ 3)
    {a b : Eisenstein} (ha : ¬π ∣ a) (hb : ¬π ∣ b) :
    cubicLog π h3 (a*b) = cubicLog π h3 a+cubicLog π h3 b := by
  exact (congrArg logOmega (cubicSymbol_mul π h3 a b)).trans
    (logOmega_mul (cubicSymbol_cube π h3 ha) (cubicSymbol_cube π h3 hb))

without_editor_info theorem cubicLog_one (π : Eisenstein) [Fact (Prime π)] (h3 : ¬π ∣ 3) :
    cubicLog π h3 1=0 := by
  simp only [cubicLog,cubicSymbol,map_one,logOmega_one]

without_editor_info theorem cubicLog_congr (π : Eisenstein) [Fact (Prime π)] (h3 : ¬π ∣ 3)
    {a b : Eisenstein} (h : reduction π a = reduction π b) :
    cubicLog π h3 a = cubicLog π h3 b := by
  simp only [cubicLog,cubicSymbol,h]

without_editor_info noncomputable def tame (π : Eisenstein) [Fact (Prime π)] (h3 : ¬π ∣ 3)
    (a b : Eisenstein) : ZMod 3 :=
  multiplicity π a * cubicLog π h3 (primeUnit π b) -
    multiplicity π b * cubicLog π h3 (primeUnit π a)

without_editor_info theorem tame_skew (π : Eisenstein) [Fact (Prime π)] (h3 : ¬π ∣ 3) (a b : Eisenstein) :
    tame π h3 a b = -tame π h3 b a := by unfold tame; ring

without_editor_info theorem tame_mul_left (π : Eisenstein) [hp : Fact (Prime π)] (h3 : ¬π ∣ 3)
    {a b c : Eisenstein} (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    tame π h3 (a*b) c=tame π h3 a c+tame π h3 b c := by
  unfold tame
  rw [multiplicity_mul hp.out (FiniteMultiplicity.of_prime_left hp.out (mul_ne_zero ha hb)),
    primeUnit_mul π ha hb,
    cubicLog_mul π h3 (primeUnit_spec π ha).2 (primeUnit_spec π hb).2]
  push_cast
  ring

without_editor_info theorem tame_of_not_dvd (π : Eisenstein) [Fact (Prime π)] (h3 : ¬π ∣ 3)
    {a b : Eisenstein} (ha : ¬π ∣ a) (hb : ¬π ∣ b) : tame π h3 a b=0 := by
  simp only [tame,multiplicity_eq_zero_of_not_dvd ha,multiplicity_eq_zero_of_not_dvd hb,
    Nat.cast_zero,zero_mul,sub_zero]

without_editor_info theorem tame_steinberg (π : Eisenstein) [hp : Fact (Prime π)] (h3 : ¬π ∣ 3)
    (a : Eisenstein) : tame π h3 a (1-a)=0 := by
  have hnotboth : ¬(π ∣ a ∧ π ∣ 1-a) := by
    rintro ⟨ha,hb⟩
    have h := dvd_add ha hb
    have hd : π ∣ (1 : Eisenstein) := by convert h using 1 <;> ring
    exact hp.out.not_unit (isUnit_of_dvd_one hd)
  by_cases ha : π ∣ a
  · have hb : ¬π ∣ 1-a := fun h => hnotboth ⟨ha,h⟩
    have hlog : cubicLog π h3 (1-a)=0 := by
      rw [cubicLog_congr π h3 (b := 1) (by
        rw [map_sub, (reduction_zero π a).mpr ha,sub_zero]), cubicLog_one]
    simp only [tame,multiplicity_eq_zero_of_not_dvd hb,primeUnit_of_not_dvd π hb,
      hlog,mul_zero,Nat.cast_zero,zero_mul,sub_zero]
  · by_cases hb : π ∣ 1-a
    · have hlog : cubicLog π h3 a=0 := by
        apply (cubicLog_congr π h3 (b := 1) ?_).trans (cubicLog_one π h3)
        have h := (reduction_zero π (1-a)).mpr hb
        rw [map_sub,sub_eq_zero] at h
        exact h.symm
      simp only [tame,multiplicity_eq_zero_of_not_dvd ha,primeUnit_of_not_dvd π ha,
        hlog,mul_zero,Nat.cast_zero,zero_mul,sub_zero]
    · exact tame_of_not_dvd π h3 ha hb

end CubicSpecial


namespace CubicSpecial

without_editor_info noncomputable instance eisenstein_units_finite : Finite Eisensteinˣ := by
  let w : Eisensteinˣ := (omega_primitive.isUnit (by decide)).unit
  have hw : (w:Eisenstein)=ω := (omega_primitive.isUnit (by decide)).unit_spec
  let f : Fin 3 × Fin 2 → Eisensteinˣ := fun e => (-1)^(e.2:ℕ)*w^(e.1:ℕ)
  apply Finite.of_surjective f
  intro u
  obtain ⟨e,s,hs⟩ := unit_eq_signed_omega u.isUnit
  refine ⟨(e,s), Units.ext ?_⟩
  simpa only [f,Units.val_mul,Units.val_pow_eq_pow_val,Units.val_neg,Units.val_one,hw] using hs.symm

without_editor_info noncomputable instance eisenstein_units_fintype : Fintype Eisensteinˣ := Fintype.ofFinite _

without_editor_info def PrimaryPrime := {π : Eisenstein // Prime π ∧ (3 : Eisenstein) ∣ π+1}

without_editor_info instance primaryPrime_fact (π : PrimaryPrime) : Fact (Prime π.val) := ⟨π.property.1⟩

without_editor_info theorem primaryPrime_ne_three (π : PrimaryPrime) : ¬π.val ∣ (3 : Eisenstein) :=
  primary_prime_away_three π.property.1 π.property.2

without_editor_info noncomputable def tameAt (π : PrimaryPrime) (a b : Eisenstein) : ZMod 3 :=
  tame π.val (primaryPrime_ne_three π) a b

without_editor_info theorem finite_primary_divisors {a : Eisenstein} (ha : a≠0) :
    {π : PrimaryPrime | π.val ∣ a}.Finite := by
  have hdiv : Fintype {d : Eisenstein // d ∣ a} := UniqueFactorizationMonoid.fintypeSubtypeDvd a ha
  let f : {π : PrimaryPrime // π.val ∣ a} → {d : Eisenstein // d ∣ a} :=
    fun π => ⟨π.val.val,π.property⟩
  have hf : Function.Injective f := by
    intro π ρ h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : {d : Eisenstein // d ∣ a} => t.val) h
  have hfin : Finite {π : PrimaryPrime // π.val ∣ a} := Finite.of_injective f hf
  exact Set.finite_coe_iff.mp hfin

without_editor_info theorem tameAt_finite_support {a b : Eisenstein} (ha : a≠0) (hb : b≠0) :
    Function.HasFiniteSupport (fun π : PrimaryPrime => tameAt π a b) := by
  apply ((finite_primary_divisors ha).union (finite_primary_divisors hb)).subset
  intro π hπ
  by_contra h
  have hs : ¬π.val ∣ a ∧ ¬π.val ∣ b := by simpa using h
  exact hπ (tame_of_not_dvd π.val (primaryPrime_ne_three π) hs.1 hs.2)

without_editor_info noncomputable def tameTotal (a b : Eisenstein) : ZMod 3 := ∑ᶠ π : PrimaryPrime, tameAt π a b

without_editor_info theorem tameTotal_skew (a b : Eisenstein) : tameTotal a b = -tameTotal b a := by
  unfold tameTotal
  simp_rw [tameAt, tame_skew _ _ a b]
  rw [finsum_neg_distrib]

without_editor_info theorem tameTotal_mul_left {a b c : Eisenstein} (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    tameTotal (a*b) c=tameTotal a c+tameTotal b c := by
  unfold tameTotal
  have he (π : PrimaryPrime) : tameAt π (a*b) c=tameAt π a c+tameAt π b c :=
    tame_mul_left π.val (primaryPrime_ne_three π) ha hb hc
  simp_rw [he]
  exact finsum_add_distrib (tameAt_finite_support ha hc) (tameAt_finite_support hb hc)

without_editor_info theorem tameTotal_steinberg (a : Eisenstein) : tameTotal a (1-a)=0 := by
  unfold tameTotal
  have he (π : PrimaryPrime) : tameAt π a (1-a)=0 :=
    tame_steinberg π.val (primaryPrime_ne_three π) a
  simp_rw [he]
  exact finsum_zero

without_editor_info noncomputable def tamePairing : CubicPairing where
  val := tameTotal
  mul_left := fun _ _ _ => tameTotal_mul_left
  skew := tameTotal_skew
  steinberg := fun a _ _ => tameTotal_steinberg a

end CubicSpecial


namespace CubicSpecial

without_editor_info def unitLookup : ZMod 9 → ZMod 9 → Fin 3 → ZMod 3 :=
![  ![![0,0,0],![1,0,0],![1,1,0],![0,0,0],![1,2,0],![1,2,0],![0,0,0],![1,1,0],![1,0,0]],
  ![![0,0,0],![2,0,0],![0,0,0],![0,0,1],![2,2,1],![0,0,0],![0,0,2],![2,1,2],![0,0,0]],
  ![![0,1,0],![0,0,0],![2,1,0],![0,1,2],![0,0,0],![2,2,2],![0,1,1],![0,0,0],![2,0,1]],
  ![![0,0,0],![1,1,2],![1,0,1],![0,0,0],![1,0,2],![1,1,1],![0,0,0],![1,2,2],![1,2,1]],
  ![![0,2,0],![2,0,2],![0,0,0],![0,2,1],![2,2,0],![0,0,0],![0,2,2],![2,1,1],![0,0,0]],
  ![![0,2,0],![0,0,0],![2,1,1],![0,2,2],![0,0,0],![2,2,0],![0,2,1],![0,0,0],![2,0,2]],
  ![![0,0,0],![1,2,1],![1,2,2],![0,0,0],![1,1,1],![1,0,2],![0,0,0],![1,0,1],![1,1,2]],
  ![![0,1,0],![2,0,1],![0,0,0],![0,1,1],![2,2,2],![0,0,0],![0,1,2],![2,1,0],![0,0,0]],
  ![![0,0,0],![0,0,0],![2,1,2],![0,0,2],![0,0,0],![2,2,1],![0,0,1],![0,0,0],![2,0,0]]]

without_editor_info def unitLog9 (a : ModE 9) : Fin 3 → ZMod 3 := unitLookup a.re a.im

without_editor_info def Unit9 (a : ModE 9) : Prop := (a.re.val+a.im.val)%3≠0

without_editor_info instance (a : ModE 9) : Decidable (Unit9 a) := inferInstanceAs (Decidable (_%3≠0))

without_editor_info def wildForm (a b : Fin 4 → ZMod 3) : ZMod 3 :=
  2*a 0*b 2+a 1*b 2+2*a 1*b 3+a 2*b 0+2*a 2*b 1+a 3*b 1

without_editor_info def wildVec (v : ℕ) (u : ModE 9) : Fin 4 → ZMod 3 :=
  ![(v:ZMod 3),unitLog9 u 0,unitLog9 u 1,unitLog9 u 2]

without_editor_info theorem unitLog9_mul_table : ∀ a b c d : ZMod 9,
    Unit9 ⟨a,b⟩ → Unit9 ⟨c,d⟩ →
    Unit9 ((⟨a,b⟩ : ModE 9)*⟨c,d⟩) ∧
    ∀ i, unitLog9 ((⟨a,b⟩ : ModE 9)*⟨c,d⟩) i =
      unitLog9 ⟨a,b⟩ i+unitLog9 ⟨c,d⟩ i := by
  decide +kernel

without_editor_info theorem wild_units_steinberg_table : ∀ a b : ZMod 9,
    Unit9 ⟨a,b⟩ → Unit9 (1-(⟨a,b⟩ : ModE 9)) →
    wildForm (wildVec 0 ⟨a,b⟩) (wildVec 0 (1-(⟨a,b⟩ : ModE 9)))=0 := by
  decide +kernel

without_editor_info theorem wild_ramified_steinberg_table : ∀ e : Fin 4, e≠0 → ∀ a b : ZMod 9,
    Unit9 ⟨a,b⟩ →
    let z : ModE 9 := 1-(1-QuadraticAlgebra.omega)^(e:ℕ)*⟨a,b⟩
    Unit9 z ∧ wildForm (wildVec e ⟨a,b⟩) (wildVec 0 z)=0 := by
  decide +kernel

without_editor_info theorem unitLog9_primary_table : ∀ a b : ZMod 9,
    a.val%3=2 → b.val%3=0 → unitLog9 ⟨a,b⟩ 0=0 := by
  decide +kernel

without_editor_info theorem unitLog9_norm_table : ∀ a b : ZMod 9, Unit9 ⟨a,b⟩ →
    unitLog9 ⟨a,b⟩ 1+2*unitLog9 ⟨a,b⟩ 2 =
      ((((QuadraticAlgebra.norm (⟨a,b⟩ : ModE 9)).val-1)/3 : ℕ) : ZMod 3) := by
  decide +kernel

without_editor_info theorem unitLog9_one : unitLog9 1=0 := by decide +kernel
without_editor_info theorem unitLog9_omega : unitLog9 (QuadraticAlgebra.omega : ModE 9)=![1,0,0] := by decide +kernel
without_editor_info theorem unitLog9_neg_one : unitLog9 (-1)=0 := by decide +kernel

end CubicSpecial


namespace CubicSpecial

without_editor_info instance lambda_fact : Fact (Prime lambda) := ⟨lambda_prime⟩

without_editor_info theorem unit9_mod3_table : ∀ a b : ZMod 9, Unit9 ⟨a,b⟩ ↔
    ZMod.castHom (by decide : 3∣9) (ZMod 3) a +
      ZMod.castHom (by decide : 3∣9) (ZMod 3) b ≠ 0 := by
  decide +kernel

without_editor_info theorem Unit9_coeffMod (a : Eisenstein) : Unit9 (coeffMod 9 a) ↔ ¬lambda ∣ a := by
  have h : Unit9 (coeffMod 9 a) ↔ modLambda a≠0 := by
    change Unit9 ⟨(a.re:ZMod 9),(a.im:ZMod 9)⟩ ↔ _
    rw [unit9_mod3_table, map_intCast, map_intCast]
    rfl
  exact h.trans (not_congr (modLambda_zero a))

without_editor_info theorem unitLog9_mul {a b : ModE 9} (ha : Unit9 a) (hb : Unit9 b) :
    unitLog9 (a*b) = unitLog9 a+unitLog9 b := by
  exact funext ((unitLog9_mul_table a.re a.im b.re b.im ha hb).2)

without_editor_info theorem wildForm_add_left (a b c : Fin 4 → ZMod 3) :
    wildForm (a+b) c=wildForm a c+wildForm b c := by
  simp only [wildForm,Pi.add_apply]
  ring

without_editor_info theorem wildForm_skew (a b : Fin 4 → ZMod 3) : wildForm a b = -wildForm b a := by
  unfold wildForm
  simp only [show (2 : ZMod 3) = -1 by decide]
  ring

without_editor_info noncomputable def wildClass (a : Eisenstein) : Fin 4 → ZMod 3 :=
  wildVec (multiplicity lambda a) (coeffMod 9 (primeUnit lambda a))

without_editor_info theorem wildClass_mul {a b : Eisenstein} (ha : a≠0) (hb : b≠0) :
    wildClass (a*b)=wildClass a+wildClass b := by
  have hul := unitLog9_mul
    ((Unit9_coeffMod _).mpr (primeUnit_spec lambda ha).2)
    ((Unit9_coeffMod _).mpr (primeUnit_spec lambda hb).2)
  unfold wildClass
  rw [multiplicity_mul lambda_prime (FiniteMultiplicity.of_prime_left lambda_prime (mul_ne_zero ha hb)),
    primeUnit_mul lambda ha hb, map_mul]
  ext i
  fin_cases i <;> simp [wildVec,hul,Nat.cast_add]

without_editor_info theorem wildClass_of_not_dvd {a : Eisenstein} (ha : ¬lambda ∣ a) :
    wildClass a=wildVec 0 (coeffMod 9 a) := by
  simp only [wildClass,multiplicity_eq_zero_of_not_dvd ha,primeUnit_of_not_dvd lambda ha]

without_editor_info noncomputable def wild (a b : Eisenstein) : ZMod 3 := wildForm (wildClass a) (wildClass b)

without_editor_info theorem wild_skew (a b : Eisenstein) : wild a b = -wild b a := wildForm_skew _ _

without_editor_info theorem wild_mul_left {a b c : Eisenstein} (ha : a≠0) (hb : b≠0) :
    wild (a*b) c=wild a c+wild b c := by
  unfold wild
  rw [wildClass_mul ha hb,wildForm_add_left]

without_editor_info theorem lambda_four_mod9 : coeffMod 9 lambda^4=0 := by decide +kernel

without_editor_info theorem wild_steinberg_ramified {a : Eisenstein} (ha : a≠0) (hd : lambda ∣ a) :
    wild a (1-a)=0 := by
  have hb : ¬lambda ∣ 1-a := by
    intro h
    have h' : lambda ∣ (1 : Eisenstein) := by
      convert dvd_add hd h using 1 <;> ring
    exact lambda_prime.not_unit (isUnit_of_dvd_one h')
  let v := multiplicity lambda a
  let u := coeffMod 9 (primeUnit lambda a)
  have hu : Unit9 u := (Unit9_coeffMod _).mpr (primeUnit_spec lambda ha).2
  have hne : v≠0 := (multiplicity_ne_zero (FiniteMultiplicity.of_prime_left lambda_prime ha)).mpr hd
  have hcomp : coeffMod 9 (1-a) = 1-(coeffMod 9 lambda)^v*u := by
    rw [map_sub,map_one]
    conv_lhs => rw [(primeUnit_spec lambda ha).1]
    rw [map_mul,map_pow]
  unfold wild
  rw [wildClass_of_not_dvd hb]
  change wildForm (wildVec v u) (wildVec 0 (coeffMod 9 (1-a)))=0
  rw [hcomp]
  by_cases hv : v<4
  · have h := wild_ramified_steinberg_table (⟨v,hv⟩ : Fin 4)
      (by intro h; exact hne (congrArg Fin.val h)) u.re u.im hu
    exact h.2
  · have hp : (coeffMod 9 lambda)^v=0 := by
      obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (show 4≤v by omega)
      rw [hk,pow_add,lambda_four_mod9,zero_mul]
    rw [hp,zero_mul,sub_zero]
    simp [wildForm,wildVec,unitLog9_one]

without_editor_info theorem wild_steinberg {a : Eisenstein} (ha : a≠0) (hb : 1-a≠0) : wild a (1-a)=0 := by
  by_cases hd : lambda ∣ a
  · exact wild_steinberg_ramified ha hd
  · by_cases he : lambda ∣ 1-a
    · have h := wild_steinberg_ramified hb he
      have heq : (1 : Eisenstein)-(1-a)=a := by ring
      rw [heq] at h
      rw [wild_skew,h,neg_zero]
    · rw [wild,wildClass_of_not_dvd hd,wildClass_of_not_dvd he]
      have h := wild_units_steinberg_table (coeffMod 9 a).re (coeffMod 9 a).im
        ((Unit9_coeffMod a).mpr hd)
        (by simpa only [map_sub,map_one] using (Unit9_coeffMod (1-a)).mpr he)
      simpa only [map_sub,map_one] using h

without_editor_info noncomputable def wildPairing : CubicPairing where
  val := wild
  mul_left := fun _ _ _ ha hb _ => wild_mul_left ha hb
  skew := wild_skew
  steinberg := fun _ => wild_steinberg

without_editor_info noncomputable def globalPairing : CubicPairing where
  val a b := tameTotal a b+wild a b
  mul_left := by
    intro a b c ha hb hc
    rw [tameTotal_mul_left ha hb hc,wild_mul_left ha hb]
    ring
  skew := by
    intro a b
    rw [tameTotal_skew a b,wild_skew a b]
    ring
  steinberg := by
    intro a ha hb
    rw [tameTotal_steinberg a,wild_steinberg ha hb,add_zero]

end CubicSpecial


namespace CubicSpecial

without_editor_info theorem primary_dvd_iff {π ρ : Eisenstein} (hπ : Prime π) (hρ : Prime ρ)
    (hp : (3 : Eisenstein) ∣ π+1) (hr : (3 : Eisenstein) ∣ ρ+1) : π ∣ ρ ↔ π=ρ :=
  ⟨fun h => primary_associated_eq hp hr (hπ.associated_of_dvd hρ h), fun h => h ▸ dvd_rfl⟩

without_editor_info theorem not_prime_dvd_unit {π u : Eisenstein} (hp : Prime π) (hu : IsUnit u) : ¬π ∣ u :=
  fun h => hp.not_unit (isUnit_of_dvd_unit h hu)

without_editor_info theorem tame_self (π : Eisenstein) [Fact (Prime π)] (h3 : ¬π ∣ 3) (a : Eisenstein) :
    tame π h3 a a=0 := by simp only [tame,sub_self]

without_editor_info theorem tame_at_prime (π : Eisenstein) [Fact (Prime π)] (h3 : ¬π ∣ 3)
    {a : Eisenstein} (ha : ¬π ∣ a) : tame π h3 π a=cubicLog π h3 a := by
  simp only [tame,multiplicity_self (FiniteMultiplicity.of_prime_left (Fact.out : Prime π)
    (Fact.out : Prime π).ne_zero),multiplicity_eq_zero_of_not_dvd ha,
    primeUnit_of_not_dvd π ha,Nat.cast_one,Nat.cast_zero,one_mul,zero_mul,sub_zero]

without_editor_info theorem tameTotal_primary (π ρ : Eisenstein) [hπ : Fact (Prime π)] [hρ : Fact (Prime ρ)]
    (hp : (3 : Eisenstein) ∣ π+1) (hr : (3 : Eisenstein) ∣ ρ+1) : tameTotal π ρ=0 := by
  classical
  by_cases heq : π=ρ
  · subst ρ
    simp only [tameTotal,tameAt,tame_self,finsum_zero]
  let p : PrimaryPrime := ⟨π,hπ.out,hp⟩
  let q : PrimaryPrime := ⟨ρ,hρ.out,hr⟩
  have hpq : p≠q := fun h => heq (congrArg Subtype.val h)
  have hs : Function.support (fun r : PrimaryPrime => tameAt r π ρ) ⊆ ({p,q} : Finset PrimaryPrime) := by
    intro r hh
    by_contra hn
    have hne : r≠p ∧ r≠q := by simpa using hn
    have hnπ : ¬r.val ∣ π := by
      rw [primary_dvd_iff r.property.1 hπ.out r.property.2 hp]
      intro h; exact hne.1 (Subtype.ext h)
    have hnρ : ¬r.val ∣ ρ := by
      rw [primary_dvd_iff r.property.1 hρ.out r.property.2 hr]
      intro h; exact hne.2 (Subtype.ext h)
    exact hh (tame_of_not_dvd r.val (primaryPrime_ne_three r) hnπ hnρ)
  have hnπ : ¬π ∣ ρ := by rwa [primary_dvd_iff hπ.out hρ.out hp hr]
  have hnρ : ¬ρ ∣ π := by rwa [primary_dvd_iff hρ.out hπ.out hr hp, eq_comm]
  rw [tameTotal,finsum_eq_sum_of_support_subset _ hs,Finset.sum_pair hpq]
  change tame π (primaryPrime_ne_three p) π ρ+tame ρ (primaryPrime_ne_three q) π ρ=0
  rw [tame_at_prime π _ hnπ,tame_skew ρ _ π ρ,tame_at_prime ρ _ hnρ]
  have he := congrArg logOmega (cubicSymbol_reciprocity π ρ
    (primaryPrime_ne_three p) (primaryPrime_ne_three q) hp hr)
  change cubicLog π _ ρ = cubicLog ρ _ π at he
  rw [he,add_neg_cancel]

without_editor_info theorem tameTotal_unit_primary {u : Eisenstein} (hu : IsUnit u)
    (π : Eisenstein) [hπ : Fact (Prime π)] (hp : (3 : Eisenstein) ∣ π+1) :
    tameTotal u π = -cubicLog π (primary_prime_away_three hπ.out hp) u := by
  let p : PrimaryPrime := ⟨π,hπ.out,hp⟩
  have hz (r : PrimaryPrime) (hr : r≠p) : tameAt r u π=0 := by
    apply tame_of_not_dvd r.val (primaryPrime_ne_three r) (not_prime_dvd_unit r.property.1 hu)
    rw [primary_dvd_iff r.property.1 hπ.out r.property.2 hp]
    exact fun h => hr (Subtype.ext h)
  rw [tameTotal,finsum_eq_single _ p hz]
  change tame π _ u π = _
  rw [tame_skew,tame_at_prime π _ (not_prime_dvd_unit hπ.out hu)]

without_editor_info theorem tameTotal_unit_lambda {u : Eisenstein} (hu : IsUnit u) : tameTotal u lambda=0 := by
  have hz (r : PrimaryPrime) : tameAt r u lambda=0 := by
    apply tame_of_not_dvd r.val (primaryPrime_ne_three r) (not_prime_dvd_unit r.property.1 hu)
    exact fun h => primaryPrime_ne_three r (h.trans lambda_dvd_three)
  simp only [tameTotal,hz,finsum_zero]

without_editor_info theorem cubicSymbol_omega (π : Eisenstein) [Fact (Prime π)] (h3 : ¬π ∣ 3) :
    cubicSymbol π h3 ω = ω^((Fintype.card (Residue π)-1)/3) := by
  apply cubic_value_injective (reduction π) (residue_omega_primitive π h3)
    (char_cubic_value (primeCharacter_spec π h3).1 _) (cubic_value_pow (Or.inr omega_primitive.pow_eq_one) _)
  exact ((primeCharacter_spec π h3).2 _).trans (map_pow (reduction π) ω _).symm

without_editor_info theorem logOmega_pow (n : ℕ) : logOmega (ω^n)=(n : ZMod 3) := by
  have hw : orderOf ω=3 := omega_primitive.eq_orderOf.symm
  rw [← pow_mod_orderOf,hw]
  have hn : (n : ZMod 3)=(n%3 : ℕ) := by simp
  rw [hn]
  have hlt := Nat.mod_lt n (by decide : 0<3)
  interval_cases h : n%3 <;> decide +kernel

without_editor_info theorem cubicLog_omega (π : Eisenstein) [Fact (Prime π)] (h3 : ¬π ∣ 3) :
    cubicLog π h3 ω = (((Fintype.card (Residue π)-1)/3 : ℕ) : ZMod 3) := by
  rw [cubicLog,cubicSymbol_omega,logOmega_pow]

end CubicSpecial


namespace CubicSpecial
open scoped QuadraticAlgebra

without_editor_info theorem coeffMod_norm (n : ℕ) (a : Eisenstein) :
    QuadraticAlgebra.norm (coeffMod n a) = ((QuadraticAlgebra.norm a : ℤ) : ZMod n) := by
  simp [coeffMod,QuadraticAlgebra.norm_def]

without_editor_info theorem primary9_table : ∀ a b : ZMod 9,
    ZMod.castHom (by decide : 3∣9) (ZMod 3) a = -1 →
    ZMod.castHom (by decide : 3∣9) (ZMod 3) b = 0 → unitLog9 ⟨a,b⟩ 0=0 := by
  decide +kernel

without_editor_info theorem unitLog9_primary {a : Eisenstein} (ha : (3 : Eisenstein) ∣ a+1) :
    unitLog9 (coeffMod 9 a) 0=0 := by
  have h := (coeffMod_zero 3 (a+1)).mpr ha
  rw [map_add,map_one] at h
  have hr : (a.re : ZMod 3)+1=0 := by simpa [coeffMod] using congrArg QuadraticAlgebra.re h
  have hi : (a.im : ZMod 3)=0 := by simpa [coeffMod] using congrArg QuadraticAlgebra.im h
  apply primary9_table
  · rw [map_intCast]; exact eq_neg_of_add_eq_zero_left hr
  · rw [map_intCast]; exact hi

without_editor_info theorem wildClass_primary {a : Eisenstein} (ha : (3 : Eisenstein) ∣ a+1) :
    wildClass a 0=0 ∧ wildClass a 1=0 := by
  rw [wildClass_of_not_dvd (primary_not_lambda_dvd ha)]
  simp [wildVec,unitLog9_primary ha]

without_editor_info theorem wild_primary {a b : Eisenstein} (ha : (3 : Eisenstein) ∣ a+1)
    (hb : (3 : Eisenstein) ∣ b+1) : wild a b=0 := by
  obtain ⟨ha0,ha1⟩ := wildClass_primary ha
  obtain ⟨hb0,hb1⟩ := wildClass_primary hb
  simp only [wild,wildForm,ha0,ha1,hb0,hb1,mul_zero,zero_mul,add_zero]

without_editor_info theorem wildClass_omega : wildClass ω=![0,1,0,0] := by
  rw [wildClass_of_not_dvd (not_lambda_dvd_unit (omega_primitive.isUnit (by decide))),
    coeffMod_omega]
  simp [wildVec,unitLog9_omega]

without_editor_info theorem primeUnit_self (π : Eisenstein) [hp : Fact (Prime π)] : primeUnit π π=1 := by
  have h := (primeUnit_spec π hp.out.ne_zero).1
  rw [multiplicity_self (FiniteMultiplicity.of_prime_left hp.out hp.out.ne_zero),pow_one] at h
  apply mul_left_cancel₀ hp.out.ne_zero
  simpa only [mul_one] using h.symm

without_editor_info theorem wildClass_lambda : wildClass lambda=![1,0,0,0] := by
  simp [wildClass,multiplicity_self (FiniteMultiplicity.of_prime_left lambda_prime lambda_prime.ne_zero),primeUnit_self,map_one,wildVec,unitLog9_one]

without_editor_info theorem wild_omega_lambda : wild ω lambda=0 := by
  simp [wild,wildClass_omega,wildClass_lambda,wildForm]

without_editor_info theorem wild_omega_prime (π : Eisenstein) [hπ : Fact (Prime π)]
    (hp : (3 : Eisenstein) ∣ π+1) :
    wild ω π=cubicLog π (primary_prime_away_three hπ.out hp) ω := by
  have h3 := primary_prime_away_three hπ.out hp
  have hu : Unit9 (coeffMod 9 π) := (Unit9_coeffMod π).mpr (primary_not_lambda_dvd hp)
  have hn := unitLog9_norm_table (coeffMod 9 π).re (coeffMod 9 π).im hu
  have hq := residue_card_mod_three π h3
  have hform (u : ModE 9) : wildForm ![0,1,0,0] (wildVec 0 u) =
      unitLog9 u 1+2*unitLog9 u 2 := by simp [wildForm,wildVec]
  rw [wild,wildClass_omega,wildClass_of_not_dvd (primary_not_lambda_dvd hp)]
  rw [hform,hn,cubicLog_omega,coeffMod_norm,residue_norm π,Int.cast_natCast,ZMod.val_natCast]
  apply (ZMod.natCast_eq_natCast_iff' _ _ 3).mpr
  omega

without_editor_info theorem globalPairing_omega (a : Eisenstein) (ha : a≠0) : globalPairing.val ω a=0 := by
  have hwne : ω≠0 := omega_primitive.ne_zero (by decide)
  have hwunit := omega_primitive.isUnit (by decide)
  apply induction_lambda_primary (P := fun a => globalPairing.val ω a=0) ?_ ?_ ?_ ?_ a ha
  · intro u hu
    obtain ⟨e,s,rfl⟩ := unit_eq_signed_omega hu
    rw [globalPairing.mul_right _ _ _ hwne (pow_ne_zero _ (by decide)) (pow_ne_zero _ hwne),
      globalPairing.pow_right hwne (by decide),globalPairing.pow_right hwne hwne,
      globalPairing.skew ω (-1), globalPairing.neg_one_left hwne,neg_zero,
      globalPairing.diagonal ω,mul_zero,mul_zero,add_zero]
  · change tameTotal ω lambda+wild ω lambda=0
    rw [tameTotal_unit_lambda hwunit,wild_omega_lambda,add_zero]
  · intro π hπ hp
    have hFact : Fact (Prime π) := ⟨hπ⟩
    change tameTotal ω π+wild ω π=0
    rw [tameTotal_unit_primary hwunit π hp,wild_omega_prime π hp,neg_add_cancel]
  · intro c d hc hd hBc hBd
    rw [globalPairing.mul_right _ _ _ hwne hc hd,hBc,hBd,add_zero]

/- The explicit global cubic product formula on nonzero Eisenstein integers.
The ramified term is the concrete 4-by-4 matrix used by the certificates;
the other terms use canonical finite-field characters and prime exponents. -/
without_editor_info theorem cubic_global_product {a b : Eisenstein} (ha : a≠0) (hb : b≠0) :
    tameTotal a b+wild a b=0 := by
  apply globalPairing.zero_of_primary_reciprocity globalPairing_omega ?_ ha hb
  intro π ρ hπ hρ hp hr
  have hπFact : Fact (Prime π) := ⟨hπ⟩
  have hρFact : Fact (Prime ρ) := ⟨hρ⟩
  change tameTotal π ρ+wild π ρ=0
  rw [tameTotal_primary π ρ hp hr,wild_primary hp hr,add_zero]

end CubicSpecial

namespace CubicSpecial

structure GraphEdge (n : ℕ) where
  src : Fin n
  dst : Fin n
  weight : ZMod 3

without_editor_info def graphSum {n m : ℕ} (edges : Fin m → GraphEdge n)
    (H C : Fin n → Eisenstein) (B : Eisenstein → Eisenstein → ZMod 3) : ZMod 3 :=
  (∑ e, (edges e).weight * B (H (edges e).src) (H (edges e).dst)) +
    ∑ i, B (H i) (C i)

without_editor_info theorem graphSum_add {n m : ℕ} (edges : Fin m → GraphEdge n)
    (H C : Fin n → Eisenstein) (B D : Eisenstein → Eisenstein → ZMod 3) :
    graphSum edges H C (fun a b => B a b+D a b)=
      graphSum edges H C B+graphSum edges H C D := by
  simp only [graphSum,mul_add,Finset.sum_add_distrib]
  ring

without_editor_info theorem finsum_const_mul {ι : Type*} (f : ι → ZMod 3)
    (hf : Function.HasFiniteSupport f) (w : ZMod 3) :
    (∑ᶠ i, w*f i)=w*(∑ᶠ i, f i) := by
  classical
  have hs : Function.support (fun i => w*f i) ⊆ hf.toFinset := by
    intro i hi
    apply hf.mem_toFinset.mpr
    intro h
    exact hi (by change w*f i=0; rw [h,mul_zero])
  rw [finsum_eq_sum_of_support_subset _ hs,finsum_eq_sum f hf,Finset.mul_sum]

without_editor_info theorem graph_tame_total {n m : ℕ} (edges : Fin m → GraphEdge n)
    (H C : Fin n → Eisenstein) (hH : ∀ i, H i≠0) (hC : ∀ i, C i≠0) :
    (∑ᶠ π : PrimaryPrime, graphSum edges H C (tameAt π)) =
      graphSum edges H C tameTotal := by
  have he (e : Fin m) : Function.HasFiniteSupport (fun π : PrimaryPrime =>
      (edges e).weight*tameAt π (H (edges e).src) (H (edges e).dst)) :=
    (tameAt_finite_support (hH _) (hH _)).fun_comp (mul_zero _)
  have hc (i : Fin n) := tameAt_finite_support (hH i) (hC i)
  rw [show (fun π => graphSum edges H C (tameAt π)) =
    (fun π => (∑ e, (edges e).weight*tameAt π (H (edges e).src) (H (edges e).dst)) +
      ∑ i, tameAt π (H i) (C i)) from rfl]
  rw [finsum_add_distrib (Function.HasFiniteSupport.sum he Finset.univ)
    (Function.HasFiniteSupport.sum hc Finset.univ),
    finsum_sum_comm _ _ (fun e _ => he e),finsum_sum_comm _ _ (fun i _ => hc i)]
  simp_rw [finsum_const_mul _ (tameAt_finite_support (hH _) (hH _))]
  rfl

without_editor_info theorem graph_global_product {n m : ℕ} (edges : Fin m → GraphEdge n)
    (H C : Fin n → Eisenstein) (hH : ∀ i, H i≠0) (hC : ∀ i, C i≠0) :
    (∑ᶠ π : PrimaryPrime, graphSum edges H C (tameAt π))+graphSum edges H C wild=0 := by
  rw [graph_tame_total edges H C hH hC,←graphSum_add]
  simp only [graphSum,cubic_global_product (hH _) (hH _),
    cubic_global_product (hH _) (hC _),mul_zero,Finset.sum_const_zero,add_zero]

without_editor_info theorem graph_finite_prime_reduction {n m : ℕ} (edges : Fin m → GraphEdge n)
    (H C : Fin n → Eisenstein) (hH : ∀ i, H i≠0) (hC : ∀ i, C i≠0)
    (S : Finset PrimaryPrime)
    (hout : ∀ π, π∉S → graphSum edges H C (tameAt π)=0) :
    (∑ π ∈ S, graphSum edges H C (tameAt π))+graphSum edges H C wild=0 := by
  have hs : Function.support (fun π => graphSum edges H C (tameAt π)) ⊆ S := by
    intro π hπ
    by_contra h
    exact hπ (hout π h)
  have h := graph_global_product edges H C hH hC
  rwa [finsum_eq_sum_of_support_subset _ hs] at h

without_editor_info def incidenceRow {n m : ℕ} (edges : Fin m → GraphEdge n) (logs : Fin n → ZMod 3)
    (i : Fin n) : ZMod 3 :=
  ∑ e, ((if (edges e).src=i then (edges e).weight*logs (edges e).dst else 0) -
    (if (edges e).dst=i then (edges e).weight*logs (edges e).src else 0))

without_editor_info theorem incidence_sum {n m : ℕ} (edges : Fin m → GraphEdge n)
    (v logs : Fin n → ZMod 3) :
    (∑ i, v i*incidenceRow edges logs i) =
      ∑ e, (edges e).weight*(v (edges e).src*logs (edges e).dst-v (edges e).dst*logs (edges e).src) := by
  classical
  simp only [incidenceRow,Finset.mul_sum,mul_sub]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  simp [Finset.sum_sub_distrib,mul_ite] <;> ring

without_editor_info theorem graph_tame_cancellation {n m : ℕ} (edges : Fin m → GraphEdge n)
    (H C : Fin n → Eisenstein) (π : Eisenstein) [Fact (Prime π)] (h3 : ¬π ∣ 3)
    (hC : ∀ i, ¬π ∣ C i)
    (hrow : ∀ i, π ∣ H i →
      cubicLog π h3 (C i)+incidenceRow edges (fun j => cubicLog π h3 (primeUnit π (H j))) i=0) :
    graphSum edges H C (tame π h3)=0 := by
  let v : Fin n → ZMod 3 := fun i => multiplicity π (H i)
  let l : Fin n → ZMod 3 := fun i => cubicLog π h3 (primeUnit π (H i))
  have hr (i : Fin n) : v i*(cubicLog π h3 (C i)+incidenceRow edges l i)=0 := by
    by_cases hi : π ∣ H i
    · rw [hrow i hi,mul_zero]
    · simp only [v,multiplicity_eq_zero_of_not_dvd hi,Nat.cast_zero,zero_mul]
  have hid := incidence_sum edges v l
  have ht : graphSum edges H C (tame π h3) =
      ∑ i, v i*(cubicLog π h3 (C i)+incidenceRow edges l i) := by
    simp only [graphSum,tame,multiplicity_eq_zero_of_not_dvd (hC _),
      primeUnit_of_not_dvd π (hC _),Nat.cast_zero,zero_mul,sub_zero]
    change (∑ e, (edges e).weight*(v (edges e).src*l (edges e).dst-v (edges e).dst*l (edges e).src)) +
      (∑ i, v i*cubicLog π h3 (C i)) = _
    rw [←hid]
    simp only [mul_add,Finset.sum_add_distrib]
    ring
  rw [ht]
  exact Finset.sum_eq_zero (fun i _ => hr i)

end CubicSpecial


namespace CubicSpecial

without_editor_info theorem primeUnit_factorization (π : Eisenstein) [hp : Fact (Prime π)]
    (e : ℕ) {a u : Eisenstein} (he : a=π^e*u) (hu : ¬π ∣ u) :
    multiplicity π a=e ∧ primeUnit π a=u := by
  have hun : u≠0 := fun h => hu (h ▸ dvd_zero _)
  have han : a≠0 := by rw [he]; exact mul_ne_zero (pow_ne_zero e hp.out.ne_zero) hun
  have hv : multiplicity π a=e := by
    rw [he,multiplicity_mul hp.out (FiniteMultiplicity.of_prime_left hp.out
      (mul_ne_zero (pow_ne_zero e hp.out.ne_zero) hun)),
      multiplicity_pow_self_of_prime hp.out,multiplicity_eq_zero_of_not_dvd hu,add_zero]
  refine ⟨hv,?_⟩
  apply mul_left_cancel₀ (pow_ne_zero e hp.out.ne_zero)
  have h := (primeUnit_spec π han).1
  rw [hv] at h
  exact h.symm.trans he

without_editor_info theorem primeUnit_congruence (π : Eisenstein) [hp : Fact (Prime π)]
    {a b : Eisenstein} (hb : b≠0) {r : ℕ} (hr : 0<r)
    (hd : π^(multiplicity π b+r) ∣ a-b) :
    multiplicity π a=multiplicity π b ∧ π^r ∣ primeUnit π a-primeUnit π b := by
  obtain ⟨t,ht⟩ := hd
  let u := primeUnit π b
  have hu : ¬π ∣ u := (primeUnit_spec π hb).2
  have he : a=π^multiplicity π b*(u+π^r*t) := by
    have h := (primeUnit_spec π hb).1
    rw [pow_add] at ht
    dsimp only [u]
    linear_combination ht+h
  have hdt : π ∣ π^r*t := dvd_mul_of_dvd_left (dvd_pow_self π hr.ne') t
  have hun : ¬π ∣ u+π^r*t := by
    intro h
    have h' := dvd_sub h hdt
    exact hu (by simpa only [add_sub_cancel_right] using h')
  obtain ⟨hval,hunit⟩ := primeUnit_factorization π (multiplicity π b) he hun
  refine ⟨hval,t,?_⟩
  rw [hunit]
  change u+π^r*t-u=π^r*t
  ring

without_editor_info theorem tame_congr_left (π : Eisenstein) [Fact (Prime π)] (h3 : ¬π ∣ 3)
    {a b : Eisenstein} (hb : b≠0)
    (hd : π^(multiplicity π b+1) ∣ a-b) (c : Eisenstein) :
    tame π h3 a c=tame π h3 b c := by
  obtain ⟨hv,hu⟩ := primeUnit_congruence π hb (by decide : 0<1) hd
  rw [pow_one] at hu
  have he : reduction π (primeUnit π a)=reduction π (primeUnit π b) := by
    have h := (reduction_zero π _).mpr hu
    rwa [map_sub,sub_eq_zero] at h
  simp only [tame,hv,cubicLog_congr π h3 he]

without_editor_info theorem nine_dvd_lambda_four : (9 : Eisenstein) ∣ lambda^4 := by
  exact ⟨ω^2,by decide⟩

without_editor_info theorem wildClass_congr {a b : Eisenstein} (hb : b≠0)
    (hd : lambda^(multiplicity lambda b+4) ∣ a-b) : wildClass a=wildClass b := by
  obtain ⟨hv,hu⟩ := primeUnit_congruence lambda hb (by decide : 0<4) hd
  have hc : coeffMod 9 (primeUnit lambda a)=coeffMod 9 (primeUnit lambda b) := by
    have h := (coeffMod_zero 9 _).mpr (nine_dvd_lambda_four.trans hu)
    rwa [map_sub,sub_eq_zero] at h
  simp only [wildClass,hv,hc]

without_editor_info theorem lambda_pow_dvd_three_pow (k : ℕ) : lambda^(2*k) ∣ (3 : Eisenstein)^k := by
  have h : lambda^2 ∣ (3 : Eisenstein) := by
    rw [three_eq_lambda_sq]
    exact dvd_mul_left _ _
  simpa only [pow_mul] using pow_dvd_pow_of_dvd h k

without_editor_info theorem wildClass_stable_mod_three_pow {a b : Eisenstein} (hb : b≠0)
    (k : ℕ) (hbound : multiplicity lambda b+4 ≤ 2*k)
    (hd : (3 : Eisenstein)^k ∣ a-b) : wildClass a=wildClass b := by
  apply wildClass_congr hb
  exact (pow_dvd_pow lambda hbound).trans ((lambda_pow_dvd_three_pow k).trans hd)

end CubicSpecial


namespace CubicSpecial

without_editor_info theorem cubicLog_pow (π : Eisenstein) [hp : Fact (Prime π)] (h3 : ¬π ∣ 3)
    {a : Eisenstein} (ha : ¬π ∣ a) (k : ℕ) :
    cubicLog π h3 (a^k)=(k : ZMod 3)*cubicLog π h3 a := by
  induction k with
  | zero => simp only [pow_zero,cubicLog_one,Nat.cast_zero,zero_mul]
  | succ k ih =>
    rw [pow_succ,cubicLog_mul π h3 (fun h => ha (hp.out.dvd_of_dvd_pow h)) ha,ih]
    push_cast
    ring

without_editor_info theorem cubicLog_prod {ι : Type*} (π : Eisenstein) [hp : Fact (Prime π)] (h3 : ¬π ∣ 3)
    (s : Finset ι) (f : ι → Eisenstein) (hf : ∀ i ∈ s, ¬π ∣ f i) :
    cubicLog π h3 (∏ i ∈ s, f i)=∑ i ∈ s, cubicLog π h3 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Finset.sum_empty,cubicLog_one]
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, ¬π ∣ f j := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hn : ¬π ∣ ∏ j ∈ s, f j := by
      intro h
      obtain ⟨j,hj,hd⟩ := (hp.out.dvd_finsetProd_iff f).mp h
      exact hs j hj hd
    rw [Finset.prod_insert hi,Finset.sum_insert hi,
      cubicLog_mul π h3 (hf i (Finset.mem_insert_self i s)) hn,ih hs]

without_editor_info theorem cubicLog_residue_cube (π : Eisenstein) [Fact (Prime π)] (h3 : ¬π ∣ 3)
    {a : Eisenstein} (ha : ¬π ∣ a)
    (hc : ∃ z : Residue π, reduction π a=z^3) : cubicLog π h3 a=0 := by
  obtain ⟨z,hz⟩ := hc
  have hzn : z≠0 := by
    intro h
    exact ha ((reduction_zero π a).mp (by simpa only [h,zero_pow (by decide : (3 : ℕ)≠0)] using hz))
  have hs : cubicSymbol π h3 a=1 := by
    change primeCharacter π h3 (reduction π a)=1
    rw [hz]
    simpa only [map_pow] using char_cube (primeCharacter_spec π h3).1 hzn
  exact (congrArg logOmega hs).trans logOmega_one

without_editor_info theorem residue_cube_of_cleared_identity (π : Eisenstein) [Fact (Prime π)]
    {a d w f r : Eisenstein} (hd : ¬π ∣ d) (hf : π ∣ f)
    (he : d^3*a=w^3+f*r) : ∃ z : Residue π, reduction π a=z^3 := by
  have hd0 : reduction π d≠0 := fun h => hd ((reduction_zero π d).mp h)
  have h := congrArg (reduction π) he
  simp only [map_mul,map_add,map_pow,(reduction_zero π f).mpr hf,zero_mul,add_zero] at h
  refine ⟨reduction π w / reduction π d,?_⟩
  rw [div_pow]
  apply (eq_div_iff (pow_ne_zero 3 hd0)).mpr
  simpa only [mul_comm] using h

without_editor_info theorem residue_not_dvd_of_bezout (π : Eisenstein) [Fact (Prime π)]
    {f g a b d : Eisenstein} (hf : π ∣ f) (hd : ¬π ∣ d)
    (he : a*f+b*g=d) : ¬π ∣ g := by
  intro hg
  apply hd
  rw [←he]
  exact dvd_add (dvd_mul_of_dvd_right hf a) (dvd_mul_of_dvd_right hg b)

without_editor_info theorem graph_tame_vanish_of_cube_products {n m : ℕ} (edges : Fin m → GraphEdge n)
    (H C : Fin n → Eisenstein) (π : Eisenstein) [hp : Fact (Prime π)] (h3 : ¬π ∣ 3)
    (hC : ∀ i, ¬π ∣ C i) (rho : Fin n → Fin n → ℕ)
    (hrow : ∀ l i, incidenceRow edges l i=∑ j, (rho i j : ZMod 3)*l j)
    (hsep : ∀ i j, π ∣ H i → rho i j≠0 → ¬π ∣ H j)
    (hcube : ∀ i, π ∣ H i → ∃ z : Residue π,
      reduction π (C i*∏ j, H j^rho i j)=z^3) :
    graphSum edges H C (tame π h3)=0 := by
  apply graph_tame_cancellation edges H C π h3 hC
  intro i hi
  have hn (j : Fin n) : ¬π ∣ H j^rho i j := by
    by_cases hr : rho i j=0
    · rw [hr,pow_zero]
      exact hp.out.not_dvd_one
    · exact fun h => hsep i j hi hr (hp.out.dvd_of_dvd_pow h)
  have hnp : ¬π ∣ ∏ j, H j^rho i j := by
    intro h
    obtain ⟨j,_,hj⟩ := (hp.out.dvd_finsetProd_iff (fun j => H j^rho i j)).mp h
    exact hn j hj
  have hc : ¬π ∣ C i*∏ j, H j^rho i j := by
    intro h
    exact (hp.out.dvd_mul.mp h).elim (hC i) hnp
  have hl := cubicLog_residue_cube π h3 hc (hcube i hi)
  rw [cubicLog_mul π h3 (hC i) hnp,
    cubicLog_prod π h3 Finset.univ _ (fun j _ => hn j)] at hl
  rw [hrow]
  convert hl using 2
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hr : rho i j=0
  · simp only [hr,pow_zero,cubicLog_one,Nat.cast_zero,zero_mul]
  · rw [primeUnit_of_not_dvd π (hsep i j hi hr),
      cubicLog_pow π h3 (hsep i j hi hr)]

end CubicSpecial


namespace CubicSpecial

section BilinearGraph
variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]

without_editor_info def vectorGraph {n m : ℕ} (edges : Fin m → GraphEdge n)
    (H C : Fin n → V) (B : V →ₗ[ZMod 3] V →ₗ[ZMod 3] ZMod 3) : ZMod 3 :=
  (∑ e, (edges e).weight*B (H (edges e).src) (H (edges e).dst)) +
    ∑ i, B (H i) (C i)

without_editor_info def graphStar {n m : ℕ} (edges : Fin m → GraphEdge n) (H C : Fin n → V)
    (i : Fin n) : V := C i + ∑ e,
  ((if (edges e).src=i then (edges e).weight • H (edges e).dst else 0) -
   (if (edges e).dst=i then (edges e).weight • H (edges e).src else 0))

without_editor_info theorem graphStar_pairing {n m : ℕ} (edges : Fin m → GraphEdge n)
    (H C d : Fin n → V) (B : V →ₗ[ZMod 3] V →ₗ[ZMod 3] ZMod 3)
    (hsk : ∀ a b, B a b = -B b a) :
    (∑ i, B (d i) (graphStar edges H C i)) =
      (∑ e, (edges e).weight*(B (d (edges e).src) (H (edges e).dst) +
        B (H (edges e).src) (d (edges e).dst))) + ∑ i, B (d i) (C i) := by
  classical
  simp only [graphStar,map_add,map_sum,map_sub,map_smul,smul_eq_mul,Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  have he (e : Fin m) :
      (∑ i, (B (d i) ((if (edges e).src=i then (edges e).weight • H (edges e).dst else 0)) -
          B (d i) ((if (edges e).dst=i then (edges e).weight • H (edges e).src else 0)))) =
      (edges e).weight*(B (d (edges e).src) (H (edges e).dst)+B (H (edges e).src) (d (edges e).dst)) := by
    rw [Finset.sum_sub_distrib]
    simp only [apply_ite,map_zero,map_smul,smul_eq_mul]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
    rw [hsk (d (edges e).dst) (H (edges e).src)]
    ring
  simp_rw [he]
  ring

without_editor_info theorem vectorGraph_add {n m : ℕ} (edges : Fin m → GraphEdge n)
    (H C d : Fin n → V) (B : V →ₗ[ZMod 3] V →ₗ[ZMod 3] ZMod 3)
    (hsk : ∀ a b, B a b = -B b a) :
    vectorGraph edges (fun i => H i+d i) C B = vectorGraph edges H C B +
      (∑ i, B (d i) (graphStar edges H C i)) +
      ∑ e, (edges e).weight*B (d (edges e).src) (d (edges e).dst) := by
  rw [graphStar_pairing edges H C d B hsk]
  simp only [vectorGraph,map_add,LinearMap.add_apply,mul_add,Finset.sum_add_distrib]
  ring

without_editor_info theorem vectorGraph_affine_constant {n m r : ℕ} (edges : Fin m → GraphEdge n)
    (H C : Fin n → V) (D : Fin n → Fin r → V)
    (B : V →ₗ[ZMod 3] V →ₗ[ZMod 3] ZMod 3) (hsk : ∀ a b, B a b = -B b a)
    (hlinear : ∀ i k, B (D i k) (graphStar edges H C i)=0)
    (hcross : ∀ e k l, B (D (edges e).src k) (D (edges e).dst l)=0)
    (a : Fin n → Fin r → ZMod 3) :
    vectorGraph edges (fun i => H i+∑ k, a i k • D i k) C B = vectorGraph edges H C B := by
  rw [vectorGraph_add edges H C _ B hsk]
  have hl (i : Fin n) : B (∑ k, a i k • D i k) (graphStar edges H C i)=0 := by
    simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,
      hlinear,smul_zero,Finset.sum_const_zero]
  have hc (e : Fin m) : B (∑ k, a (edges e).src k • D (edges e).src k)
      (∑ l, a (edges e).dst l • D (edges e).dst l)=0 := by
    simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,
      hcross,smul_zero,Finset.sum_const_zero]
  simp only [hl,hc,mul_zero,Finset.sum_const_zero,add_zero]

end BilinearGraph
end CubicSpecial


namespace CubicSpecial

without_editor_info def digitE (i j : Fin 9) : Eisenstein := ⟨i.val,j.val⟩

without_editor_info theorem exists_digitE (a : Eisenstein) : ∃ i j : Fin 9, (9 : Eisenstein) ∣ a-digitE i j := by
  let i : Fin 9 := ⟨(a.re : ZMod 9).val,ZMod.val_lt _⟩
  let j : Fin 9 := ⟨(a.im : ZMod 9).val,ZMod.val_lt _⟩
  refine ⟨i,j,(coeffMod_zero 9 _).mp ?_⟩
  ext <;> simp [coeffMod,digitE,i,j]

without_editor_info theorem lambda_low_order_congr {a b : Eisenstein} (hb : b≠0) (k : ℕ)
    (hv : multiplicity lambda b < 2*k) (hd : (3 : Eisenstein)^k ∣ a-b) :
    a≠0 ∧ multiplicity lambda a=multiplicity lambda b := by
  have hdp : lambda^(2*k) ∣ a-b := (lambda_pow_dvd_three_pow k).trans hd
  have ha : a≠0 := by
    intro h
    have hn := (FiniteMultiplicity.of_prime_left lambda_prime hb).not_pow_dvd_of_multiplicity_lt hv
    exact hn (by simpa only [h,zero_sub,dvd_neg] using hdp)
  refine ⟨ha,?_⟩
  apply (primeUnit_congruence lambda hb (r := 2*k-multiplicity lambda b) (by omega) ?_).1
  rwa [Nat.add_sub_of_le hv.le]

without_editor_info theorem wildClass_finite_lifts {a b : Eisenstein} (hb : b≠0) (k : ℕ)
    (hv : multiplicity lambda b < 2*k) (hd : (3 : Eisenstein)^k ∣ a-b) :
    ∃ i j : Fin 9, wildClass a=wildClass (b+(3 : Eisenstein)^k*digitE i j) := by
  obtain ⟨t,ht⟩ := hd
  obtain ⟨i,j,q,hq⟩ := exists_digitE t
  let b' := b+(3 : Eisenstein)^k*digitE i j
  have hdb : (3 : Eisenstein)^k ∣ b'-b := ⟨digitE i j,by dsimp [b']; ring⟩
  obtain ⟨hb',hv'⟩ := lambda_low_order_congr hb k hv hdb
  refine ⟨i,j,?_⟩
  apply wildClass_stable_mod_three_pow hb' (k+2) (by rw [hv']; omega)
  refine ⟨q,?_⟩
  dsimp only [b']
  rw [pow_add]
  linear_combination ht+(3 : Eisenstein)^k*hq

end CubicSpecial


namespace CubicSpecial

without_editor_info theorem wildClass_one : wildClass 1=0 := by
  rw [wildClass_of_not_dvd (not_lambda_dvd_unit isUnit_one),map_one]
  simp [wildVec,unitLog9_one]

without_editor_info theorem wildClass_neg_one : wildClass (-1)=0 := by
  rw [wildClass_of_not_dvd (not_lambda_dvd_unit (isUnit_one.neg)),map_neg,map_one]
  simp [wildVec,unitLog9_neg_one]

without_editor_info theorem wildClass_pow {a : Eisenstein} (ha : a≠0) (k : ℕ) :
    wildClass (a^k)=(k : ZMod 3) • wildClass a := by
  induction k with
  | zero => simp only [pow_zero,wildClass_one,Nat.cast_zero,zero_smul]
  | succ k ih =>
    rw [pow_succ,wildClass_mul (pow_ne_zero k ha) ha,ih]
    simp only [Nat.cast_add,Nat.cast_one,add_smul,one_smul]

without_editor_info theorem wildClass_three : wildClass 3=![2,2,0,0] := by
  rw [three_eq_lambda_sq,show -ω^2=(-1 : Eisenstein)*ω^2 by ring,
    wildClass_mul (mul_ne_zero (by decide) (pow_ne_zero _ (omega_primitive.ne_zero (by decide))))
      (pow_ne_zero _ lambda_prime.ne_zero),
    wildClass_mul (by decide) (pow_ne_zero _ (omega_primitive.ne_zero (by decide))),
    wildClass_pow (omega_primitive.ne_zero (by decide)),wildClass_pow lambda_prime.ne_zero,
    wildClass_neg_one,wildClass_omega,wildClass_lambda]
  decide +kernel

without_editor_info theorem unitLog9_real_table : ∀ t : ZMod 9, Unit9 ⟨t,0⟩ →
    unitLog9 ⟨t,0⟩=![0,unitLog9 ⟨t,0⟩ 1,0] := by decide +kernel

without_editor_info theorem wildClass_integer_unit (t : ℤ) (ht : ¬(3 : ℤ) ∣ t) :
    ∃ c : ZMod 3, wildClass (t : Eisenstein)=c • ![0,0,1,0] := by
  have hd : ¬lambda ∣ (t : Eisenstein) := by
    rw [lambda_dvd_iff]
    simpa using ht
  have hu := (Unit9_coeffMod (t : Eisenstein)).mpr hd
  have he : coeffMod 9 (t : Eisenstein)=⟨(t : ZMod 9),0⟩ := by ext <;> simp [coeffMod]
  rw [he] at hu
  refine ⟨unitLog9 ⟨(t : ZMod 9),0⟩ 1,?_⟩
  rw [wildClass_of_not_dvd hd,he]
  have hl := unitLog9_real_table (t : ZMod 9) hu
  have h0 : unitLog9 ⟨(t : ZMod 9),0⟩ 0=0 := by simpa using congrFun hl 0
  have h2 : unitLog9 ⟨(t : ZMod 9),0⟩ 2=0 := by simpa using congrFun hl 2
  ext i
  fin_cases i <;> simp [wildVec,h0,h2]

without_editor_info theorem wildClass_integer (a : ℤ) (ha : a≠0) :
    ∃ e c : ZMod 3, wildClass (a : Eisenstein)=
      e • ![2,2,0,0]+c • ![0,0,1,0] := by
  obtain ⟨t,he,ht⟩ := (FiniteMultiplicity.of_prime_left Int.prime_three ha).exists_eq_pow_mul_and_not_dvd
  have htn : t≠0 := fun h => ht (h ▸ dvd_zero _)
  obtain ⟨c,hc⟩ := wildClass_integer_unit t ht
  refine ⟨(multiplicity (3 : ℤ) a : ZMod 3),c,?_⟩
  have he' : (a : Eisenstein)=(3 : Eisenstein)^multiplicity (3 : ℤ) a*(t : Eisenstein) := by
    exact_mod_cast he
  rw [he',wildClass_mul (pow_ne_zero _ (by norm_num)) (by exact_mod_cast htn),
    wildClass_pow (by norm_num : (3 : Eisenstein)≠0),wildClass_three,hc]

end CubicSpecial

namespace CubicSpecial

without_editor_info def normNat (a : Eisenstein) : ℕ := (QuadraticAlgebra.norm a).natAbs

without_editor_info theorem normNat_mul (a b : Eisenstein) : normNat (a*b)=normNat a*normNat b := by
  simp [normNat,map_mul,Int.natAbs_mul]

without_editor_info theorem normNat_unit {a : Eisenstein} : IsUnit a ↔ normNat a=1 := by
  exact QuadraticAlgebra.isUnit_iff_norm_isUnit.trans Int.isUnit_iff_natAbs_eq

without_editor_info theorem prime_of_normNat_prime {a : Eisenstein} (ha : (normNat a).Prime) : Prime a := by
  apply irreducible_iff_prime.mp
  refine ⟨fun hu => ha.ne_one (normNat_unit.mp hu),?_⟩
  intro b c he
  have hn : normNat a=normNat b*normNat c := by rw [he,normNat_mul]
  obtain h | h := ha.prime.irreducible.isUnit_or_isUnit hn
  · exact Or.inl (normNat_unit.mpr (Nat.isUnit_iff.mp h))
  · exact Or.inr (normNat_unit.mpr (Nat.isUnit_iff.mp h))

without_editor_info theorem normNat_mod_three (a : Eisenstein) : normNat a % 3≠2 := by
  have ht : ∀ a b : ZMod 3, a*a-a*b+b*b≠2 := by decide +kernel
  have hn : (normNat a : ℤ)=QuadraticAlgebra.norm a := by
    simp only [normNat,Int.natCast_natAbs,abs_of_nonneg (eisenstein_norm_nonneg a)]
  intro h
  have hcast : (normNat a : ZMod 3)=2 := by
    apply (ZMod.natCast_eq_natCast_iff' _ _ 3).mpr
    exact h
  have he : ((QuadraticAlgebra.norm a : ℤ) : ZMod 3)=2 := by
    rw [←hn,Int.cast_natCast]
    exact hcast
  apply ht (a.re : ZMod 3) (a.im : ZMod 3)
  simpa [QuadraticAlgebra.norm_def,pow_two,sub_eq_add_neg] using he

without_editor_info theorem prime_integer_of_mod_three {p : ℕ} (hp : p.Prime) (h3 : p%3=2) :
    Prime (p : Eisenstein) := by
  have hn : normNat (p : Eisenstein)=p^2 := by simp [normNat]
  have hnu : ¬IsUnit (p : Eisenstein) := by
    intro h
    have h1 := normNat_unit.mp h
    rw [hn] at h1
    have h2 := hp.two_le
    nlinarith
  apply irreducible_iff_prime.mp
  refine ⟨hnu,?_⟩
  intro a b he
  by_contra h
  obtain ⟨ha,hb⟩ := not_or.mp h
  have hab : normNat a*normNat b=p^2 := by rw [←normNat_mul,←he,hn]
  have hna : normNat a=p := (hp.mul_eq_prime_sq_iff
    (fun hh => ha (normNat_unit.mpr hh)) (fun hh => hb (normNat_unit.mpr hh))).mp hab |>.1
  exact normNat_mod_three a (hna ▸ h3)

without_editor_info theorem small_primary_prime_checks :
    Prime (2 : Eisenstein) ∧ Prime (5 : Eisenstein) ∧ Prime (11 : Eisenstein) ∧
    Prime (17 : Eisenstein) ∧ Prime (⟨-1,-3⟩ : Eisenstein) ∧
    Prime (⟨-1,3⟩ : Eisenstein) ∧ Prime (⟨2,-3⟩ : Eisenstein) := by
  refine ⟨prime_integer_of_mod_three (by norm_num) (by decide),
    prime_integer_of_mod_three (by norm_num) (by decide),
    prime_integer_of_mod_three (by norm_num) (by decide),
    prime_integer_of_mod_three (by norm_num) (by decide),
    prime_of_normNat_prime ?_,prime_of_normNat_prime ?_,prime_of_normNat_prime ?_⟩ <;>
    norm_num [normNat,QuadraticAlgebra.norm_def]

end CubicSpecial

namespace CubicSpecial

without_editor_info def adjacencyEntry {n : ℕ} (e : GraphEdge n) (i : Fin n) : List (Fin n × ℕ) :=
  (if e.src=i then [(e.dst,e.weight.val)] else []) ++
  (if e.dst=i then [(e.src,(-e.weight).val)] else [])

without_editor_info def neighborList {n m : ℕ} (edges : Fin m → GraphEdge n) (i : Fin n) : List (Fin n × ℕ) :=
  (List.ofFn edges).flatMap (fun e => adjacencyEntry e i)

without_editor_info def rowLog {n : ℕ} (row : List (Fin n × ℕ)) (l : Fin n → ZMod 3) : ZMod 3 :=
  (row.map (fun jk => (jk.2 : ZMod 3)*l jk.1)).sum

without_editor_info theorem adjacencyEntry_log {n : ℕ} (e : GraphEdge n) (i : Fin n) (l : Fin n → ZMod 3) :
    rowLog (adjacencyEntry e i) l =
      (if e.src=i then e.weight*l e.dst else 0) - (if e.dst=i then e.weight*l e.src else 0) := by
  by_cases hs : e.src=i <;> by_cases hd : e.dst=i <;>
    simp [rowLog,adjacencyEntry,hs,hd] <;> ring

without_editor_info theorem neighborList_log {n m : ℕ} (edges : Fin m → GraphEdge n) (i : Fin n) (l : Fin n → ZMod 3) :
    rowLog (neighborList edges i) l=incidenceRow edges l i := by
  have h (es : List (GraphEdge n)) :
      rowLog (es.flatMap (fun e => adjacencyEntry e i)) l =
        (es.map (fun e => (if e.src=i then e.weight*l e.dst else 0) -
          (if e.dst=i then e.weight*l e.src else 0))).sum := by
    induction es with
    | nil => simp [rowLog]
    | cons e es ih =>
      simp only [List.flatMap_cons,rowLog,List.map_append,List.sum_append,List.map_cons,List.sum_cons] at *
      rw [ih]
      exact congrArg (·+_) (adjacencyEntry_log e i l)
  unfold neighborList
  rw [h]
  simp only [List.map_ofFn,List.sum_ofFn,incidenceRow,Function.comp_apply]

without_editor_info def rowProduct {n : ℕ} (row : List (Fin n × ℕ)) (H : Fin n → Eisenstein) (C : Eisenstein) : Eisenstein :=
  row.foldr (fun jk v => H jk.1^jk.2*v) C

without_editor_info theorem rowProduct_not_dvd {n : ℕ} (π : Eisenstein) [hp : Fact (Prime π)]
    (row : List (Fin n × ℕ)) (H : Fin n → Eisenstein) {C : Eisenstein}
    (hC : ¬π ∣ C) (hH : ∀ jk ∈ row, ¬π ∣ H jk.1) : ¬π ∣ rowProduct row H C := by
  induction row with
  | nil => exact hC
  | cons jk row ih =>
    intro h
    change π ∣ H jk.1^jk.2*rowProduct row H C at h
    obtain h | h := hp.out.dvd_mul.mp h
    · exact hH jk (List.mem_cons_self) (hp.out.dvd_of_dvd_pow h)
    · exact ih (fun a ha => hH a (List.mem_cons_of_mem _ ha)) h

without_editor_info theorem rowProduct_log {n : ℕ} (π : Eisenstein) [hp : Fact (Prime π)] (h3 : ¬π ∣ 3)
    (row : List (Fin n × ℕ)) (H : Fin n → Eisenstein) {C : Eisenstein}
    (hC : ¬π ∣ C) (hH : ∀ jk ∈ row, ¬π ∣ H jk.1) :
    cubicLog π h3 (rowProduct row H C)=cubicLog π h3 C+rowLog row (fun j => cubicLog π h3 (H j)) := by
  induction row with
  | nil => simp [rowProduct,rowLog]
  | cons jk row ih =>
    have hj := hH jk List.mem_cons_self
    have hr := fun a ha => hH a (List.mem_cons_of_mem _ ha)
    change cubicLog π h3 (H jk.1^jk.2*rowProduct row H C)=_
    rw [cubicLog_mul π h3 (fun h => hj (hp.out.dvd_of_dvd_pow h)) (rowProduct_not_dvd π row H hC hr),
      cubicLog_pow π h3 hj,ih hr]
    simp only [rowLog,List.map_cons,List.sum_cons]
    ring

without_editor_info theorem graph_tame_vanish_lists {n m : ℕ} (edges : Fin m → GraphEdge n)
    (H C : Fin n → Eisenstein) (rows : Fin n → List (Fin n × ℕ))
    (hrows : ∀ i, rows i=neighborList edges i)
    (π : Eisenstein) [Fact (Prime π)] (h3 : ¬π ∣ 3) (hC : ∀ i, ¬π ∣ C i)
    (hsep : ∀ i, π ∣ H i → ∀ jk ∈ rows i, ¬π ∣ H jk.1)
    (hcube : ∀ i, π ∣ H i → ∃ z : Residue π, reduction π (rowProduct (rows i) H (C i))=z^3) :
    graphSum edges H C (tame π h3)=0 := by
  apply graph_tame_cancellation edges H C π h3 hC
  intro i hi
  have hl := cubicLog_residue_cube π h3 (rowProduct_not_dvd π (rows i) H (hC i) (hsep i hi)) (hcube i hi)
  rw [rowProduct_log π h3 (rows i) H (hC i) (hsep i hi)] at hl
  rw [←neighborList_log,←hrows]
  have he : rowLog (rows i) (fun j => cubicLog π h3 (primeUnit π (H j))) =
      rowLog (rows i) (fun j => cubicLog π h3 (H j)) := by
    unfold rowLog
    apply congrArg List.sum
    apply List.map_congr_left
    intro jk hjk
    dsimp only
    rw [primeUnit_of_not_dvd π (hsep i hi jk hjk)]
  rwa [he]

without_editor_info theorem neighborList_not_dvd {n m : ℕ} (edges : Fin m → GraphEdge n) (H : Fin n → Eisenstein)
    (π : Eisenstein) (hE : ∀ e, ¬(π ∣ H (edges e).src ∧ π ∣ H (edges e).dst))
    (i : Fin n) (hi : π ∣ H i) : ∀ jk ∈ neighborList edges i, ¬π ∣ H jk.1 := by
  intro jk hj
  obtain ⟨e,he,hj⟩ := List.mem_flatMap.mp hj
  obtain ⟨z,rfl⟩ := List.mem_ofFn.mp he
  by_cases hs : (edges z).src=i
  · by_cases hd : (edges z).dst=i
    · exact False.elim (hE z ⟨hs ▸ hi,hd ▸ hi⟩)
    · simp [adjacencyEntry,hs,hd] at hj
      subst jk
      exact fun h => hE z ⟨hs ▸ hi,h⟩
  · by_cases hd : (edges z).dst=i
    · simp [adjacencyEntry,hs,hd] at hj
      subst jk
      exact fun h => hE z ⟨h,hd ▸ hi⟩
    · simp [adjacencyEntry,hs,hd] at hj

end CubicSpecial
namespace CubicSpecial

without_editor_info def lambdaDivides (a : Eisenstein) : Bool := decide ((a.re+a.im)%3=0)
without_editor_info def divideLambda (a : Eisenstein) : Eisenstein := ⟨(2*a.re-a.im)/3,(a.re+a.im)/3⟩

without_editor_info theorem lambdaDivides_iff (a : Eisenstein) : lambdaDivides a=true ↔ lambda ∣ a := by
  simp only [lambdaDivides,decide_eq_true_eq,lambda_dvd_iff,Int.dvd_iff_emod_eq_zero]

without_editor_info theorem divideLambda_spec {a : Eisenstein} (ha : lambdaDivides a=true) : a=lambda*divideLambda a := by
  have h : (a.re+a.im)%3=0 := by simpa only [lambdaDivides,decide_eq_true_eq] using ha
  change a=(⟨1,-1⟩ : Eisenstein)*divideLambda a
  ext <;> simp [divideLambda] <;> omega

without_editor_info def splitLambda : ℕ → Eisenstein → ℕ × Eisenstein
  | 0,a => (0,a)
  | k+1,a => if lambdaDivides a then
      let eu := splitLambda k (divideLambda a)
      (eu.1+1,eu.2)
    else (0,a)

without_editor_info theorem splitLambda_spec (k : ℕ) (a : Eisenstein) :
    a=lambda^(splitLambda k a).1*(splitLambda k a).2 := by
  induction k generalizing a with
  | zero => simp [splitLambda]
  | succ k ih =>
    by_cases h : lambdaDivides a=true
    · rw [splitLambda,if_pos h]
      simp only
      calc a=lambda*divideLambda a := divideLambda_spec h
        _=lambda*(lambda^(splitLambda k (divideLambda a)).1*(splitLambda k (divideLambda a)).2) :=
          congrArg (lambda*·) (ih (divideLambda a))
        _=lambda^((splitLambda k (divideLambda a)).1+1)*(splitLambda k (divideLambda a)).2 := by
          rw [pow_succ]; ring
    · simp [splitLambda,h]

without_editor_info def computeWildClass (k : ℕ) (a : Eisenstein) : Option (Fin 4 → ZMod 3) :=
  let eu := splitLambda k a
  if lambdaDivides eu.2 then none else some (wildVec eu.1 (coeffMod 9 eu.2))

without_editor_info theorem computeWildClass_sound {k : ℕ} {a : Eisenstein} {v : Fin 4 → ZMod 3}
    (h : computeWildClass k a=some v) : wildClass a=v := by
  unfold computeWildClass at h
  dsimp only at h
  split at h
  · contradiction
  · rename_i hn
    have hunit : ¬lambda ∣ (splitLambda k a).2 := by
      intro hd
      exact hn ((lambdaDivides_iff _).mpr hd)
    obtain ⟨hv,hu⟩ := primeUnit_factorization lambda _ (splitLambda_spec k a) hunit
    have he := Option.some.inj h
    simpa only [wildClass,hv,hu] using he

without_editor_info theorem exists_digitE_real (a : Eisenstein) (ha : a.im=0) :
    ∃ i : Fin 9, (9 : Eisenstein) ∣ a-digitE i 0 := by
  let i : Fin 9 := ⟨(a.re : ZMod 9).val,ZMod.val_lt _⟩
  refine ⟨i,(coeffMod_zero 9 _).mp ?_⟩
  ext <;> simp [coeffMod,digitE,i,ha]

without_editor_info theorem wildClass_finite_real_lifts {a b : Eisenstein} (hb : b≠0) (haR : a.im=0) (hbR : b.im=0)
    (k : ℕ) (hv : multiplicity lambda b < 2*k) (hd : (3 : Eisenstein)^k ∣ a-b) :
    ∃ i : Fin 9, wildClass a=wildClass (b+(3 : Eisenstein)^k*digitE i 0) := by
  obtain ⟨t,ht⟩ := hd
  have htR : t.im=0 := by
    have hp : (3 : Eisenstein)^k=(((3 : ℤ)^k : ℤ) : Eisenstein) := by push_cast; rfl
    rw [hp] at ht
    have he' := congrArg QuadraticAlgebra.im ht
    simp only [QuadraticAlgebra.im_sub,haR,hbR,sub_self,QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_intCast,QuadraticAlgebra.im_intCast,zero_mul,add_zero] at he'
    norm_num only [Int.cast_id,zero_mul,add_zero] at he'
    exact (mul_eq_zero.mp he'.symm).resolve_left (pow_ne_zero k (by norm_num : (3 : ℤ)≠0))
  obtain ⟨i,q,hq⟩ := exists_digitE_real t htR
  let b' := b+(3 : Eisenstein)^k*digitE i 0
  have hdb : (3 : Eisenstein)^k ∣ b'-b := ⟨digitE i 0,by dsimp [b']; ring⟩
  obtain ⟨hb',hv'⟩ := lambda_low_order_congr hb k hv hdb
  refine ⟨i,?_⟩
  apply wildClass_stable_mod_three_pow hb' (k+2) (by rw [hv']; omega)
  refine ⟨q,?_⟩
  dsimp only [b']
  rw [pow_add]
  linear_combination ht+(3 : Eisenstein)^k*hq

end CubicSpecial


namespace CubicSpecial

abbrev WildVector := Fin 4 → ZMod 3

without_editor_info def wildBilinear : WildVector →ₗ[ZMod 3] WildVector →ₗ[ZMod 3] ZMod 3 where
  toFun a := {
    toFun := wildForm a
    map_add' b c := by simp only [wildForm,Pi.add_apply]; ring
    map_smul' c b := by simp only [wildForm,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring }
  map_add' a b := by apply LinearMap.ext; intro c; exact wildForm_add_left a b c
  map_smul' c a := by
    apply LinearMap.ext
    intro b
    simp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.smul_apply,wildForm,
      Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    ring

structure WildEnvelope where
  base : WildVector
  directions : Fin 4 → WildVector

without_editor_info def WildEnvelope.contains (E : WildEnvelope) (v : WildVector) : Prop :=
  ∃ c : Fin 4 → ZMod 3, v=E.base+∑ j, c j • E.directions j

without_editor_info def WildEnvelope.pivotCoeff (d v : WildVector) : ZMod 3 :=
  if d 0≠0 then v 0*d 0 else if d 1≠0 then v 1*d 1 else
    if d 2≠0 then v 2*d 2 else if d 3≠0 then v 3*d 3 else 0

without_editor_info def WildEnvelope.greedyCoeffs (E : WildEnvelope) (v : WildVector) : Fin 4 → ZMod 3 :=
  let v0 := v-E.base
  let c0 := pivotCoeff (E.directions 0) v0
  let v1 := v0-c0 • E.directions 0
  let c1 := pivotCoeff (E.directions 1) v1
  let v2 := v1-c1 • E.directions 1
  let c2 := pivotCoeff (E.directions 2) v2
  let v3 := v2-c2 • E.directions 2
  let c3 := pivotCoeff (E.directions 3) v3
  ![c0,c1,c2,c3]

without_editor_info def WildEnvelope.fastContains (E : WildEnvelope) (v : WildVector) : Bool :=
  decide (v=E.base+∑ j, E.greedyCoeffs v j • E.directions j)

without_editor_info theorem WildEnvelope.fastContains_sound (E : WildEnvelope) (v : WildVector)
    (h : E.fastContains v=true) : E.contains v :=
  ⟨E.greedyCoeffs v,of_decide_eq_true h⟩

without_editor_info instance (E : WildEnvelope) (v : WildVector) : Decidable (E.contains v) := by
  by_cases h : E.fastContains v=true
  · exact isTrue (E.fastContains_sound v h)
  · exact inferInstanceAs (Decidable (∃ c : Fin 4 → ZMod 3, v=E.base+∑ j, c j • E.directions j))

without_editor_info theorem wild_graph_envelopes {n m : ℕ} (edges : Fin m → GraphEdge n)
    (H C : Fin n → Eisenstein) (E : Fin n → WildEnvelope) (cs : Fin n → WildVector)
    (hH : ∀ i, (E i).contains (wildClass (H i)))
    (hC : ∀ i, wildClass (C i)=cs i)
    (hlinear : ∀ i k, wildForm ((E i).directions k) (graphStar edges (fun i => (E i).base) cs i)=0)
    (hcross : ∀ e k l, wildForm ((E (edges e).src).directions k) ((E (edges e).dst).directions l)=0) :
    graphSum edges H C wild=vectorGraph edges (fun i => (E i).base) cs wildBilinear := by
  classical
  choose c hc using hH
  have he : (fun i => wildClass (H i))=(fun i => (E i).base+∑ j, c i j • (E i).directions j) :=
    funext hc
  have hce : (fun i => wildClass (C i))=cs := funext hC
  change vectorGraph edges (fun i => wildClass (H i)) (fun i => wildClass (C i)) wildBilinear = _
  rw [he,hce]
  exact vectorGraph_affine_constant edges (fun i => (E i).base) cs (fun i => (E i).directions)
    wildBilinear wildForm_skew hlinear hcross c

without_editor_info theorem wild_envelope_stable (E : WildEnvelope) {a b : Eisenstein} (hb : b≠0)
    (k : ℕ) (hv : multiplicity lambda b+4≤2*k) (hd : (3 : Eisenstein)^k ∣ a-b)
    (hE : E.contains (wildClass b)) : E.contains (wildClass a) := by
  rwa [wildClass_stable_mod_three_pow hb k hv hd]

without_editor_info theorem wild_envelope_lifts (E : WildEnvelope) {a b : Eisenstein} (hb : b≠0)
    (k : ℕ) (hv : multiplicity lambda b<2*k) (hd : (3 : Eisenstein)^k ∣ a-b)
    (hE : ∀ i j : Fin 9, E.contains (wildClass (b+(3 : Eisenstein)^k*digitE i j))) :
    E.contains (wildClass a) := by
  obtain ⟨i,j,h⟩ := wildClass_finite_lifts hb k hv hd
  rw [h]
  exact hE i j

without_editor_info theorem wild_envelope_real_lifts (E : WildEnvelope) {a b : Eisenstein} (hb : b≠0)
    (haR : a.im=0) (hbR : b.im=0)
    (k : ℕ) (hv : multiplicity lambda b<2*k) (hd : (3 : Eisenstein)^k ∣ a-b)
    (hE : ∀ i : Fin 9, E.contains (wildClass (b+(3 : Eisenstein)^k*digitE i 0))) :
    E.contains (wildClass a) := by
  obtain ⟨i,h⟩ := wildClass_finite_real_lifts hb haR hbR k hv hd
  rw [h]
  exact hE i

end CubicSpecial
namespace CubicSpecial

without_editor_info def computedContains (E : WildEnvelope) (a : Eisenstein) : Prop :=
  match computeWildClass 32 a with
  | none => False
  | some v => E.contains v

without_editor_info instance (E : WildEnvelope) (a : Eisenstein) : Decidable (computedContains E a) := by
  unfold computedContains
  split <;> infer_instance

without_editor_info theorem computedContains_sound (E : WildEnvelope) (a : Eisenstein) (h : computedContains E a) :
    E.contains (wildClass a) := by
  unfold computedContains at h
  split at h
  · contradiction
  · rename_i v he
    rwa [computeWildClass_sound he]

without_editor_info def wildEnvelopeCheck (E : WildEnvelope) (b : Eisenstein) (k : ℕ) (real : Bool) : Prop :=
  if b=0 then
    if real then ∀ e c : ZMod 3, E.contains (e • ![2,2,0,0]+c • ![0,0,1,0])
    else ∀ v : WildVector, E.contains v
  else
    let eu := splitLambda 32 b
    lambdaDivides eu.2=false ∧
    if eu.1+4≤2*k then E.contains (wildVec eu.1 (coeffMod 9 eu.2))
    else eu.1<2*k ∧
      if real then ∀ i : Fin 9, computedContains E (b+(3 : Eisenstein)^k*digitE i 0)
      else ∀ i j : Fin 9, computedContains E (b+(3 : Eisenstein)^k*digitE i j)

without_editor_info instance (E : WildEnvelope) (b : Eisenstein) (k : ℕ) (real : Bool) :
    Decidable (wildEnvelopeCheck E b k real) := by
  unfold wildEnvelopeCheck
  infer_instance

without_editor_info theorem wildEnvelopeCheck_sound (E : WildEnvelope) (b : Eisenstein) (k : ℕ) (real : Bool)
    (hcheck : wildEnvelopeCheck E b k real) {a : Eisenstein} (ha : a≠0)
    (hd : (3 : Eisenstein)^k ∣ a-b)
    (hreal : real=true → a.im=0 ∧ b.im=0) : E.contains (wildClass a) := by
  unfold wildEnvelopeCheck at hcheck
  by_cases hb : b=0
  · rw [if_pos hb] at hcheck
    cases hr : real
    · exact (by simpa only [hr,Bool.false_eq_true,↓reduceIte] using hcheck : ∀ v, E.contains v) _
    · have hR := (hreal hr).1
      have hae : a=(a.re : Eisenstein) := by ext <;> simp [hR]
      have han : a.re≠0 := by intro h; apply ha; simpa only [h,Int.cast_zero] using hae
      obtain ⟨e,c,hc⟩ := wildClass_integer a.re han
      rw [hae,hc]
      have hE : ∀ e c : ZMod 3, E.contains
          (e • (![2,2,0,0] : WildVector)+c • (![0,0,1,0] : WildVector)) := by
        simpa only [hr,↓reduceIte] using hcheck
      exact hE e c
  · rw [if_neg hb] at hcheck
    obtain ⟨hn,hE⟩ := hcheck
    have hunit : ¬lambda ∣ (splitLambda 32 b).2 := by
      intro h
      have h' := (lambdaDivides_iff _).mpr h
      rw [hn] at h'
      contradiction
    obtain ⟨hv,hu⟩ := primeUnit_factorization lambda _ (splitLambda_spec 32 b) hunit
    by_cases hbound : (splitLambda 32 b).1+4≤2*k
    · rw [if_pos hbound] at hE
      apply wild_envelope_stable E hb k (by rwa [hv]) hd
      simpa only [wildClass,hv,hu] using hE
    · rw [if_neg hbound] at hE
      obtain ⟨hsmall,hE⟩ := hE
      have hsmall' : multiplicity lambda b<2*k := by rwa [hv]
      cases hr : real
      · apply wild_envelope_lifts E hb k hsmall' hd
        intro i j
        simp only [hr,Bool.false_eq_true,↓reduceIte] at hE
        exact computedContains_sound E _ (hE i j)
      · apply wild_envelope_real_lifts E hb (hreal hr).1 (hreal hr).2 k hsmall' hd
        intro i
        simp only [hr,↓reduceIte] at hE
        exact computedContains_sound E _ (hE i)

without_editor_info def residueE (m : ℕ) (a : Eisenstein) : Eisenstein := ⟨a.re%m,a.im%m⟩

without_editor_info theorem residueE_dvd (m : ℕ) (a : Eisenstein) : (m : Eisenstein) ∣ a-residueE m a := by
  apply (coeffMod_zero m _).mp
  ext <;> simp [coeffMod,residueE]

without_editor_info theorem wildEnvelopeCheck_residue_sound (E : WildEnvelope) (b : Eisenstein) (k : ℕ) (real : Bool)
    (hcheck : wildEnvelopeCheck E (residueE (3^k) b) k real) {a : Eisenstein} (ha : a≠0)
    (hd : (3 : Eisenstein)^k ∣ a-b) (hreal : real=true → a.im=0 ∧ b.im=0) :
    E.contains (wildClass a) := by
  apply wildEnvelopeCheck_sound E _ k real hcheck ha
  · have h := dvd_add hd (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using residueE_dvd (3^k) b)
    simpa only [sub_add_sub_cancel] using h
  · intro hr
    exact ⟨(hreal hr).1,by simp [residueE,(hreal hr).2]⟩

end CubicSpecial


namespace CubicSpecial

without_editor_info theorem prime_dvd_normNat (π : Eisenstein) : π ∣ (normNat π : Eisenstein) := by
  have hn : (normNat π : ℤ)=QuadraticAlgebra.norm π := by
    simp only [normNat,Int.natCast_natAbs,abs_of_nonneg (eisenstein_norm_nonneg π)]
  have hc : (normNat π : Eisenstein)=π*star π := by
    rw [←Int.cast_natCast,hn]
    exact QuadraticAlgebra.algebraMap_norm_eq_mul_star π
  rw [hc]
  exact dvd_mul_right _ _

without_editor_info theorem coeffMod_eq_reduction (π : Eisenstein) [Fact (Prime π)] {a b : Eisenstein}
    (h : coeffMod (normNat π) a=coeffMod (normNat π) b) : reduction π a=reduction π b := by
  have hn : (normNat π : Eisenstein) ∣ a-b := (coeffMod_zero _ _).mp (by rw [map_sub,h,sub_self])
  have he := (reduction_zero π _).mpr ((prime_dvd_normNat π).trans hn)
  rwa [map_sub,sub_eq_zero] at he

without_editor_info theorem cubicLog_of_euler_witness (π : Eisenstein) [Fact (Prime π)] (h3 : ¬π ∣ 3)
    {u w : Eisenstein} (hu : ¬π ∣ u) (e : Fin 3)
    (he : coeffMod (normNat π) u ^ ((normNat π-1)/3)=
      coeffMod (normNat π) (ω^e.val+π*w)) : cubicLog π h3 u=(e.val : ZMod 3) := by
  have hq : Fintype.card (Residue π)=normNat π := by
    simpa only [Nat.card_eq_fintype_card,normNat] using residue_card π
  have hred : reduction π u ^ ((normNat π-1)/3)=reduction π (ω^e.val) := by
    have h := coeffMod_eq_reduction π (a := u^((normNat π-1)/3)) (b := ω^e.val+π*w)
      (by simpa only [map_pow] using he)
    simpa only [map_pow,map_add,map_mul,(reduction_zero π π).mpr dvd_rfl,zero_mul,add_zero] using h
  have hs : cubicSymbol π h3 u=ω^e.val := by
    have he3 : (ω^e.val)^3=1 := by
      rw [←pow_mul,mul_comm e.val 3,pow_mul,omega_primitive.pow_eq_one,one_pow]
    apply cubic_value_injective (reduction π) (residue_omega_primitive π h3)
      (Or.inr (cubicSymbol_cube π h3 hu)) (Or.inr he3)
    change reduction π (primeCharacter π h3 (reduction π u))=_
    rw [(primeCharacter_spec π h3).2,hq]
    exact hred
  exact (congrArg logOmega hs).trans (logOmega_pow e.val)

structure TameCertificate where
  exponent : ℕ
  unit : Eisenstein
  inv : Eisenstein
  invQuot : Eisenstein
  cubic : Fin 3
  cubicQuot : Eisenstein

without_editor_info def TameCertificate.check (c : TameCertificate) (π a : Eisenstein) : Prop :=
  a=π^c.exponent*c.unit ∧ c.unit*c.inv+π*c.invQuot=1 ∧
  coeffMod (normNat π) c.unit ^ ((normNat π-1)/3)=
    coeffMod (normNat π) (ω^c.cubic.val+π*c.cubicQuot)

without_editor_info instance (c : TameCertificate) (π a : Eisenstein) : Decidable (c.check π a) := by
  unfold TameCertificate.check
  infer_instance

without_editor_info noncomputable def tameClass (π : Eisenstein) [Fact (Prime π)] (h3 : ¬π ∣ 3) (a : Eisenstein) :
    Fin 2 → ZMod 3 := ![multiplicity π a,cubicLog π h3 (primeUnit π a)]

without_editor_info theorem TameCertificate.sound (c : TameCertificate) (π : Eisenstein) [hp : Fact (Prime π)]
    (h3 : ¬π ∣ 3) {a : Eisenstein} (hc : c.check π a) :
    tameClass π h3 a=![(c.exponent : ZMod 3),(c.cubic.val : ZMod 3)] := by
  obtain ⟨he,hi,hl⟩ := hc
  have hu : ¬π ∣ c.unit := by
    intro h
    have h1 : π ∣ (1 : Eisenstein) := by
      rw [←hi]
      exact dvd_add (dvd_mul_of_dvd_left h c.inv) (dvd_mul_right _ _)
    exact hp.out.not_dvd_one h1
  obtain ⟨hv,hu'⟩ := primeUnit_factorization π c.exponent he hu
  simp only [tameClass,hv,hu',cubicLog_of_euler_witness π h3 hu c.cubic hl]

without_editor_info theorem tameClass_congr (π : Eisenstein) [Fact (Prime π)] (h3 : ¬π ∣ 3)
    {a b : Eisenstein} (hb : b≠0) (hd : π^(multiplicity π b+1) ∣ a-b) :
    tameClass π h3 a=tameClass π h3 b := by
  obtain ⟨hv,hu⟩ := primeUnit_congruence π hb (by decide : 0<1) hd
  have hl : cubicLog π h3 (primeUnit π a)=cubicLog π h3 (primeUnit π b) := by
    apply cubicLog_congr
    have he := (reduction_zero π _).mpr (by simpa only [pow_one] using hu)
    rwa [map_sub,sub_eq_zero] at he
  simp only [tameClass,hv,hl]

end CubicSpecial


namespace CubicSpecial

without_editor_info theorem natCast_dvd_intCast (p : ℕ) (a : ℤ) : (p : Eisenstein) ∣ (a : Eisenstein) ↔ (p : ℤ) ∣ a := by
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨b.re,?_⟩
    have h := congrArg QuadraticAlgebra.re hb
    simpa using h
  · rintro ⟨b,hb⟩
    exact ⟨(b : Eisenstein),by exact_mod_cast hb⟩

without_editor_info theorem cubicLog_integer_inert (p : ℕ) [Fact p.Prime] [Fact (Prime (p : Eisenstein))]
    (h3 : ¬(p : Eisenstein) ∣ 3) (hp : p%3=2) (a : ℤ) (ha : ¬(p : ℤ) ∣ a) :
    cubicLog (p : Eisenstein) h3 (a : Eisenstein)=0 := by
  have hF : (p : ℤ) ∣ a^p-a := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by
    push_cast
    rw [ZMod.pow_card,sub_self])
  have hD : (p : Eisenstein) ∣ (a : Eisenstein)^p-(a : Eisenstein) := by
    simpa only [Int.cast_sub,Int.cast_pow] using (natCast_dvd_intCast p (a^p-a)).mpr hF
  have hR := (reduction_zero (p : Eisenstein) _).mpr hD
  rw [map_sub,map_pow,sub_eq_zero] at hR
  have hS := congrArg (primeCharacter (p : Eisenstein) h3) hR
  simp only [map_pow] at hS
  change cubicSymbol (p : Eisenstein) h3 (a : Eisenstein)^p = cubicSymbol (p : Eisenstein) h3 (a : Eisenstein) at hS
  have hnd := (natCast_dvd_intCast p a).not.mpr ha
  have hc := cubicSymbol_cube (p : Eisenstein) h3 hnd
  have he : cubicSymbol (p : Eisenstein) h3 (a : Eisenstein)^p =
      cubicSymbol (p : Eisenstein) h3 (a : Eisenstein)^2 := by
    calc _=cubicSymbol (p : Eisenstein) h3 (a : Eisenstein)^(p%3+3*(p/3)) :=
        congrArg (fun n : ℕ => cubicSymbol (p : Eisenstein) h3 (a : Eisenstein)^n) (Nat.mod_add_div p 3).symm
      _=_ := by rw [pow_add,pow_mul,hc,one_pow,mul_one,hp]
  have hn : cubicSymbol (p : Eisenstein) h3 (a : Eisenstein)≠0 :=
    (cubicSymbol_eq_zero (p : Eisenstein) h3 _).not.mpr hnd
  have h1 : cubicSymbol (p : Eisenstein) h3 (a : Eisenstein)=1 := by
    apply mul_left_cancel₀ hn
    simpa only [pow_two,mul_one] using he.symm.trans hS
  exact (congrArg logOmega h1).trans logOmega_one

without_editor_info theorem tameClass_integer_inert (p : ℕ) [hp : Fact p.Prime] [Fact (Prime (p : Eisenstein))]
    (h3 : ¬(p : Eisenstein) ∣ 3) (hmod : p%3=2) (a : ℤ) (ha : a≠0) :
    ∃ e : ZMod 3, tameClass (p : Eisenstein) h3 (a : Eisenstein)=![e,0] := by
  have hpZ : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp.out)
  obtain ⟨t,he,ht⟩ := (FiniteMultiplicity.of_prime_left hpZ ha).exists_eq_pow_mul_and_not_dvd
  have he' : (a : Eisenstein)=(p : Eisenstein)^multiplicity (p : ℤ) a*(t : Eisenstein) := by exact_mod_cast he
  obtain ⟨hv,hu⟩ := primeUnit_factorization (p : Eisenstein) _ he' ((natCast_dvd_intCast p t).not.mpr ht)
  refine ⟨multiplicity (p : ℤ) a,?_⟩
  simp only [tameClass,hv,hu,cubicLog_integer_inert p h3 hmod t ht]

end CubicSpecial


namespace CubicSpecial

without_editor_info def tameForm (a b : WildVector) : ZMod 3 := a 0*b 1-a 1*b 0+a 2*b 3-a 3*b 2
without_editor_info def tameBilinear : WildVector →ₗ[ZMod 3] WildVector →ₗ[ZMod 3] ZMod 3 where
  toFun a := {
    toFun := tameForm a
    map_add' b c := by simp only [tameForm,Pi.add_apply]; ring
    map_smul' c b := by simp only [tameForm,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring }
  map_add' a b := by
    apply LinearMap.ext
    intro c
    change tameForm (a+b) c=tameForm a c+tameForm b c
    simp only [tameForm,Pi.add_apply]
    ring
  map_smul' c a := by
    apply LinearMap.ext
    intro b
    simp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.smul_apply,tameForm,
      Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    ring

without_editor_info theorem tameForm_skew (a b : WildVector) : tameForm a b= -tameForm b a := by unfold tameForm; ring

without_editor_info noncomputable def paddedTame (π : Eisenstein) [Fact (Prime π)] (h3 : ¬π ∣ 3) (a : Eisenstein) : WildVector :=
  ![tameClass π h3 a 0,tameClass π h3 a 1,0,0]

without_editor_info def TameCertificate.vector (c : TameCertificate) : WildVector := ![c.exponent,c.cubic.val,0,0]

without_editor_info theorem TameCertificate.vector_sound (c : TameCertificate) (π : Eisenstein) [Fact (Prime π)]
    (h3 : ¬π ∣ 3) {a : Eisenstein} (hc : c.check π a) : paddedTame π h3 a=c.vector := by
  simp only [paddedTame,c.sound π h3 hc,TameCertificate.vector]
  rfl

without_editor_info theorem TameCertificate.valuation (c : TameCertificate) (π : Eisenstein) [hp : Fact (Prime π)]
    {a : Eisenstein} (hc : c.check π a) : a≠0 ∧ multiplicity π a=c.exponent := by
  have hu : ¬π ∣ c.unit := by
    intro h
    apply hp.out.not_dvd_one
    rw [←hc.2.1]
    exact dvd_add (dvd_mul_of_dvd_left h c.inv) (dvd_mul_right _ _)
  have hun : c.unit≠0 := fun h => hu (h ▸ dvd_zero _)
  refine ⟨?_,(primeUnit_factorization π _ hc.1 hu).1⟩
  rw [hc.1]
  exact mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) hun

without_editor_info theorem tame_graph_envelopes {n m : ℕ} (edges : Fin m → GraphEdge n)
    (H C : Fin n → Eisenstein) (π : Eisenstein) [Fact (Prime π)] (h3 : ¬π ∣ 3)
    (E : Fin n → WildEnvelope) (cs : Fin n → WildVector)
    (hH : ∀ i, (E i).contains (paddedTame π h3 (H i)))
    (hC : ∀ i, paddedTame π h3 (C i)=cs i)
    (hlinear : ∀ i k, tameForm ((E i).directions k) (graphStar edges (fun i => (E i).base) cs i)=0)
    (hcross : ∀ e k l, tameForm ((E (edges e).src).directions k) ((E (edges e).dst).directions l)=0) :
    graphSum edges H C (tame π h3)=vectorGraph edges (fun i => (E i).base) cs tameBilinear := by
  classical
  choose c hc using hH
  have he : (fun i => paddedTame π h3 (H i))=(fun i => (E i).base+∑ j, c i j • (E i).directions j) := funext hc
  have hce : (fun i => paddedTame π h3 (C i))=cs := funext hC
  have hid : graphSum edges H C (tame π h3)=
      vectorGraph edges (fun i => paddedTame π h3 (H i)) (fun i => paddedTame π h3 (C i)) tameBilinear := by
    simp [graphSum,vectorGraph,tameBilinear,tameForm,paddedTame,tameClass,tame,mul_comm]
  rw [hid,he,hce]
  exact vectorGraph_affine_constant edges (fun i => (E i).base) cs (fun i => (E i).directions)
    tameBilinear tameForm_skew hlinear hcross c

without_editor_info def inertEnvelopeCheck (E : WildEnvelope) (p : ℕ) (b : Eisenstein) (k : ℕ) (real : Bool)
    (c : TameCertificate) : Prop :=
  if b=0 then
    if real then ∀ e : ZMod 3, E.contains ![e,0,0,0]
    else ∀ e l : ZMod 3, E.contains ![e,l,0,0]
  else c.check (p : Eisenstein) b ∧ c.exponent<k ∧ E.contains c.vector

without_editor_info instance (E : WildEnvelope) (p : ℕ) (b : Eisenstein) (k : ℕ) (real : Bool) (c : TameCertificate) :
    Decidable (inertEnvelopeCheck E p b k real c) := by unfold inertEnvelopeCheck; infer_instance

without_editor_info theorem inertEnvelopeCheck_sound (E : WildEnvelope) (p : ℕ) [Fact p.Prime] [Fact (Prime (p : Eisenstein))]
    (h3 : ¬(p : Eisenstein) ∣ 3) (hp : p%3=2) (b : Eisenstein) (k : ℕ) (real : Bool) (c : TameCertificate)
    (hcheck : inertEnvelopeCheck E p b k real c) {a : Eisenstein} (ha : a≠0)
    (hd : (p : Eisenstein)^k ∣ a-b) (hreal : real=true → a.im=0) :
    E.contains (paddedTame (p : Eisenstein) h3 a) := by
  unfold inertEnvelopeCheck at hcheck
  by_cases hb : b=0
  · rw [if_pos hb] at hcheck
    cases hr : real
    · simp only [hr,Bool.false_eq_true,↓reduceIte] at hcheck
      exact hcheck _ _
    · simp only [hr,↓reduceIte] at hcheck
      have hR := hreal hr
      have hae : a=(a.re : Eisenstein) := by ext <;> simp [hR]
      have han : a.re≠0 := by intro h; apply ha; simpa only [h,Int.cast_zero] using hae
      obtain ⟨e,he⟩ := tameClass_integer_inert p h3 hp a.re han
      have hvect : paddedTame (p : Eisenstein) h3 a=![e,0,0,0] := by
        unfold paddedTame
        rw [hae,he]
        rfl
      rw [hvect]
      exact hcheck e
  · rw [if_neg hb] at hcheck
    obtain ⟨hc,hbound,he⟩ := hcheck
    have hv := (c.valuation (p : Eisenstein) hc).2
    have hcon : tameClass (p : Eisenstein) h3 a=tameClass (p : Eisenstein) h3 b := by
      apply tameClass_congr _ h3 hb
      exact (pow_dvd_pow (p : Eisenstein) (by omega : multiplicity (p : Eisenstein) b+1≤k)).trans hd
    have hvect : paddedTame (p : Eisenstein) h3 a=c.vector := by
      simp only [paddedTame,hcon]
      exact c.vector_sound _ h3 hc
    rwa [hvect]

without_editor_info theorem inertEnvelopeCheck_residue_sound (E : WildEnvelope) (p : ℕ) [Fact p.Prime] [Fact (Prime (p : Eisenstein))]
    (h3 : ¬(p : Eisenstein) ∣ 3) (hp : p%3=2) (b : Eisenstein) (k : ℕ) (real : Bool) (c : TameCertificate)
    (hcheck : inertEnvelopeCheck E p (residueE (p^k) b) k real c) {a : Eisenstein} (ha : a≠0)
    (hd : (p : Eisenstein)^k ∣ a-b) (hreal : real=true → a.im=0) :
    E.contains (paddedTame (p : Eisenstein) h3 a) := by
  apply inertEnvelopeCheck_sound E p h3 hp _ k real c hcheck ha ?_ hreal
  have hh := dvd_add hd (by simpa only [Nat.cast_pow] using residueE_dvd (p^k) b)
  simpa only [sub_add_sub_cancel] using hh

end CubicSpecial


namespace CubicSpecial

without_editor_info def splitRepresentative (p : ℕ) (r : ℤ) (k : ℕ) (b : Eisenstein) : ℤ :=
  (b.re+b.im*r)%(p : ℤ)^k

without_editor_info theorem splitRepresentative_congr (π : Eisenstein) (p : ℕ) (r : ℤ) (k : ℕ)
    {a b : Eisenstein} (hpi : π ∣ (p : Eisenstein)) (hr : π^k ∣ ω-(r : Eisenstein))
    (hd : (p : Eisenstein)^k ∣ a-b) : π^k ∣ a-(splitRepresentative p r k b : Eisenstein) := by
  have hpw : π^k ∣ (p : Eisenstein)^k := pow_dvd_pow_of_dvd hpi k
  have h1 := hpw.trans hd
  let n : ℤ := b.re+b.im*r
  have he : b-(n : Eisenstein)=(b.im : Eisenstein)*(ω-(r : Eisenstein)) := by
    have hb := eisenstein_coordinates b
    dsimp only [n]
    push_cast
    linear_combination hb
  have h2 : π^k ∣ b-(n : Eisenstein) := he ▸ dvd_mul_of_dvd_right hr (b.im : Eisenstein)
  have h3Z : (p : ℤ)^k ∣ n-n%(p : ℤ)^k := by
    refine ⟨n/(p : ℤ)^k,?_⟩
    linear_combination -(Int.emod_add_mul_ediv n ((p : ℤ)^k))
  have h3 : (p : Eisenstein)^k ∣ (n : Eisenstein)-(splitRepresentative p r k b : Eisenstein) := by
    obtain ⟨q,hq⟩ := h3Z
    exact ⟨(q : Eisenstein),by dsimp only [splitRepresentative,n] at *; exact_mod_cast hq⟩
  have h := dvd_add (dvd_add h1 h2) (hpw.trans h3)
  simpa only [sub_add_sub_cancel] using h

without_editor_info def splitKnown (π : Eisenstein) (p : ℕ) (r : ℤ) (k : ℕ) (b : Eisenstein) (c : TameCertificate) : Prop :=
  if splitRepresentative p r k b=0 then True else c.check π (splitRepresentative p r k b : Eisenstein) ∧ c.exponent<k

without_editor_info def splitMatches (p : ℕ) (r : ℤ) (k : ℕ) (b : Eisenstein) (c : TameCertificate) (e l : ZMod 3) : Prop :=
  splitRepresentative p r k b=0 ∨ (e=(c.exponent : ZMod 3) ∧ l=(c.cubic.val : ZMod 3))

without_editor_info instance (π : Eisenstein) (p : ℕ) (r : ℤ) (k : ℕ) (b : Eisenstein) (c : TameCertificate) :
    Decidable (splitKnown π p r k b c) := by unfold splitKnown; infer_instance
without_editor_info instance (p : ℕ) (r : ℤ) (k : ℕ) (b : Eisenstein) (c : TameCertificate) (e l : ZMod 3) :
    Decidable (splitMatches p r k b c e l) := by unfold splitMatches; infer_instance

without_editor_info theorem splitMatches_sound (π : Eisenstein) [Fact (Prime π)] (h3 : ¬π ∣ 3)
    (p : ℕ) (r : ℤ) (k : ℕ) (b : Eisenstein) (c : TameCertificate)
    (hknown : splitKnown π p r k b c) (hpi : π ∣ (p : Eisenstein)) (hr : π^k ∣ ω-(r : Eisenstein))
    {a : Eisenstein} (hd : (p : Eisenstein)^k ∣ a-b) :
    splitMatches p r k b c (tameClass π h3 a 0) (tameClass π h3 a 1) := by
  by_cases hb : splitRepresentative p r k b=0
  · exact Or.inl hb
  · have hc : c.check π (splitRepresentative p r k b : Eisenstein) ∧ c.exponent<k := by
      simpa only [splitKnown,if_neg hb] using hknown
    obtain ⟨hbn,hval⟩ := c.valuation π hc.1
    have hcon := tameClass_congr π h3 hbn
      ((pow_dvd_pow π (by omega : multiplicity π (splitRepresentative p r k b : Eisenstein)+1≤k)).trans
        (splitRepresentative_congr π p r k hpi hr hd))
    right
    rw [hcon,c.sound π h3 hc.1]
    exact ⟨rfl,rfl⟩

without_editor_info noncomputable def jointTame (π ρ : Eisenstein) [Fact (Prime π)] [Fact (Prime ρ)]
    (hπ : ¬π ∣ 3) (hρ : ¬ρ ∣ 3) (a : Eisenstein) : WildVector :=
  ![tameClass π hπ a 0,tameClass π hπ a 1,tameClass ρ hρ a 0,tameClass ρ hρ a 1]

without_editor_info def jointEnvelopeCheck (E : WildEnvelope) (π ρ : Eisenstein) (p : ℕ) (r s : ℤ) (k : ℕ)
    (b : Eisenstein) (c d : TameCertificate) : Prop :=
  splitKnown π p r k b c ∧ splitKnown ρ p s k b d ∧
  ∀ e l f m : ZMod 3, splitMatches p r k b c e l → splitMatches p s k b d f m → E.contains ![e,l,f,m]

without_editor_info instance (E : WildEnvelope) (π ρ : Eisenstein) (p : ℕ) (r s : ℤ) (k : ℕ)
    (b : Eisenstein) (c d : TameCertificate) : Decidable (jointEnvelopeCheck E π ρ p r s k b c d) := by
  unfold jointEnvelopeCheck
  infer_instance

without_editor_info theorem jointEnvelopeCheck_sound (E : WildEnvelope) (π ρ : Eisenstein) [Fact (Prime π)] [Fact (Prime ρ)]
    (hπ : ¬π ∣ 3) (hρ : ¬ρ ∣ 3) (p : ℕ) (r s : ℤ) (k : ℕ)
    (b : Eisenstein) (c d : TameCertificate) (hcheck : jointEnvelopeCheck E π ρ p r s k b c d)
    (hpi : π ∣ (p : Eisenstein)) (hrho : ρ ∣ (p : Eisenstein))
    (hr : π^k ∣ ω-(r : Eisenstein)) (hs : ρ^k ∣ ω-(s : Eisenstein))
    {a : Eisenstein} (hd : (p : Eisenstein)^k ∣ a-b) : E.contains (jointTame π ρ hπ hρ a) := by
  exact hcheck.2.2 _ _ _ _ (splitMatches_sound π hπ p r k b c hcheck.1 hpi hr hd)
    (splitMatches_sound ρ hρ p s k b d hcheck.2.1 hrho hs hd)

without_editor_info theorem joint_graph_envelopes {n m : ℕ} (edges : Fin m → GraphEdge n)
    (H C : Fin n → Eisenstein) (π ρ : Eisenstein) [Fact (Prime π)] [Fact (Prime ρ)] (hπ : ¬π ∣ 3) (hρ : ¬ρ ∣ 3)
    (E : Fin n → WildEnvelope) (cs : Fin n → WildVector)
    (hH : ∀ i, (E i).contains (jointTame π ρ hπ hρ (H i)))
    (hC : ∀ i, jointTame π ρ hπ hρ (C i)=cs i)
    (hlinear : ∀ i k, tameForm ((E i).directions k) (graphStar edges (fun i => (E i).base) cs i)=0)
    (hcross : ∀ e k l, tameForm ((E (edges e).src).directions k) ((E (edges e).dst).directions l)=0) :
    graphSum edges H C (tame π hπ)+graphSum edges H C (tame ρ hρ)=
      vectorGraph edges (fun i => (E i).base) cs tameBilinear := by
  classical
  choose c hc using hH
  have he : (fun i => jointTame π ρ hπ hρ (H i))=(fun i => (E i).base+∑ j, c i j • (E i).directions j) := funext hc
  have hce : (fun i => jointTame π ρ hπ hρ (C i))=cs := funext hC
  have hid : graphSum edges H C (tame π hπ)+graphSum edges H C (tame ρ hρ)=
      vectorGraph edges (fun i => jointTame π ρ hπ hρ (H i)) (fun i => jointTame π ρ hπ hρ (C i)) tameBilinear := by
    simp [graphSum,vectorGraph,tameBilinear,tameForm,jointTame,tameClass,tame,
      mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,mul_comm]
    ring
  rw [hid,he,hce]
  exact vectorGraph_affine_constant edges (fun i => (E i).base) cs (fun i => (E i).directions)
    tameBilinear tameForm_skew hlinear hcross c

end CubicSpecial
namespace CompactResidueCover

without_editor_info def children (F : ℤ → ℤ → ℤ) (p : ℕ) (m a b : ℤ) : List (ℤ × ℤ) :=
  ((List.finRange p).flatMap fun i => (List.finRange p).map fun j =>
    (a+m*(i.val : ℤ), b+m*(j.val : ℤ))).filter fun q => decide (m*(p : ℤ)∣F q.1 q.2)

without_editor_info theorem lift_integer (p : ℕ) (hp : 0<p) (m a x : ℤ) (hx : m∣x-a) :
    ∃ i : Fin p, m*(p : ℤ)∣x-(a+m*(i.val : ℤ)) := by
  obtain ⟨t,ht⟩ := hx
  have ht0 : 0≤t%(p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
  have ht1 : t%(p : ℤ)<p := Int.emod_lt_of_pos _ (by exact_mod_cast hp)
  let i : Fin p := ⟨(t%(p : ℤ)).toNat,by omega⟩
  have hi : (i.val : ℤ)=t%(p : ℤ) := by simp [i,Int.toNat_of_nonneg ht0]
  refine ⟨i,t/(p : ℤ),?_⟩
  rw [hi]
  linear_combination ht-m*(Int.emod_add_mul_ediv t (p : ℤ))

without_editor_info theorem cover (F : ℤ → ℤ → ℤ)
    (congr : ∀ {m x u a b : ℤ}, m∣x-a → m∣u-b → m∣F x u-F a b)
    (P : ℤ → ℤ → Prop) (p : ℕ) (hp : 0<p) (m a b : ℤ) (cs : List (ℤ × ℤ))
    (hc : children F p m a b=cs)
    (step : ∀ q∈cs, ∀ x u : ℤ, F x u=0 → m*(p : ℤ)∣x-q.1 → m*(p : ℤ)∣u-q.2 → P x u)
    {x u : ℤ} (hf : F x u=0) (hx : m∣x-a) (hu : m∣u-b) : P x u := by
  obtain ⟨i,hi⟩ := lift_integer p hp m a x hx
  obtain ⟨j,hj⟩ := lift_integer p hp m b u hu
  have hd : m*(p : ℤ)∣F (a+m*(i.val : ℤ)) (b+m*(j.val : ℤ)) := by
    simpa only [hf,zero_sub,dvd_neg] using congr hi hj
  apply step (a+m*(i.val : ℤ),b+m*(j.val : ℤ)) ?_ x u hf hi hj
  rw [←hc,children,List.mem_filter]
  refine ⟨?_,?_⟩
  · exact List.mem_flatMap.mpr ⟨i,List.mem_finRange i,
      List.mem_map.mpr ⟨j,List.mem_finRange j,rfl⟩⟩
  · exact decide_eq_true hd

end CompactResidueCover
namespace CubicSpecial
without_editor_info def unpackWild (a : ℕ) : WildVector :=
  ![(a : ZMod 3),((a/3 : ℕ) : ZMod 3),((a/9 : ℕ) : ZMod 3),((a/27 : ℕ) : ZMod 3)]
without_editor_info def packedWildAt (v : Array ℕ) (j : ℕ) : WildVector := unpackWild (v.getD j 0)
without_editor_info def packedEnvelope (v : Array ℕ) (i : ℕ) : WildEnvelope :=
  ⟨packedWildAt v (5*i),fun j => packedWildAt v (5*i+j.val+1)⟩
end CubicSpecial



namespace CubicSpecial

without_editor_info def listEdges {n m : ℕ} (es : List (GraphEdge n)) (h : es.length=m)
    (i : Fin m) : GraphEdge n := es.get (Fin.cast h.symm i)

without_editor_info theorem ofFn_listEdges {n m : ℕ} (es : List (GraphEdge n)) (h : es.length=m) :
    List.ofFn (listEdges es h)=es := by
  subst m
  change List.ofFn es.get=es
  exact List.ofFn_get es

without_editor_info theorem neighborList_listEdges {n m : ℕ} (es : List (GraphEdge n)) (h : es.length=m)
    (i : Fin n) : neighborList (listEdges es h) i=es.flatMap (fun e => adjacencyEntry e i) := by
  rw [neighborList,ofFn_listEdges]

end CubicSpecial


namespace CubicSpecial

without_editor_info theorem sum_listEdges {n m : ℕ} {A : Type*} [AddCommMonoid A]
    (es : List (GraphEdge n)) (h : es.length=m) (f : GraphEdge n → A) :
    (∑ i, f (listEdges es h i))=(es.map f).sum := by
  rw [←List.sum_ofFn]
  change (List.ofFn (f ∘ listEdges es h)).sum=(es.map f).sum
  rw [←List.map_ofFn,ofFn_listEdges]

without_editor_info theorem listEdges_all {n m : ℕ} (es : List (GraphEdge n)) (h : es.length=m)
    (P : GraphEdge n → Prop) [DecidablePred P]
    (hc : es.all (fun e => decide (P e))=true) : ∀ i, P (listEdges es h i) := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp hc) _ (List.get_mem _ _))

section
variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]

without_editor_info theorem vectorGraph_listEdges {n m : ℕ} (es : List (GraphEdge n)) (h : es.length=m)
    (H C : Fin n → V) (B : V →ₗ[ZMod 3] V →ₗ[ZMod 3] ZMod 3) :
    vectorGraph (listEdges es h) H C B=
      (es.map (fun e => e.weight*B (H e.src) (H e.dst))).sum + ∑ i, B (H i) (C i) := by
  unfold vectorGraph
  rw [sum_listEdges es h (fun e => e.weight*B (H e.src) (H e.dst))]

without_editor_info theorem graphStar_listEdges {n m : ℕ} (es : List (GraphEdge n)) (h : es.length=m)
    (H C : Fin n → V) (i : Fin n) :
    graphStar (listEdges es h) H C i=C i + (es.map (fun e =>
      (if e.src=i then e.weight • H e.dst else 0) -
      (if e.dst=i then e.weight • H e.src else 0))).sum := by
  unfold graphStar
  rw [sum_listEdges es h (fun e => (if e.src=i then e.weight • H e.dst else 0) -
      (if e.dst=i then e.weight • H e.src else 0))]

end
end CubicSpecial


namespace CubicSpecial

without_editor_info theorem graphStar_coordinates {n m : ℕ} (edges : Fin m → GraphEdge n)
    (H C : Fin n → WildVector) (i : Fin n) :
    graphStar edges H C i = fun k => C i k + incidenceRow edges (fun j => H j k) i := by
  ext k
  simp only [graphStar, incidenceRow, Pi.add_apply, Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  split_ifs <;> simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

without_editor_info theorem graphStar_neighbors {n m : ℕ} (edges : Fin m → GraphEdge n)
    (neighbors : Fin n → List (Fin n × ℕ))
    (hn : ∀ i, neighbors i = neighborList edges i)
    (H C : Fin n → WildVector) (i : Fin n) :
    graphStar edges H C i = fun k => C i k + rowLog (neighbors i) (fun j => H j k) := by
  rw [graphStar_coordinates]
  funext k
  rw [hn i, neighborList_log]

end CubicSpecial

/- Source module: GraphCert.CubicBackend. -/
namespace GraphCert.Cubic
open CubicSpecial

/-- A finite local obstruction, with no equation-specific assumptions. -/
structure Certificate (f : ℤ → ℤ → ℤ) where
  vertices : ℕ
  edgeCount : ℕ
  edges : Fin edgeCount → GraphEdge vertices
  values : ℤ → ℤ → Fin vertices → Eisenstein
  constants : Fin vertices → Eisenstein
  support : Finset PrimaryPrime
  nonzero : ∀ x y, f x y = 0 → ∀ i, values x y i ≠ 0
  constantsNonzero : ∀ i, constants i ≠ 0
  outside : ∀ x y, f x y = 0 → ∀ π, π ∉ support →
    graphSum edges (values x y) constants (tameAt π) = 0
  localObstruction : ∀ x y, f x y = 0 →
    (∑ π ∈ support, graphSum edges (values x y) constants (tameAt π)) +
      graphSum edges (values x y) constants wild ≠ 0

theorem Certificate.sound {f : ℤ → ℤ → ℤ} (c : Certificate f) :
    ¬ ∃ x y, f x y = 0 := by
  rintro ⟨x, y, h⟩
  exact c.localObstruction x y h
    (graph_finite_prime_reduction c.edges (c.values x y) c.constants
      (c.nonzero x y h) c.constantsNonzero c.support (c.outside x y h))

/-- A cleared polynomial identity proves the required residue cube. -/
theorem residue_cube_of_identity (π : Eisenstein) [Fact (Prime π)]
    {A F H R Q D W : Eisenstein} (hF : F = 0) (hH : π ∣ H)
    (hD : ¬ π ∣ D) (hid : D^3 * A - W^3 = F * R + H * Q) :
    ∃ z : Residue π, reduction π A = z^3 := by
  have hd : reduction π D ≠ 0 := fun h => hD ((reduction_zero π D).mp h)
  have hh : reduction π H = 0 := (reduction_zero π H).mpr hH
  have he := congrArg (reduction π) hid
  simp only [map_sub, map_add, map_mul, map_pow, hF, map_zero, hh, zero_mul, add_zero] at he
  refine ⟨reduction π W / reduction π D, ?_⟩
  rw [div_pow, eq_div_iff (pow_ne_zero 3 hd)]
  linear_combination he

/-- An integral Bezout identity separates adjacent vertices away from its constant. -/
theorem separate_of_identity (π : Eisenstein) {F H K A B C D : Eisenstein}
    (hF : F = 0) (hD : ¬ π ∣ D) (hid : F*A + H*B + K*C = D) :
    ¬ (π ∣ H ∧ π ∣ K) := by
  rintro ⟨hH, hK⟩
  apply hD
  rw [← hid, hF, zero_mul, zero_add]
  exact dvd_add (dvd_mul_of_dvd_left hH _) (dvd_mul_of_dvd_left hK _)

/-- Divisibility of a fixed support power certifies all exceptional constants. -/
theorem not_dvd_of_support (π N A B : Eisenstein) [hπ : Fact (Prime π)]
    (k : ℕ) (hN : ¬ π ∣ N) (h : A*B = N^k) : ¬ π ∣ A := by
  intro ha
  exact hN (hπ.out.dvd_of_dvd_pow (h ▸ dvd_mul_of_dvd_left ha B))

theorem finite_relation {n m k : ℕ} (edges : Fin m → GraphEdge n)
    (H C : Fin n → Eisenstein) (hH : ∀ i, H i ≠ 0) (hC : ∀ i, C i ≠ 0)
    (primes : Fin k → PrimaryPrime) (hinj : Function.Injective primes)
    (N : Eisenstein) (hN : N = 3 * ∏ i, (primes i).val)
    (hout : ∀ π : PrimaryPrime, ¬ π.val ∣ N → graphSum edges H C (tameAt π) = 0) :
    (∑ i, graphSum edges H C (tameAt (primes i))) + graphSum edges H C wild = 0 := by
  classical
  have h := graph_finite_prime_reduction edges H C hH hC (Finset.univ.image primes) ?_
  · simpa only [Finset.sum_image (fun i _ j _ h => hinj h)] using h
  · intro π hπ
    apply hout π
    intro hd
    rw [hN] at hd
    have hd' : π.val ∣ ∏ i, (primes i).val :=
      (π.property.1.dvd_mul.mp hd).resolve_left (primaryPrime_ne_three π)
    obtain ⟨i, _, hi⟩ := (π.property.1.dvd_finsetProd_iff (fun i => (primes i).val)).mp hd'
    have he : π = primes i := Subtype.ext
      (primary_associated_eq π.property.2 (primes i).property.2
        (π.property.1.irreducible.associated_of_dvd (primes i).property.1.irreducible hi))
    exact hπ (he ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

theorem support_not_dvd [DecidableEq PrimaryPrime] {k : ℕ} (primes : Fin k → PrimaryPrime) (N : Eisenstein)
    (hN : N = 3 * ∏ i, (primes i).val) (π : PrimaryPrime)
    (hπ : π ∉ Finset.univ.image primes) : ¬ π.val ∣ N := by
  intro hd
  rw [hN] at hd
  have hd' : π.val ∣ ∏ i, (primes i).val :=
    (π.property.1.dvd_mul.mp hd).resolve_left (primaryPrime_ne_three π)
  obtain ⟨i, _, hi⟩ := (π.property.1.dvd_finsetProd_iff (fun i => (primes i).val)).mp hd'
  have he : π = primes i := Subtype.ext
    (primary_associated_eq π.property.2 (primes i).property.2
      (π.property.1.irreducible.associated_of_dvd (primes i).property.1.irreducible hi))
  exact hπ (he ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- The finite local checker works for arbitrary polynomial values. -/
theorem wild_cell {n m : ℕ} (edges : Fin m → GraphEdge n)
    (values : ℤ → ℤ → Fin n → Eisenstein) (constants : Fin n → Eisenstein)
    (real : Fin n → Bool)
    (hcongr : ∀ (M : ℕ) x y a b, (M : ℤ) ∣ x-a → (M : ℤ) ∣ y-b →
      ∀ i, (M : Eisenstein) ∣ values x y i-values a b i)
    (hreal : ∀ i, real i = true → ∀ x y, (values x y i).im = 0)
    (a b : ℤ) (k : ℕ) (E : Fin n → WildEnvelope) (cs : Fin n → WildVector)
    (val : ZMod 3)
    (hC : ∀ i, computeWildClass 32 (constants i) = some (cs i))
    (hcheck : ∀ i, wildEnvelopeCheck (E i) (residueE (3^k) (values a b i)) k (real i))
    (hlinear : ∀ i j, wildForm ((E i).directions j)
      (graphStar edges (fun i => (E i).base) cs i) = 0)
    (hcross : ∀ e j l, wildForm ((E (edges e).src).directions j)
      ((E (edges e).dst).directions l) = 0)
    (hval : vectorGraph edges (fun i => (E i).base) cs wildBilinear = val)
    {x y : ℤ} (hnonzero : ∀ i, values x y i ≠ 0)
    (hx : (3 : ℤ)^k ∣ x-a) (hy : (3 : ℤ)^k ∣ y-b) :
    graphSum edges (values x y) constants wild = val := by
  rw [wild_graph_envelopes edges (values x y) constants E cs ?_
    (fun i => computeWildClass_sound (hC i)) hlinear hcross]
  · exact hval
  · intro i
    apply wildEnvelopeCheck_residue_sound (E i) (values a b i) k _ (hcheck i) (hnonzero i)
    · simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        hcongr (3^k) x y a b (by simpa using hx) (by simpa using hy) i
    · intro hr
      exact ⟨hreal i hr x y, hreal i hr a b⟩

theorem inert_cell {n m : ℕ} (edges : Fin m → GraphEdge n)
    (values : ℤ → ℤ → Fin n → Eisenstein) (constants : Fin n → Eisenstein)
    (real : Fin n → Bool)
    (hcongr : ∀ (M : ℕ) x y a b, (M : ℤ) ∣ x-a → (M : ℤ) ∣ y-b →
      ∀ i, (M : Eisenstein) ∣ values x y i-values a b i)
    (hreal : ∀ i, real i = true → ∀ x y, (values x y i).im = 0)
    (p : ℕ) [Fact p.Prime] [Fact (Prime (p : Eisenstein))]
    (h3 : ¬ (p : Eisenstein) ∣ 3) (hmod : p % 3 = 2)
    (a b : ℤ) (k : ℕ) (E : Fin n → WildEnvelope)
    (cc cs : Fin n → TameCertificate) (val : ZMod 3)
    (hC : ∀ i, (cc i).check (p : Eisenstein) (constants i))
    (hcheck : ∀ i, inertEnvelopeCheck (E i) p
      (residueE (p^k) (values a b i)) k (real i) (cs i))
    (hlinear : ∀ i j, tameForm ((E i).directions j)
      (graphStar edges (fun i => (E i).base) (fun i => (cc i).vector) i) = 0)
    (hcross : ∀ e j l, tameForm ((E (edges e).src).directions j)
      ((E (edges e).dst).directions l) = 0)
    (hval : vectorGraph edges (fun i => (E i).base)
      (fun i => (cc i).vector) tameBilinear = val)
    {x y : ℤ} (hnonzero : ∀ i, values x y i ≠ 0)
    (hx : (p : ℤ)^k ∣ x-a) (hy : (p : ℤ)^k ∣ y-b) :
    graphSum edges (values x y) constants (tame (p : Eisenstein) h3) = val := by
  rw [tame_graph_envelopes edges (values x y) constants (p : Eisenstein) h3 E
    (fun i => (cc i).vector) ?_ (fun i => (cc i).vector_sound _ h3 (hC i)) hlinear hcross]
  · exact hval
  · intro i
    apply inertEnvelopeCheck_residue_sound (E i) p h3 hmod (values a b i) k _
      (cs i) (hcheck i) (hnonzero i)
    · simpa only [Nat.cast_pow] using
        hcongr (p^k) x y a b (by simpa using hx) (by simpa using hy) i
    · intro hr
      exact hreal i hr x y

end GraphCert.Cubic

/- Source module: GraphCert.CubicSplit. -/
namespace GraphCert.Cubic
open CubicSpecial

without_editor_info def jointEnvelopeFastCheck (E : WildEnvelope) (π ρ : Eisenstein) (p : ℕ) (r s : ℤ) (k : ℕ)
    (b : Eisenstein) (c d : TameCertificate) : Prop :=
  splitKnown π p r k b c ∧ splitKnown ρ p s k b d ∧
  if splitRepresentative p r k b=0 then
    if splitRepresentative p s k b=0 then ∀ e l f m : ZMod 3, E.contains ![e,l,f,m]
    else ∀ e l : ZMod 3, E.contains ![e,l,d.exponent,d.cubic.val]
  else if splitRepresentative p s k b=0 then
    ∀ f m : ZMod 3, E.contains ![c.exponent,c.cubic.val,f,m]
  else E.contains ![(c.exponent : ZMod 3),c.cubic.val,d.exponent,d.cubic.val]

without_editor_info instance (E : WildEnvelope) (π ρ : Eisenstein) (p : ℕ) (r s : ℤ) (k : ℕ)
    (b : Eisenstein) (c d : TameCertificate) : Decidable (jointEnvelopeFastCheck E π ρ p r s k b c d) := by
  unfold jointEnvelopeFastCheck
  infer_instance

without_editor_info theorem jointEnvelopeFastCheck_sound (E : WildEnvelope) (π ρ : Eisenstein) (p : ℕ) (r s : ℤ) (k : ℕ)
    (b : Eisenstein) (c d : TameCertificate) (h : jointEnvelopeFastCheck E π ρ p r s k b c d) :
    jointEnvelopeCheck E π ρ p r s k b c d := by
  refine ⟨h.1,h.2.1,?_⟩
  intro e l f m he hf
  have hh := h.2.2
  by_cases h0 : splitRepresentative p r k b=0 <;>
    by_cases h1 : splitRepresentative p s k b=0
  · simp only [if_pos h0,if_pos h1] at hh
    exact hh e l f m
  · simp only [if_pos h0,if_neg h1] at hh
    simp only [splitMatches,h1,false_or] at hf
    obtain ⟨rfl,rfl⟩ := hf
    exact hh e l
  · simp only [if_neg h0,if_pos h1] at hh
    simp only [splitMatches,h0,false_or] at he
    obtain ⟨rfl,rfl⟩ := he
    exact hh f m
  · simp only [if_neg h0,if_neg h1] at hh
    simp only [splitMatches,h0,false_or] at he
    simp only [splitMatches,h1,false_or] at hf
    obtain ⟨rfl,rfl⟩ := he
    obtain ⟨rfl,rfl⟩ := hf
    exact hh

without_editor_info theorem tameForm_zero_of_shortcheck (a b : WildVector)
    (h : a=0 ∨ b=0 ∨ tameForm a b=0) : tameForm a b=0 := by
  rcases h with h | h | h
  · simp [h,tameForm]
  · simp [h,tameForm]
  · exact h

without_editor_info def jointCertificate (c d : TameCertificate) : WildVector :=
  ![(c.exponent : ZMod 3),c.cubic.val,d.exponent,d.cubic.val]

theorem split_cell {n m : ℕ} (edges : Fin m → GraphEdge n)
    (values : ℤ → ℤ → Fin n → Eisenstein) (constants : Fin n → Eisenstein)
    (hcongr : ∀ (M : ℕ) x y a b, (M : ℤ) ∣ x-a → (M : ℤ) ∣ y-b →
      ∀ i, (M : Eisenstein) ∣ values x y i-values a b i)
    (π ρ : Eisenstein) [Fact (Prime π)] [Fact (Prime ρ)]
    (hπ : ¬ π ∣ 3) (hρ : ¬ ρ ∣ 3) (p : ℕ) (r s a b : ℤ) (k : ℕ)
    (hpi : π ∣ (p : Eisenstein)) (hrho : ρ ∣ (p : Eisenstein))
    (hr : π^k ∣ ω-(r : Eisenstein)) (hs : ρ^k ∣ ω-(s : Eisenstein))
    (E : Fin n → WildEnvelope) (cc dd cs ds : Fin n → TameCertificate) (val : ZMod 3)
    (hC : ∀ i, (cc i).check π (constants i)) (hD : ∀ i, (dd i).check ρ (constants i))
    (hcheck : ∀ i, jointEnvelopeCheck (E i) π ρ p r s k (values a b i) (cs i) (ds i))
    (hlinear : ∀ i j, tameForm ((E i).directions j)
      (graphStar edges (fun i => (E i).base) (fun i => jointCertificate (cc i) (dd i)) i)=0)
    (hcross : ∀ e j l, tameForm ((E (edges e).src).directions j) ((E (edges e).dst).directions l)=0)
    (hval : vectorGraph edges (fun i => (E i).base)
      (fun i => jointCertificate (cc i) (dd i)) tameBilinear=val)
    {x y : ℤ} (hx : (p : ℤ)^k ∣ x-a) (hy : (p : ℤ)^k ∣ y-b) :
    graphSum edges (values x y) constants (tame π hπ) +
      graphSum edges (values x y) constants (tame ρ hρ) = val := by
  rw [joint_graph_envelopes edges (values x y) constants π ρ hπ hρ E
    (fun i => jointCertificate (cc i) (dd i)) ?_ ?_ hlinear hcross]
  · exact hval
  · intro i
    apply jointEnvelopeCheck_sound (E i) π ρ hπ hρ p r s k (values a b i) (cs i) (ds i)
      (hcheck i) hpi hrho hr hs
    simpa only [Nat.cast_pow] using
      hcongr (p^k) x y a b (by simpa using hx) (by simpa using hy) i
  · intro i
    unfold jointTame jointCertificate
    rw [(cc i).sound π hπ (hC i), (dd i).sound ρ hρ (hD i)]
    rfl

end GraphCert.Cubic

/- Source module: GraphCert.CubicPolynomial. -/
namespace CubicSpecial.Dense

abbrev Poly := List Eisenstein

without_editor_info def add : Poly → Poly → Poly
  | [],b => b
  | a,[] => a
  | a::as,b::bs => (a+b)::add as bs

without_editor_info def scale (a : Eisenstein) (b : Poly) : Poly := b.map (a*·)
without_editor_info def neg (a : Poly) : Poly := scale (-1) a
without_editor_info def sub (a b : Poly) : Poly := add a (neg b)

without_editor_info def mul : Poly → Poly → Poly
  | [],_ => []
  | a::as,b => add (scale a b) (0::mul as b)

without_editor_info def pow (a : Poly) : ℕ → Poly
  | 0 => [1]
  | n+1 => mul (pow a n) a

without_editor_info def comp : Poly → Poly → Poly
  | [],_ => []
  | a::as,b => add [a] (mul b (comp as b))

without_editor_info def eval {R : Type*} [CommRing R] (f : Eisenstein →+* R) : Poly → R → R
  | [],_ => 0
  | a::as,t => f a+t*eval f as t

without_editor_info theorem eval_add {R : Type*} [CommRing R] (f : Eisenstein →+* R) (a b : Poly) (t : R) :
    eval f (add a b) t=eval f a t+eval f b t := by
  induction a generalizing b with
  | nil => simp [add,eval]
  | cons a as ih =>
    cases b with
    | nil => simp [add,eval]
    | cons b bs => simp only [add,eval,map_add,ih]; ring

without_editor_info theorem eval_scale {R : Type*} [CommRing R] (f : Eisenstein →+* R) (a : Eisenstein) (b : Poly) (t : R) :
    eval f (scale a b) t=f a*eval f b t := by
  induction b with
  | nil => simp [scale,eval]
  | cons b bs ih => simp only [scale,List.map_cons,eval,map_mul] at *; rw [ih]; ring

without_editor_info theorem eval_neg {R : Type*} [CommRing R] (f : Eisenstein →+* R) (a : Poly) (t : R) :
    eval f (neg a) t= -eval f a t := by simp [neg,eval_scale]

without_editor_info theorem eval_sub {R : Type*} [CommRing R] (f : Eisenstein →+* R) (a b : Poly) (t : R) :
    eval f (sub a b) t=eval f a t-eval f b t := by simp [sub,eval_add,eval_neg,sub_eq_add_neg]

without_editor_info theorem eval_mul {R : Type*} [CommRing R] (f : Eisenstein →+* R) (a b : Poly) (t : R) :
    eval f (mul a b) t=eval f a t*eval f b t := by
  induction a with
  | nil => simp [mul,eval]
  | cons a as ih => rw [mul,eval_add,eval_scale]; simp only [eval,map_zero,zero_add,ih]; ring

without_editor_info theorem eval_pow {R : Type*} [CommRing R] (f : Eisenstein →+* R) (a : Poly) (n : ℕ) (t : R) :
    eval f (pow a n) t=(eval f a t)^n := by
  induction n with
  | zero => simp [pow,eval]
  | succ n ih => rw [pow,eval_mul,ih,pow_succ]

without_editor_info theorem eval_comp {R : Type*} [CommRing R] (f : Eisenstein →+* R) (a b : Poly) (t : R) :
    eval f (comp a b) t=eval f a (eval f b t) := by
  induction a with
  | nil => rfl
  | cons a as ih => rw [comp,eval_add,eval_mul,ih]; simp [eval]

without_editor_info def equal (a b : Poly) : Bool := (sub a b).all (· == 0)

without_editor_info theorem eval_of_all_zero {R : Type*} [CommRing R] (f : Eisenstein →+* R) (a : Poly)
    (ha : a.all (· == 0)=true) (t : R) : eval f a t=0 := by
  induction a with
  | nil => rfl
  | cons a as ih =>
    simp only [List.all_cons,Bool.and_eq_true,beq_iff_eq] at ha
    simp only [eval,ha.1,map_zero,ih ha.2,mul_zero,add_zero]

without_editor_info theorem eval_equal {R : Type*} [CommRing R] (f : Eisenstein →+* R) (a b : Poly)
    (h : equal a b=true) (t : R) : eval f a t=eval f b t := by
  exact sub_eq_zero.mp ((eval_sub f a b t).symm.trans (eval_of_all_zero f _ h t))

without_editor_info def X : Poly := [0,1]
end CubicSpecial.Dense

namespace GraphCert.Cubic.Polynomial
open CubicSpecial
abbrev Poly := List Dense.Poly

def add : Poly → Poly → Poly
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => Dense.add a b :: add as bs

def scale (a : Dense.Poly) (b : Poly) : Poly := b.map (Dense.mul a)
def neg (a : Poly) : Poly := a.map Dense.neg
def sub (a b : Poly) : Poly := add a (neg b)

def mul : Poly → Poly → Poly
  | [], _ => []
  | a :: as, b => add (scale a b) ([] :: mul as b)

def pow (a : Poly) : ℕ → Poly
  | 0 => [[1]]
  | n+1 => mul (pow a n) a

def eval {R : Type*} [CommRing R] (f : Eisenstein →+* R) : Poly → R → R → R
  | [], _, _ => 0
  | a :: as, x, y => Dense.eval f a y + x * eval f as x y

theorem eval_add {R : Type*} [CommRing R] (f : Eisenstein →+* R)
    (a b : Poly) (x y : R) : eval f (add a b) x y = eval f a x y + eval f b x y := by
  induction a generalizing b with
  | nil => simp [add, eval]
  | cons a as ih =>
    cases b with
    | nil => simp [add, eval]
    | cons b bs => simp only [add, eval, Dense.eval_add, ih]; ring

theorem eval_scale {R : Type*} [CommRing R] (f : Eisenstein →+* R)
    (a : Dense.Poly) (b : Poly) (x y : R) :
    eval f (scale a b) x y = Dense.eval f a y * eval f b x y := by
  induction b with
  | nil => simp [scale, eval]
  | cons b bs ih => simp only [scale, List.map_cons, eval, Dense.eval_mul] at *; rw [ih]; ring

theorem eval_neg {R : Type*} [CommRing R] (f : Eisenstein →+* R)
    (a : Poly) (x y : R) : eval f (neg a) x y = -eval f a x y := by
  induction a with
  | nil => simp [neg, eval]
  | cons a as ih => simp only [neg, List.map_cons, eval, Dense.eval_neg] at *; rw [ih]; ring

theorem eval_sub {R : Type*} [CommRing R] (f : Eisenstein →+* R)
    (a b : Poly) (x y : R) : eval f (sub a b) x y = eval f a x y - eval f b x y := by
  simp [sub, eval_add, eval_neg, sub_eq_add_neg]

theorem eval_mul {R : Type*} [CommRing R] (f : Eisenstein →+* R)
    (a b : Poly) (x y : R) : eval f (mul a b) x y = eval f a x y * eval f b x y := by
  induction a with
  | nil => simp [mul, eval]
  | cons a as ih =>
    rw [mul, eval_add, eval_scale]
    simp only [eval, Dense.eval, zero_add, ih]
    ring

theorem eval_pow {R : Type*} [CommRing R] (f : Eisenstein →+* R)
    (a : Poly) (k : ℕ) (x y : R) : eval f (pow a k) x y = eval f a x y ^ k := by
  induction k with
  | zero => simp [pow, eval, Dense.eval]
  | succ k ih => rw [pow, eval_mul, ih, pow_succ]

def equal (a b : Poly) : Bool := (sub a b).all (fun row => Dense.equal row [])

theorem eval_zero {R : Type*} [CommRing R] (f : Eisenstein →+* R)
    (a : Poly) (h : a.all (fun row => Dense.equal row []) = true) (x y : R) :
    eval f a x y = 0 := by
  induction a with
  | nil => rfl
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [eval, Dense.eval_equal f a [] h.1 y, Dense.eval, ih h.2, mul_zero, add_zero]

theorem eval_equal {R : Type*} [CommRing R] (f : Eisenstein →+* R)
    (a b : Poly) (h : equal a b = true) (x y : R) : eval f a x y = eval f b x y := by
  exact sub_eq_zero.mp ((eval_sub f a b x y).symm.trans (eval_zero f _ h x y))

theorem eval_map {R S : Type*} [CommRing R] [CommRing S]
    (f : Eisenstein →+* R) (g : R →+* S) (p : Poly) (x y : R) :
    g (eval f p x y) = eval (g.comp f) p (g x) (g y) := by
  have hd (p : Dense.Poly) (t : R) : g (Dense.eval f p t) = Dense.eval (g.comp f) p (g t) := by
    induction p with
    | nil => simp [Dense.eval]
    | cons a as ih => simp [Dense.eval, ih]
  induction p with
  | nil => simp [eval]
  | cons a as ih => simp [eval, hd, ih]

def value (p : Poly) (x y : ℤ) : Eisenstein := eval (RingHom.id _) p x y

def constant (c : Eisenstein) : Poly := [[c]]

theorem eval_constant {R : Type*} [CommRing R] (f : Eisenstein →+* R)
    (c : Eisenstein) (x y : R) : eval f (constant c) x y = f c := by
  simp [constant, eval, Dense.eval]

def row {n : ℕ} (neighbors : List (Fin n × ℕ)) (H : Fin n → Poly) (c : Eisenstein) : Poly :=
  neighbors.foldr (fun jw acc => mul (pow (H jw.1) jw.2) acc) (constant c)

theorem eval_row {n : ℕ} (neighbors : List (Fin n × ℕ)) (H : Fin n → Poly)
    (c : Eisenstein) (x y : ℤ) : value (row neighbors H c) x y =
      rowProduct neighbors (fun i => value (H i) x y) c := by
  induction neighbors with
  | nil => simp [row, value, rowProduct, eval_constant]
  | cons jw js ih =>
    simpa only [row, List.foldr_cons, value, eval_mul, eval_pow, rowProduct] using
      congrArg (fun z => value (H jw.1) x y ^ jw.2 * z) ih

theorem identity_power {n : ℕ} (neighbors : List (Fin n × ℕ)) (H : Fin n → Poly)
    (c : Eisenstein) (F A B W : Poly) (i : Fin n) (D : Eisenstein)
    (exponent : ℕ)
    (h : equal (sub (mul (constant (D^exponent)) (row neighbors H c)) (pow W exponent))
      (add (mul F A) (mul (H i) B)) = true) (x y : ℤ) :
    D^exponent * rowProduct neighbors (fun i => value (H i) x y) c - value W x y ^ exponent =
      value F x y * value A x y + value (H i) x y * value B x y := by
  have h := eval_equal (RingHom.id Eisenstein) _ _ h (x : Eisenstein) (y : Eisenstein)
  simp only [eval_sub, eval_mul, eval_constant, RingHom.id_apply, eval_pow, eval_add] at h
  change D^exponent * value (row neighbors H c) x y - value W x y ^ exponent =
    value F x y * value A x y + value (H i) x y * value B x y at h
  simpa only [eval_row] using h

theorem identity {n : ℕ} (neighbors : List (Fin n × ℕ)) (H : Fin n → Poly)
    (c : Eisenstein) (F A B W : Poly) (i : Fin n) (D : Eisenstein)
    (h : equal (sub (mul (constant (D^3)) (row neighbors H c)) (pow W 3))
      (add (mul F A) (mul (H i) B)) = true) (x y : ℤ) :
    D^3 * rowProduct neighbors (fun i => value (H i) x y) c - value W x y ^ 3 =
      value F x y * value A x y + value (H i) x y * value B x y :=
  identity_power neighbors H c F A B W i D 3 h x y

theorem bezout (F H K A B C : Poly) (D : Eisenstein)
    (h : equal (add (add (mul F A) (mul H B)) (mul K C)) (constant D) = true)
    (x y : ℤ) : value F x y * value A x y + value H x y * value B x y +
      value K x y * value C x y = D := by
  have h := eval_equal (RingHom.id Eisenstein) _ _ h (x : Eisenstein) (y : Eisenstein)
  simpa only [eval_add, eval_mul, eval_constant, RingHom.id_apply, value] using h

theorem value_congr (p : Poly) (M : ℕ) {x y a b : ℤ}
    (hx : (M : ℤ) ∣ x-a) (hy : (M : ℤ) ∣ y-b) :
    (M : Eisenstein) ∣ value p x y - value p a b := by
  apply (coeffMod_zero M _).mp
  have hx' : (M : Eisenstein) ∣ (x : Eisenstein) - (a : Eisenstein) := by
    obtain ⟨q, hq⟩ := hx
    exact ⟨q, by exact_mod_cast hq⟩
  have hy' : (M : Eisenstein) ∣ (y : Eisenstein) - (b : Eisenstein) := by
    obtain ⟨q, hq⟩ := hy
    exact ⟨q, by exact_mod_cast hq⟩
  have ex := (coeffMod_zero M _).mpr hx'
  have ey := (coeffMod_zero M _).mpr hy'
  rw [map_sub, sub_eq_zero] at ex ey
  simp only [map_sub, value, eval_map, ex, ey, sub_self]

theorem nonzero_of_mod (F H : Poly) (M : ℕ)
    (check : ∀ x y : ZMod M,
      eval (coeffMod M) F ⟨x, 0⟩ ⟨y, 0⟩ = 0 →
      eval (coeffMod M) H ⟨x, 0⟩ ⟨y, 0⟩ ≠ 0)
    {x y : ℤ} (hF : value F x y = 0) : value H x y ≠ 0 := by
  intro hH
  have hF' := congrArg (coeffMod M) hF
  have hH' := congrArg (coeffMod M) hH
  simp only [value, eval_map, RingHom.comp_id, map_zero] at hF' hH'
  have hc (z : ℤ) : coeffMod M (z : Eisenstein) = ⟨(z : ZMod M), 0⟩ := by
    ext <;> simp [coeffMod]
  simp only [hc] at hF' hH'
  exact check (x : ZMod M) (y : ZMod M) hF' hH'

theorem real_congr (p : Poly) {M x y a b : ℤ}
    (hx : M ∣ x-a) (hy : M ∣ y-b) :
    M ∣ (value p x y).re - (value p a b).re := by
  have hx' : (M.natAbs : ℤ) ∣ x-a := by simpa only [Int.natCast_natAbs, abs_dvd] using hx
  have hy' : (M.natAbs : ℤ) ∣ y-b := by simpa only [Int.natCast_natAbs, abs_dvd] using hy
  have hd := value_congr p M.natAbs hx' hy'
  obtain ⟨q, hq⟩ := hd
  have hr := congrArg QuadraticAlgebra.re hq
  have hd' : (M.natAbs : ℤ) ∣ (value p x y).re - (value p a b).re := by
    refine ⟨q.re, ?_⟩
    simpa using hr
  rwa [Int.natCast_natAbs, abs_dvd] at hd'

end GraphCert.Cubic.Polynomial

/- Source module: GraphCert.LocalObstruction. -/
/-! A joint finite obstruction. Coordinates with different powers remain
in the same row throughout the check. Taking separate coordinate projections
would lose information and is intentionally not part of this interface. -/

namespace GraphCert

abbrev Signature {n : ℕ} (powers : Fin n → ℕ) := (i : Fin n) → ZMod (powers i)

def sumRows {A : Type*} [AddMonoid A] : List (List A) → List A
  | [] => [0]
  | row :: rows => row.flatMap fun a => (sumRows rows).map (a + ·)

theorem sum_mem_sumRows {A : Type*} [AddMonoid A]
    (values : List A) (rows : List (List A))
    (h : List.Forall₂ (fun value row => value ∈ row) values rows) :
    values.sum ∈ sumRows rows := by
  induction h with
  | nil => simp [sumRows]
  | @cons a row values rows ha _ ih =>
    exact List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨values.sum, ih, rfl⟩⟩

/-- Proof obligations connect finite tables to the actual arithmetic symbols.
The tables by themselves never establish an obstruction. -/
structure LocalObstruction (f : ℤ → ℤ → ℤ) (A : Type*) [AddMonoid A] where
  values : ℤ → ℤ → List A
  rows : List (List A)
  covers : ∀ x y, f x y = 0 →
    List.Forall₂ (fun value row => value ∈ row) (values x y) rows
  reciprocity : ∀ x y, f x y = 0 → (values x y).sum = 0
  excludesZero : (0 : A) ∉ sumRows rows

theorem LocalObstruction.sound {f : ℤ → ℤ → ℤ} {A : Type*} [AddMonoid A]
    (certificate : LocalObstruction f A) : ¬ ∃ x y, f x y = 0 := by
  rintro ⟨x, y, h⟩
  apply certificate.excludesZero
  rw [← certificate.reciprocity x y h]
  exact sum_mem_sumRows _ _ (certificate.covers x y h)

end GraphCert



set_option Elab.async false

open CubicSpecial

open GraphCert.Cubic

open GraphCert.Cubic.Polynomial

namespace GraphCert.Generated.g5786bb6f19cbbfc7842a018a.Proof

without_editor_info def F : Poly := [[⟨2,0⟩,⟨1,0⟩,⟨1,0⟩,⟨1,0⟩],[⟨1,0⟩],[],[],[⟨1,0⟩]]

without_editor_info def nodes : Fin 20 → Poly := ![[[⟨1,1⟩,⟨(-1),0⟩]],[[⟨(-1),(-1)⟩,⟨(-1),0⟩]],[[],[⟨1,0⟩]],[[⟨1,1⟩],[⟨1,0⟩]],[[⟨1,0⟩],[⟨1,0⟩]],[[⟨0,1⟩],[⟨1,0⟩]],[[⟨0,(-1)⟩],[⟨1,0⟩]],[[⟨(-1),(-1)⟩],[⟨1,0⟩]],[[⟨0,1⟩,⟨(-1),0⟩],[⟨1,0⟩]],[[⟨0,(-2)⟩,⟨0,(-1)⟩],[⟨1,0⟩]],[[⟨(-2),(-1)⟩,⟨(-1),0⟩],[⟨(-1),(-1)⟩],[⟨0,(-1)⟩]],[[⟨(-1),0⟩,⟨(-1),0⟩]],[[⟨1,0⟩,⟨1,0⟩],[⟨1,0⟩]],[[⟨0,0⟩,⟨(-1),0⟩],[⟨1,0⟩]],[[⟨(-2),(-1)⟩,⟨(-1),0⟩]],[[⟨(-1),0⟩,⟨(-1),0⟩],[⟨0,(-1)⟩]],[[⟨0,1⟩,⟨(-1),0⟩],[⟨(-1),(-1)⟩]],[[⟨1,0⟩,⟨1,0⟩,⟨1,0⟩],[⟨0,0⟩,⟨0,1⟩]],[[⟨0,(-1)⟩,⟨0,(-1)⟩,⟨1,0⟩],[⟨1,1⟩,⟨(-1),0⟩]],[[⟨1,0⟩,⟨0,0⟩,⟨1,0⟩],[⟨0,0⟩,⟨0,1⟩],[⟨(-1),(-1)⟩]]]

without_editor_info def constants : Fin 20 → Eisenstein := ![⟨4,0⟩,⟨(-4),(-4)⟩,⟨0,4⟩,⟨0,2⟩,⟨4,0⟩,⟨0,2⟩,⟨2,0⟩,⟨1,0⟩,⟨4,0⟩,⟨2,4⟩,⟨2,0⟩,⟨0,1⟩,⟨4,8⟩,⟨0,1⟩,⟨0,2⟩,⟨6,6⟩,⟨0,(-6)⟩,⟨1,0⟩,⟨(-1),(-1)⟩,⟨(-1),(-1)⟩]

without_editor_info def edgeList : List (GraphEdge 20) := [⟨0,8,1⟩,⟨0,13,1⟩,⟨0,16,1⟩,⟨0,17,2⟩,⟨1,2,2⟩,⟨1,4,1⟩,⟨1,5,2⟩,⟨1,6,1⟩,⟨1,10,2⟩,⟨1,12,1⟩,⟨1,13,2⟩,⟨1,15,2⟩,⟨1,17,2⟩,⟨2,9,2⟩,⟨2,14,2⟩,⟨2,18,2⟩,⟨2,19,2⟩,⟨3,9,2⟩,⟨3,10,2⟩,⟨3,11,1⟩,⟨3,12,1⟩,⟨3,16,1⟩,⟨3,18,1⟩,⟨4,10,2⟩,⟨4,12,1⟩,⟨4,14,2⟩,⟨4,19,2⟩,⟨5,8,2⟩,⟨5,11,2⟩,⟨5,12,2⟩,⟨5,18,2⟩,⟨5,19,2⟩,⟨6,8,2⟩,⟨6,9,2⟩,⟨6,10,1⟩,⟨6,18,2⟩,⟨6,19,2⟩,⟨7,11,1⟩,⟨7,17,1⟩,⟨8,9,1⟩,⟨8,16,2⟩,⟨8,17,2⟩,⟨9,12,2⟩,⟨9,14,2⟩,⟨9,15,2⟩,⟨10,11,1⟩,⟨10,13,2⟩,⟨10,17,2⟩,⟨11,16,2⟩,⟨12,15,2⟩,⟨13,15,1⟩,⟨13,18,1⟩,⟨13,19,1⟩,⟨14,15,1⟩,⟨15,17,1⟩,⟨15,18,2⟩,⟨16,19,1⟩,⟨18,19,2⟩]

without_editor_info def edges : Fin 58 → GraphEdge 20 := listEdges edgeList (by decide)

without_editor_info def neighbors : Fin 20 → List (Fin 20 × ℕ) := ![[(8,1),(13,1),(16,1),(17,2)],[(2,2),(4,1),(5,2),(6,1),(10,2),(12,1),(13,2),(15,2),(17,2)],[(1,1),(9,2),(14,2),(18,2),(19,2)],[(9,2),(10,2),(11,1),(12,1),(16,1),(18,1)],[(1,2),(10,2),(12,1),(14,2),(19,2)],[(1,1),(8,2),(11,2),(12,2),(18,2),(19,2)],[(1,2),(8,2),(9,2),(10,1),(18,2),(19,2)],[(11,1),(17,1)],[(0,2),(5,1),(6,1),(9,1),(16,2),(17,2)],[(2,1),(3,1),(6,1),(8,2),(12,2),(14,2),(15,2)],[(1,1),(3,1),(4,1),(6,2),(11,1),(13,2),(17,2)],[(3,2),(5,1),(7,2),(10,2),(16,2)],[(1,2),(3,2),(4,2),(5,1),(9,1),(15,2)],[(0,2),(1,1),(10,1),(15,1),(18,1),(19,1)],[(2,1),(4,1),(9,1),(15,1)],[(1,1),(9,1),(12,1),(13,2),(14,2),(17,1),(18,2)],[(0,2),(3,2),(8,1),(11,1),(19,1)],[(0,1),(1,1),(7,2),(8,1),(10,1),(15,2)],[(2,1),(3,2),(5,1),(6,1),(13,2),(15,1),(19,2)],[(2,1),(4,1),(5,1),(6,1),(13,2),(16,2),(18,1)]]

without_editor_info theorem adjacency_checked : ∀ i : Fin 20, neighbors i = neighborList edges i := by
  simp only [edges, neighborList_listEdges]
  decide +kernel

without_editor_info def equation (x y : ℤ) : ℤ := (value F x y).re

without_editor_info def values (x y : ℤ) (i : Fin 20) : Eisenstein := value (nodes i) x y

without_editor_info theorem curve_zero {x y : ℤ} (hf : equation x y = 0) : value F x y = 0 := by
  ext
  · exact hf
  · simp [value, eval, CubicSpecial.Dense.eval, F]

without_editor_info theorem equation_congr {M x y a b : ℤ} (hx : M ∣ x-a) (hy : M ∣ y-b) :
    M ∣ equation x y-equation a b := real_congr F hx hy

without_editor_info theorem values_congr (M : ℕ) (x y a b : ℤ) (hx : (M : ℤ) ∣ x-a) (hy : (M : ℤ) ∣ y-b) :
    ∀ i : Fin 20, (M : Eisenstein) ∣ values x y i-values a b i :=
  fun i => value_congr (nodes i) M hx hy

without_editor_info def real : Fin 20 → Bool := ![false,false,true,false,true,false,false,false,false,false,false,true,true,true,false,false,false,false,false,false]

without_editor_info theorem values_real (i : Fin 20) (h : real i = true) (x y : ℤ) : (values x y i).im = 0 := by
  fin_cases i <;> simp [real] at h <;> simp [values, value, eval, CubicSpecial.Dense.eval, nodes]

without_editor_info theorem nonzero_0 {x y : ℤ} (hf : equation x y = 0) : values x y 0 ≠ 0 :=
  nonzero_of_mod F (nodes 0) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_1 {x y : ℤ} (hf : equation x y = 0) : values x y 1 ≠ 0 :=
  nonzero_of_mod F (nodes 1) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_2 {x y : ℤ} (hf : equation x y = 0) : values x y 2 ≠ 0 :=
  nonzero_of_mod F (nodes 2) 3 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_3 {x y : ℤ} (hf : equation x y = 0) : values x y 3 ≠ 0 :=
  nonzero_of_mod F (nodes 3) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_4 {x y : ℤ} (hf : equation x y = 0) : values x y 4 ≠ 0 :=
  nonzero_of_mod F (nodes 4) 3 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_5 {x y : ℤ} (hf : equation x y = 0) : values x y 5 ≠ 0 :=
  nonzero_of_mod F (nodes 5) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_6 {x y : ℤ} (hf : equation x y = 0) : values x y 6 ≠ 0 :=
  nonzero_of_mod F (nodes 6) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_7 {x y : ℤ} (hf : equation x y = 0) : values x y 7 ≠ 0 :=
  nonzero_of_mod F (nodes 7) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_8 {x y : ℤ} (hf : equation x y = 0) : values x y 8 ≠ 0 :=
  nonzero_of_mod F (nodes 8) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_9 {x y : ℤ} (hf : equation x y = 0) : values x y 9 ≠ 0 :=
  nonzero_of_mod F (nodes 9) 3 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_10 {x y : ℤ} (hf : equation x y = 0) : values x y 10 ≠ 0 :=
  nonzero_of_mod F (nodes 10) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_11 {x y : ℤ} (hf : equation x y = 0) : values x y 11 ≠ 0 :=
  nonzero_of_mod F (nodes 11) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_12 {x y : ℤ} (hf : equation x y = 0) : values x y 12 ≠ 0 :=
  nonzero_of_mod F (nodes 12) 3 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_13 {x y : ℤ} (hf : equation x y = 0) : values x y 13 ≠ 0 :=
  nonzero_of_mod F (nodes 13) 3 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_14 {x y : ℤ} (hf : equation x y = 0) : values x y 14 ≠ 0 :=
  nonzero_of_mod F (nodes 14) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_15 {x y : ℤ} (hf : equation x y = 0) : values x y 15 ≠ 0 :=
  nonzero_of_mod F (nodes 15) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_16 {x y : ℤ} (hf : equation x y = 0) : values x y 16 ≠ 0 :=
  nonzero_of_mod F (nodes 16) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_17 {x y : ℤ} (hf : equation x y = 0) : values x y 17 ≠ 0 :=
  nonzero_of_mod F (nodes 17) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_18 {x y : ℤ} (hf : equation x y = 0) : values x y 18 ≠ 0 :=
  nonzero_of_mod F (nodes 18) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_19 {x y : ℤ} (hf : equation x y = 0) : values x y 19 ≠ 0 :=
  nonzero_of_mod F (nodes 19) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem all_nonzero {x y : ℤ} (hf : equation x y = 0) : ∀ i : Fin 20, values x y i ≠ 0 := by
  intro i
  fin_cases i
  · exact nonzero_0 hf
  · exact nonzero_1 hf
  · exact nonzero_2 hf
  · exact nonzero_3 hf
  · exact nonzero_4 hf
  · exact nonzero_5 hf
  · exact nonzero_6 hf
  · exact nonzero_7 hf
  · exact nonzero_8 hf
  · exact nonzero_9 hf
  · exact nonzero_10 hf
  · exact nonzero_11 hf
  · exact nonzero_12 hf
  · exact nonzero_13 hf
  · exact nonzero_14 hf
  · exact nonzero_15 hf
  · exact nonzero_16 hf
  · exact nonzero_17 hf
  · exact nonzero_18 hf
  · exact nonzero_19 hf

without_editor_info theorem constants_nonzero : ∀ i : Fin 20, constants i ≠ 0 := by decide +kernel

without_editor_info def root_0 : Poly := [[⟨4,0⟩],[],[],[⟨2,0⟩]]

without_editor_info def starA_0 : Poly := [[⟨0,0⟩,⟨8,0⟩,⟨8,(-4)⟩,⟨12,(-4)⟩],[⟨16,0⟩,⟨8,0⟩,⟨8,4⟩,⟨8,0⟩],[⟨(-40),0⟩],[],[],[⟨(-8),0⟩]]

without_editor_info def starB_0 : Poly := [[⟨0,64⟩,⟨68,80⟩,⟨104,52⟩,⟨92,20⟩,⟨60,(-4)⟩,⟨24,(-8)⟩,⟨4,0⟩],[⟨(-4),32⟩,⟨12,68⟩,⟨24,84⟩,⟨16,88⟩,⟨20,52⟩,⟨4,12⟩],[⟨4,(-64)⟩,⟨(-48),(-104)⟩,⟨(-64),(-100)⟩,⟨(-40),(-68)⟩,⟨(-16),(-28)⟩],[⟨(-4),56⟩,⟨48,68⟩,⟨52,40⟩,⟨28,16⟩]]

without_editor_info theorem star_0 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 0) (values x y) (constants 0) - value root_0 x y ^ 3 =
      value F x y * value starA_0 x y + values x y 0 * value starB_0 x y :=
  identity_power (neighbors 0) nodes (constants 0) F starA_0 starB_0 root_0 0 1 3 (by decide +kernel) x y

without_editor_info def root_1 : Poly := [[⟨(-4),(-4)⟩],[⟨(-4),(-4)⟩]]

without_editor_info def starA_1 : Poly := [[⟨(-160),(-64)⟩,⟨(-720),(-344)⟩,⟨(-1964),(-728)⟩,⟨(-3592),(-376)⟩,⟨(-4652),644⟩,⟨(-4408),2640⟩,⟨(-2948),3804⟩,⟨(-1496),4312⟩,⟨192,4064⟩,⟨876,2668⟩,⟨732,1504⟩,⟨548,696⟩,⟨232,168⟩,⟨32,12⟩],[⟨(-80),(-112)⟩,⟨(-256),(-520)⟩,⟨(-912),(-1412)⟩,⟨(-1856),(-2296)⟩,⟨(-3100),(-2980)⟩,⟨(-3284),(-2240)⟩,⟨(-2820),(-1672)⟩,⟨(-2152),(-868)⟩,⟨(-1128),(-200)⟩,⟨(-488),(-108)⟩,⟨(-204),(-32)⟩,⟨(-52),(-4)⟩,⟨(-4),(-4)⟩],[⟨0,(-72)⟩,⟨64,(-276)⟩,⟨(-132),(-772)⟩,⟨(-632),(-1420)⟩,⟨(-1836),(-1888)⟩,⟨(-2376),(-1260)⟩,⟨(-2292),(-396)⟩,⟨(-1480),468⟩,⟨(-592),804⟩,⟨(-28),648⟩,⟨140,292⟩,⟨44,40⟩,⟨0,(-4)⟩],[⟨56,(-4)⟩,⟨268,(-12)⟩,⟨560,(-232)⟩,⟨692,(-1008)⟩,⟨124,(-2044)⟩,⟨(-708),(-2716)⟩,⟨(-1408),(-2376)⟩,⟨(-1300),(-1464)⟩,⟨(-920),(-596)⟩,⟨(-360),4⟩,⟨(-4),100⟩,⟨16,20⟩],[⟨52,40⟩,⟨224,188⟩,⟨676,428⟩,⟨1244,424⟩,⟨1592,144⟩,⟨1176,(-640)⟩,⟨396,(-908)⟩,⟨(-96),(-868)⟩,⟨(-328),(-552)⟩,⟨(-200),(-156)⟩,⟨(-32),(-12)⟩],[⟨4,40⟩,⟨(-4),184⟩,⟨116,512⟩,⟨332,884⟩,⟨744,1116⟩,⟨712,716⟩,⟨508,380⟩,⟨220,68⟩,⟨48,(-4)⟩,⟨4,4⟩],[⟨(-20),8⟩,⟨(-76),8⟩,⟨(-108),(-4)⟩,⟨(-88),12⟩,⟨140,(-28)⟩,⟨144,(-208)⟩,⟨104,(-296)⟩,⟨(-88),(-248)⟩,⟨(-48),(-48)⟩,⟨0,4⟩],[⟨(-28),(-4)⟩,⟨(-52),16⟩,⟨(-40),100⟩,⟨124,376⟩,⟨400,520⟩,⟨512,500⟩,⟨416,148⟩,⟨48,(-76)⟩,⟨(-16),(-20)⟩],[⟨(-32),(-16)⟩,⟨(-80),(-24)⟩,⟨(-216),(-20)⟩,⟨(-256),176⟩,⟨(-200),292⟩,⟨32,452⟩,⟨192,216⟩,⟨40,12⟩],[⟨(-20),(-28)⟩,⟨(-44),(-92)⟩,⟨(-184),(-244)⟩,⟨(-288),(-280)⟩,⟨(-388),(-280)⟩,⟨(-220),0⟩,⟨(-8),36⟩],[⟨0,(-12)⟩,⟨44,(-16)⟩,⟨56,(-68)⟩,⟨84,(-88)⟩,⟨(-28),(-160)⟩,⟨(-44),(-36)⟩],[⟨4,0⟩,⟨32,24⟩,⟨44,36⟩,⟨80,52⟩,⟨28,(-12)⟩],[⟨0,0⟩,⟨0,8⟩,⟨(-12),8⟩,⟨4,20⟩],[⟨0,0⟩,⟨0,0⟩,⟨(-4),(-4)⟩]]

without_editor_info def starB_1 : Poly := [[⟨(-128),128⟩,⟨(-880),592⟩,⟨(-2456),1472⟩,⟨(-3360),4212⟩,⟨(-4372),7848⟩,⟨(-3028),11624⟩,⟨(-1108),14412⟩,⟨1300,15192⟩,⟨3692,13460⟩,⟨4056,10248⟩,⟨3804,6824⟩,⟨2804,3712⟩,⟨1492,1676⟩,⟨716,632⟩,⟨244,148⟩,⟨32,12⟩],[⟨(-288),(-160)⟩,⟨(-1336),(-312)⟩,⟨(-3872),(-1084)⟩,⟨(-5928),(-1248)⟩,⟨(-8296),(-348)⟩,⟨(-8180),368⟩,⟨(-7424),1224⟩,⟨(-5540),2040⟩,⟨(-3156),1624⟩,⟨(-1912),1132⟩,⟨(-868),664⟩,⟨(-316),192⟩,⟨(-176),28⟩,⟨(-56),(-4)⟩,⟨(-4),(-4)⟩],[⟨(-256),(-368)⟩,⟨(-776),(-904)⟩,⟨(-2412),(-2076)⟩,⟨(-4256),(-3472)⟩,⟨(-5980),(-2720)⟩,⟨(-6548),(-1776)⟩,⟨(-5808),84⟩,⟨(-4064),1960⟩,⟨(-2064),2500⟩,⟨(-576),2356⟩,⟨80,1556⟩,⟨260,788⟩,⟨180,288⟩,⟨40,36⟩,⟨0,(-4)⟩],[⟨(-80),(-256)⟩,⟨(-24),(-760)⟩,⟨(-348),(-1720)⟩,⟨(-1552),(-3732)⟩,⟨(-2756),(-4760)⟩,⟨(-4328),(-5520)⟩,⟨(-4692),(-4932)⟩,⟨(-4328),(-3580)⟩,⟨(-3308),(-2040)⟩,⟨(-1768),(-728)⟩,⟨(-848),(-152)⟩,⟨(-260),104⟩,⟨16,104⟩,⟨16,20⟩]]

without_editor_info theorem star_1 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 1) (values x y) (constants 1) - value root_1 x y ^ 3 =
      value F x y * value starA_1 x y + values x y 1 * value starB_1 x y :=
  identity_power (neighbors 1) nodes (constants 1) F starA_1 starB_1 root_1 1 1 3 (by decide +kernel) x y

without_editor_info def root_2 : Poly := [[⟨0,0⟩,⟨0,(-2)⟩,⟨2,0⟩]]

without_editor_info def starA_2 : Poly := [[⟨(-24),0⟩,⟨(-76),40⟩,⟨(-156),92⟩,⟨(-284),144⟩,⟨(-356),196⟩,⟨(-412),140⟩,⟨(-360),68⟩,⟨(-228),8⟩,⟨(-108),(-12)⟩,⟨(-32),(-4)⟩,⟨(-4),0⟩],[⟨240,60⟩,⟨836,148⟩,⟨1520,228⟩,⟨1756,668⟩,⟨1944,1308⟩,⟨1364,1044⟩,⟨552,688⟩,⟨248,360⟩,⟨64,64⟩],[⟨(-12),132⟩,⟨92,448⟩,⟨0,440⟩,⟨(-392),312⟩,⟨(-360),252⟩,⟨(-276),(-28)⟩,⟨(-192),(-64)⟩,⟨(-40),0⟩],[⟨(-72),(-48)⟩,⟨(-104),(-40)⟩,⟨(-72),(-128)⟩,⟨(-104),(-168)⟩,⟨(-8),(-64)⟩,⟨24,(-40)⟩,⟨0,(-16)⟩],[⟨0,(-12)⟩,⟨4,(-4)⟩,⟨24,4⟩,⟨12,4⟩,⟨8,12⟩,⟨4,4⟩]]

without_editor_info def starB_2 : Poly := [[⟨(-504),(-264)⟩,⟨(-2132),(-964)⟩,⟨(-4608),(-2204)⟩,⟨(-7120),(-4772)⟩,⟨(-9284),(-7912)⟩,⟨(-9168),(-9320)⟩,⟨(-7096),(-9120)⟩,⟨(-4728),(-7352)⟩,⟨(-2344),(-4496)⟩,⟨(-776),(-2204)⟩,⟨(-220),(-824)⟩,⟨(-40),(-176)⟩,⟨0,(-16)⟩],[⟨24,(-192)⟩,⟨44,(-668)⟩,⟨1168,(-380)⟩,⟨3712,76⟩,⟨5700,856⟩,⟨7080,2580⟩,⟨6836,3484⟩,⟨4824,3180⟩,⟨2568,2192⟩,⟨1036,1064⟩,⟨288,312⟩,⟨40,40⟩],[⟨(-12),132⟩,⟨(-292),568⟩,⟨(-776),1768⟩,⟨(-1536),2936⟩,⟨(-2680),3236⟩,⟨(-3612),2340⟩,⟨(-3584),1104⟩,⟨(-2456),176⟩,⟨(-1296),(-224)⟩,⟨(-456),(-96)⟩,⟨(-64),0⟩],[⟨(-132),(-264)⟩,⟨(-732),(-1128)⟩,⟨(-1576),(-2600)⟩,⟨(-2172),(-3976)⟩,⟨(-1492),(-4280)⟩,⟨(-536),(-3832)⟩,⟨84,(-2324)⟩,⟨460,(-928)⟩,⟨236,(-344)⟩,⟨32,(-72)⟩,⟨4,0⟩]]

without_editor_info theorem star_2 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 2) (values x y) (constants 2) - value root_2 x y ^ 3 =
      value F x y * value starA_2 x y + values x y 2 * value starB_2 x y :=
  identity_power (neighbors 2) nodes (constants 2) F starA_2 starB_2 root_2 2 1 3 (by decide +kernel) x y

without_editor_info def root_3 : Poly := [[⟨(-8),(-4)⟩,⟨(-4),(-6)⟩,⟨2,0⟩]]

without_editor_info def starA_3 : Poly := [[⟨(-334),(-172)⟩,⟨(-926),(-862)⟩,⟨(-624),(-1224)⟩,⟨104,(-672)⟩,⟨228,(-150)⟩,⟨76,(-12)⟩,⟨8,0⟩],[⟨(-240),(-218)⟩,⟨(-518),(-588)⟩,⟨(-356),(-640)⟩,⟨(-62),(-410)⟩,⟨24,(-186)⟩,⟨8,(-52)⟩,⟨0,(-6)⟩],[⟨(-20),(-136)⟩,⟨44,(-234)⟩,⟨170,(-76)⟩,⟨158,44⟩,⟨60,24⟩,⟨8,2⟩],[⟨48,(-10)⟩,⟨98,28⟩,⟨64,76⟩,⟨16,46⟩,⟨2,8⟩],[⟨16,14⟩,⟨10,22⟩,⟨(-12),8⟩,⟨(-6),0⟩],[⟨0,2⟩,⟨(-2),0⟩,⟨(-2),(-2)⟩]]

without_editor_info def starB_3 : Poly := [[⟨704,(-156)⟩,⟨2344,438⟩,⟨2796,1136⟩,⟨2568,946⟩,⟨2690,1166⟩,⟨1966,1456⟩,⟨784,1006⟩,⟨156,382⟩,⟨12,76⟩,⟨0,6⟩],[⟨772,574⟩,⟨1882,1588⟩,⟨2412,2106⟩,⟨2504,2528⟩,⟨1678,2410⟩,⟨472,1326⟩,⟨(-50),374⟩,⟨(-54),48⟩,⟨(-8),2⟩],[⟨98,416⟩,⟨392,1122⟩,⟨614,1786⟩,⟨106,1826⟩,⟨(-512),986⟩,⟨(-454),216⟩,⟨(-150),(-6)⟩,⟨(-18),(-6)⟩],[⟨(-6),170⟩,⟨(-60),712⟩,⟨(-618),784⟩,⟨(-1090),64⟩,⟨(-778),(-338)⟩,⟨(-268),(-198)⟩,⟨(-42),(-40)⟩,⟨(-2),(-2)⟩]]

without_editor_info theorem star_3 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 3) (values x y) (constants 3) - value root_3 x y ^ 3 =
      value F x y * value starA_3 x y + values x y 3 * value starB_3 x y :=
  identity_power (neighbors 3) nodes (constants 3) F starA_3 starB_3 root_3 3 1 3 (by decide +kernel) x y

without_editor_info def root_4 : Poly := [[⟨2,2⟩,⟨2,2⟩,⟨2,2⟩]]

without_editor_info def starA_4 : Poly := [[⟨(-44),(-60)⟩,⟨(-284),(-204)⟩,⟨(-732),(-244)⟩,⟨(-980),244⟩,⟨(-336),1064⟩,⟨440,1040⟩,⟨412,384⟩,⟨112,36⟩,⟨8,(-4)⟩],[⟨(-36),(-84)⟩,⟨(-272),(-376)⟩,⟨(-996),(-872)⟩,⟨(-1852),(-616)⟩,⟨(-1200),740⟩,⟨140,1128⟩,⟨364,424⟩,⟨92,32⟩,⟨4,(-4)⟩],[⟨48,12⟩,⟨220,(-100)⟩,⟨8,(-760)⟩,⟨(-868),(-1192)⟩,⟨(-984),(-480)⟩,⟨(-316),128⟩,⟨0,100⟩,⟨8,12⟩],[⟨36,60⟩,⟨280,176⟩,⟨436,(-72)⟩,⟨56,(-456)⟩,⟨(-212),(-312)⟩,⟨(-96),(-48)⟩,⟨(-8),4⟩],[⟨(-12),24⟩,⟨68,136⟩,⟨196,136⟩,⟨124,(-8)⟩,⟨12,(-40)⟩,⟨(-4),(-8)⟩],[⟨(-12),0⟩,⟨(-8),32⟩,⟨28,48⟩,⟨24,16⟩,⟨4,0⟩]]

without_editor_info def starB_4 : Poly := [[⟨60,84⟩,⟨432,384⟩,⟨1432,764⟩,⟨2532,240⟩,⟨2144,(-1396)⟩,⟨860,(-2288)⟩,⟨40,(-2216)⟩,⟨(-584),(-1844)⟩,⟨(-756),(-1008)⟩,⟨(-380),(-252)⟩,⟨(-76),(-8)⟩,⟨(-4),4⟩],[⟨(-4),60⟩,⟨144,440⟩,⟨1096,1288⟩,⟨2400,1184⟩,⟨2012,(-308)⟩,⟨740,(-988)⟩,⟨232,(-688)⟩,⟨48,(-460)⟩,⟨(-88),(-256)⟩,⟨(-56),(-64)⟩,⟨(-8),(-4)⟩],[⟨(-56),(-12)⟩,⟨(-176),216⟩,⟨328,1072⟩,⟨1504,1576⟩,⟨1928,868⟩,⟨1256,(-124)⟩,⟨392,(-516)⟩,⟨(-44),(-356)⟩,⟨(-68),(-100)⟩,⟨(-12),(-8)⟩],[⟨(-64),(-36)⟩,⟨(-296),16⟩,⟨(-356),524⟩,⟨172,1308⟩,⟨1032,1628⟩,⟨1300,948⟩,⟨656,60⟩,⟨96,(-148)⟩,⟨(-16),(-48)⟩,⟨(-4),(-4)⟩]]

without_editor_info theorem star_4 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 4) (values x y) (constants 4) - value root_4 x y ^ 3 =
      value F x y * value starA_4 x y + values x y 4 * value starB_4 x y :=
  identity_power (neighbors 4) nodes (constants 4) F starA_4 starB_4 root_4 4 1 3 (by decide +kernel) x y

without_editor_info def root_5 : Poly := [[⟨(-2),(-2)⟩,⟨(-2),0⟩]]

without_editor_info def starA_5 : Poly := [[⟨(-6),4⟩,⟨(-6),24⟩,⟨(-122),(-16)⟩,⟨(-392),(-146)⟩,⟨(-618),(-372)⟩,⟨(-702),(-652)⟩,⟨(-582),(-784)⟩,⟨(-344),(-672)⟩,⟨(-110),(-416)⟩,⟨10,(-188)⟩,⟨14,(-58)⟩,⟨2,(-10)⟩,⟨0,(-2)⟩],[⟨4,0⟩,⟨28,(-24)⟩,⟨146,50⟩,⟨354,256⟩,⟨496,490⟩,⟨490,694⟩,⟨326,696⟩,⟨88,510⟩,⟨(-64),252⟩,⟨(-84),52⟩,⟨(-32),0⟩],[⟨4,6⟩,⟨(-12),8⟩,⟨(-18),58⟩,⟨(-70),116⟩,⟨(-222),86⟩,⟨(-334),(-38)⟩,⟨(-326),(-188)⟩,⟨(-184),(-186)⟩,⟨(-42),(-90)⟩,⟨(-4),(-28)⟩],[⟨(-2),(-2)⟩,⟨(-34),(-28)⟩,⟨(-54),(-96)⟩,⟨(-32),(-170)⟩,⟨36,(-158)⟩,⟨118,(-74)⟩,⟨104,(-12)⟩,⟨56,20⟩,⟨24,16⟩],[⟨4,0⟩,⟨12,12⟩,⟨26,18⟩,⟨30,16⟩,⟨28,34⟩,⟨26,38⟩,⟨2,20⟩,⟨(-8),6⟩],[⟨0,0⟩,⟨4,12⟩,⟨0,20⟩,⟨(-20),8⟩,⟨(-28),(-4)⟩,⟨(-16),(-12)⟩,⟨(-4),(-8)⟩],[⟨(-2),(-2)⟩,⟨(-2),(-4)⟩,⟨2,(-4)⟩,⟨4,(-2)⟩,⟨4,2⟩,⟨2,2⟩]]

without_editor_info def starB_5 : Poly := [[⟨(-10),(-4)⟩,⟨(-30),(-16)⟩,⟨(-186),(-262)⟩,⟨(-464),(-850)⟩,⟨(-502),(-1548)⟩,⟨(-102),(-2116)⟩,⟨632,(-2210)⟩,⟨1372,(-1734)⟩,⟨1782,(-944)⟩,⟨1696,(-230)⟩,⟨1206,142⟩,⟨666,234⟩,⟨278,162⟩,⟨66,56⟩,⟨4,8⟩],[⟨(-8),(-8)⟩,⟨56,24⟩,⟨170,16⟩,⟨324,18⟩,⟨654,328⟩,⟨992,940⟩,⟨1064,1534⟩,⟨666,1700⟩,⟨116,1440⟩,⟨(-220),912⟩,⟨(-346),360⟩,⟨(-248),68⟩,⟨(-86),(-6)⟩,⟨(-14),(-6)⟩],[⟨(-4),0⟩,⟨6,28⟩,⟨(-44),116⟩,⟨(-298),76⟩,⟨(-818),(-234)⟩,⟨(-1354),(-676)⟩,⟨(-1510),(-1122)⟩,⟨(-1320),(-1406)⟩,⟨(-854),(-1248)⟩,⟨(-308),(-782)⟩,⟨(-32),(-350)⟩,⟨22,(-100)⟩,⟨10,(-14)⟩],[⟨(-2),(-4)⟩,⟨(-22),(-56)⟩,⟨(-18),(-86)⟩,⟨96,(-162)⟩,⟨270,(-316)⟩,⟨544,(-246)⟩,⟨854,50⟩,⟨890,318⟩,⟨622,398⟩,⟨314,296⟩,⟨110,144⟩,⟨22,38⟩,⟨0,2⟩]]

without_editor_info theorem star_5 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 5) (values x y) (constants 5) - value root_5 x y ^ 3 =
      value F x y * value starA_5 x y + values x y 5 * value starB_5 x y :=
  identity_power (neighbors 5) nodes (constants 5) F starA_5 starB_5 root_5 5 1 3 (by decide +kernel) x y

without_editor_info def root_6 : Poly := [[⟨8,2⟩,⟨4,4⟩,⟨2,2⟩]]

without_editor_info def starA_6 : Poly := [[⟨(-138),94⟩,⟨(-382),(-120)⟩,⟨(-176),66⟩,⟨(-170),360⟩,⟨(-404),1134⟩,⟨(-706),1212⟩,⟨(-1178),808⟩,⟨(-1028),492⟩,⟨(-652),274⟩,⟨(-328),114⟩,⟨(-164),54⟩,⟨(-28),30⟩,⟨2,2⟩],[⟨(-48),(-16)⟩,⟨(-304),(-106)⟩,⟨(-738),(-288)⟩,⟨(-1620),(-1126)⟩,⟨(-2682),(-1762)⟩,⟨(-2870),(-2114)⟩,⟨(-2730),(-2220)⟩,⟨(-2202),(-1908)⟩,⟨(-1436),(-1194)⟩,⟨(-658),(-672)⟩,⟨(-318),(-318)⟩,⟨(-72),(-48)⟩],[⟨18,(-30)⟩,⟨64,(-130)⟩,⟨400,(-234)⟩,⟨726,(-652)⟩,⟨1088,(-828)⟩,⟨1272,(-896)⟩,⟨1458,(-448)⟩,⟨1202,(-354)⟩,⟨660,(-28)⟩,⟨408,78⟩,⟨84,(-18)⟩],[⟨22,32⟩,⟨88,190⟩,⟨358,584⟩,⟨594,1070⟩,⟨848,1476⟩,⟨430,1326⟩,⟨288,1314⟩,⟨74,608⟩,⟨(-134),258⟩,⟨0,108⟩],[⟨(-32),(-18)⟩,⟨(-174),(-66)⟩,⟨(-434),(-192)⟩,⟨(-742),(-276)⟩,⟨(-654),(-404)⟩,⟨(-780),(-676)⟩,⟨(-416),(-340)⟩,⟨(-134),(-272)⟩,⟨(-84),(-102)⟩],[⟨14,(-12)⟩,⟨60,(-56)⟩,⟨88,(-182)⟩,⟨104,(-124)⟩,⟨318,(-8)⟩,⟨168,(-60)⟩,⟨130,88⟩,⟨72,24⟩],[⟨4,16⟩,⟨46,72⟩,⟨50,56⟩,⟨(-20),84⟩,⟨28,94⟩,⟨(-36),2⟩,⟨(-18),18⟩],[⟨(-10),(-6)⟩,⟨(-12),4⟩,⟨(-8),(-16)⟩,⟨(-28),(-20)⟩,⟨2,(-4)⟩,⟨(-4),(-12)⟩],[⟨0,(-2)⟩,⟨0,0⟩,⟨4,0⟩,⟨0,0⟩,⟨2,2⟩]]

without_editor_info def starB_6 : Poly := [[⟨344,(-140)⟩,⟨1180,558⟩,⟨1814,922⟩,⟨2902,1572⟩,⟨5482,2420⟩,⟨7918,3466⟩,⟨10044,5356⟩,⟨10584,6306⟩,⟨9050,6108⟩,⟨6562,5052⟩,⟨4036,3376⟩,⟨2022,1776⟩,⟨824,768⟩,⟨298,272⟩,⟨60,44⟩],[⟨(-204),(-102)⟩,⟨(-56),(-118)⟩,⟨30,272⟩,⟨(-272),1706⟩,⟨(-806),2976⟩,⟨(-2718),3264⟩,⟨(-4172),2888⟩,⟨(-4984),1658⟩,⟨(-4464),442⟩,⟨(-3350),(-286)⟩,⟨(-1888),(-240)⟩,⟨(-832),(-178)⟩,⟨(-362),(-88)⟩,⟨(-78),4⟩,⟨(-2),0⟩],[⟨36,178⟩,⟨(-356),(-76)⟩,⟨(-962),(-1114)⟩,⟨(-1294),(-2246)⟩,⟨(-1184),(-3574)⟩,⟨(-514),(-4050)⟩,⟨312,(-4164)⟩,⟨808,(-3106)⟩,⟨1222,(-1892)⟩,⟨754,(-1178)⟩,⟨390,(-484)⟩,⟨214,(-220)⟩,⟨38,(-96)⟩,⟨4,(-8)⟩],[⟨172,(-46)⟩,⟨632,414⟩,⟨904,930⟩,⟨1396,1576⟩,⟨1562,2176⟩,⟨2134,3174⟩,⟨1842,3040⟩,⟨1172,2716⟩,⟨822,1944⟩,⟨386,1014⟩,⟨154,510⟩,⟨82,204⟩,⟨16,34⟩]]

without_editor_info theorem star_6 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 6) (values x y) (constants 6) - value root_6 x y ^ 3 =
      value F x y * value starA_6 x y + values x y 6 * value starB_6 x y :=
  identity_power (neighbors 6) nodes (constants 6) F starA_6 starB_6 root_6 6 1 3 (by decide +kernel) x y

without_editor_info def root_7 : Poly := [[⟨1,0⟩]]

without_editor_info def starA_7 : Poly := [[⟨(-1),0⟩]]

without_editor_info def starB_7 : Poly := [[⟨0,0⟩,⟨0,(-1)⟩,⟨0,(-1)⟩],[⟨0,1⟩],[⟨1,1⟩],[⟨1,0⟩]]

without_editor_info theorem star_7 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 7) (values x y) (constants 7) - value root_7 x y ^ 3 =
      value F x y * value starA_7 x y + values x y 7 * value starB_7 x y :=
  identity_power (neighbors 7) nodes (constants 7) F starA_7 starB_7 root_7 7 1 3 (by decide +kernel) x y

without_editor_info def root_8 : Poly := [[],[⟨4,2⟩],[⟨(-2),(-4)⟩],[⟨(-2),2⟩]]

without_editor_info def starA_8 : Poly := [[⟨(-104),0⟩,⟨(-200),(-72)⟩,⟨(-388),(-228)⟩,⟨(-400),(-456)⟩,⟨(-152),(-480)⟩,⟨184,(-156)⟩,⟨172,64⟩,⟨28,40⟩],[⟨188,164⟩,⟨8,8⟩,⟨68,(-4)⟩,⟨176,96⟩,⟨116,152⟩,⟨(-16),80⟩,⟨(-36),(-8)⟩],[⟨(-144),(-288)⟩,⟨8,0⟩,⟨24,24⟩,⟨(-4),36⟩,⟨(-40),(-8)⟩,⟨(-8),(-20)⟩],[⟨(-144),144⟩,⟨0,0⟩,⟨0,4⟩,⟨(-8),(-8)⟩,⟨4,0⟩],[⟨144,72⟩],[⟨(-24),(-48)⟩]]

without_editor_info def starB_8 : Poly := [[⟨(-216),(-216)⟩,⟨(-364),(-324)⟩,⟨(-464),(-748)⟩,⟨(-444),(-1004)⟩,⟨16,(-728)⟩,⟨244,(-440)⟩,⟨256,(-172)⟩,⟨284,28⟩,⟨156,92⟩,⟨28,40⟩],[⟨(-40),52⟩,⟨36,(-272)⟩,⟨128,(-364)⟩,⟨404,(-76)⟩,⟨472,92⟩,⟨272,212⟩,⟨184,192⟩,⟨60,104⟩,⟨(-8),32⟩],[⟨220,(-124)⟩,⟨80,(-268)⟩,⟨176,(-28)⟩,⟨160,4⟩,⟨12,24⟩,⟨112,72⟩,⟨72,72⟩,⟨(-4),32⟩,⟨0,4⟩],[⟨(-120),(-208)⟩,⟨(-12),0⟩,⟨60,16⟩,⟨116,96⟩,⟨236,240⟩,⟨64,184⟩,⟨(-52),48⟩,⟨(-20),(-4)⟩]]

without_editor_info theorem star_8 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 8) (values x y) (constants 8) - value root_8 x y ^ 3 =
      value F x y * value starA_8 x y + values x y 8 * value starB_8 x y :=
  identity_power (neighbors 8) nodes (constants 8) F starA_8 starB_8 root_8 8 1 3 (by decide +kernel) x y

without_editor_info def root_9 : Poly := [[⟨(-12),(-6)⟩,⟨(-24),(-12)⟩,⟨(-16),(-8)⟩,⟨(-4),(-2)⟩]]

without_editor_info def starA_9 : Poly := [[⟨42,(-24)⟩,⟨246,(-78)⟩,⟨358,(-226)⟩,⟨210,(-330)⟩,⟨16,(-292)⟩,⟨(-58),(-164)⟩,⟨(-34),(-50)⟩,⟨(-6),(-6)⟩],[⟨(-12),(-6)⟩,⟨12,30⟩,⟨52,44⟩,⟨82,20⟩,⟨66,(-30)⟩,⟨14,(-38)⟩,⟨(-2),(-10)⟩],[⟨12,6⟩,⟨36,12⟩,⟨56,76⟩,⟨100,128⟩,⟨74,64⟩,⟨16,8⟩],[⟨12,6⟩,⟨(-24),(-36)⟩,⟨(-76),(-32)⟩,⟨(-36),12⟩,⟨(-2),8⟩],[⟨12,6⟩,⟨0,(-24)⟩,⟨(-22),(-26)⟩,⟨(-8),(-4)⟩],[⟨12,6⟩,⟨12,0⟩,⟨2,(-2)⟩]]

without_editor_info def starB_9 : Poly := [[⟨(-390),282⟩,⟨(-2106),1536⟩,⟨(-4910),3914⟩,⟨(-6672),5610⟩,⟨(-5904),4980⟩,⟨(-3486),2892⟩,⟨(-1354),1108⟩,⟨(-330),282⟩,⟨(-40),52⟩,⟨0,6⟩],[⟨312,192⟩,⟨1536,864⟩,⟨3370,1886⟩,⟨4124,2320⟩,⟨3066,1776⟩,⟨1424,850⟩,⟨372,222⟩,⟨34,26⟩,⟨(-2),2⟩],[⟨(-60),(-156)⟩,⟨(-318),(-714)⟩,⟨(-592),(-1394)⟩,⟨(-662),(-1522)⟩,⟨(-436),(-956)⟩,⟨(-152),(-364)⟩,⟨(-34),(-92)⟩,⟨(-6),(-12)⟩],[⟨(-54),18⟩,⟨(-186),168⟩,⟨(-246),294⟩,⟨(-228),246⟩,⟨(-126),150⟩,⟨(-40),58⟩,⟨(-12),12⟩,⟨(-2),2⟩]]

without_editor_info theorem star_9 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 9) (values x y) (constants 9) - value root_9 x y ^ 3 =
      value F x y * value starA_9 x y + values x y 9 * value starB_9 x y :=
  identity_power (neighbors 9) nodes (constants 9) F starA_9 starB_9 root_9 9 1 3 (by decide +kernel) x y

without_editor_info def root_10 : Poly := [[⟨(-2),(-2)⟩],[⟨(-2),(-2)⟩],[⟨0,(-4)⟩],[⟨0,(-2)⟩],[⟨2,0⟩]]

without_editor_info def starA_10 : Poly := [[⟨(-412),(-180)⟩,⟨(-144),(-106)⟩,⟨42,(-60)⟩,⟨(-70),(-52)⟩,⟨(-64),(-58)⟩,⟨(-40),(-76)⟩,⟨(-42),(-42)⟩,⟨(-14),(-6)⟩],[⟨(-302),(-296)⟩,⟨(-134),(-106)⟩,⟨(-114),(-98)⟩,⟨(-106),(-110)⟩,⟨32,(-20)⟩,⟨(-6),(-48)⟩,⟨(-30),(-26)⟩,⟨(-4),4⟩],[⟨(-22),(-406)⟩,⟨(-24),(-62)⟩,⟨(-16),(-50)⟩,⟨(-4),(-38)⟩,⟨40,32⟩,⟨30,2⟩,⟨0,(-10)⟩],[⟨160,(-120)⟩,⟨(-20),(-120)⟩,⟨64,(-16)⟩,⟨(-32),(-16)⟩,⟨(-12),(-6)⟩,⟨8,(-2)⟩,⟨(-4),(-8)⟩],[⟨232,96⟩,⟨8,0⟩,⟨8,(-2)⟩,⟨6,(-4)⟩,⟨(-2),(-2)⟩],[⟨136,120⟩],[⟨24,72⟩],[⟨0,24⟩],[⟨(-8),0⟩]]

without_editor_info def starB_10 : Poly := [[⟨(-392),32⟩,⟨(-244),(-180)⟩,⟨(-152),(-74)⟩,⟨(-294),(-80)⟩,⟨(-88),(-160)⟩,⟨(-82),(-70)⟩,⟨(-124),(-66)⟩,⟨(-56),(-60)⟩,⟨(-34),(-28)⟩,⟨(-14),(-6)⟩],[⟨(-316),(-64)⟩,⟨(-212),(-94)⟩,⟨(-248),(-170)⟩,⟨(-232),(-94)⟩,⟨(-158),(-102)⟩,⟨(-116),(-126)⟩,⟨(-24),(-8)⟩,⟨(-16),(-10)⟩,⟨(-14),(-8)⟩,⟨(-4),4⟩],[⟨(-104),(-216)⟩,⟨(-98),(-40)⟩,⟨(-118),(-168)⟩,⟨(-10),(-66)⟩,⟨16,18⟩,⟨(-14),(-12)⟩,⟨(-4),14⟩,⟨2,12⟩,⟨2,2⟩],[⟨24,(-196)⟩,⟨8,(-16)⟩,⟨(-22),(-70)⟩,⟨(-6),(-58)⟩,⟨0,4⟩,⟨(-14),(-22)⟩,⟨(-14),(-22)⟩,⟨(-8),(-4)⟩],[⟨(-56),24⟩,⟨(-16),(-96)⟩,⟨74,10⟩,⟨(-16),6⟩,⟨(-6),(-18)⟩,⟨4,(-10)⟩,⟨(-4),(-8)⟩],[⟨80,56⟩,⟨(-80),16⟩,⟨(-64),(-74)⟩,⟨22,16⟩,⟨(-12),6⟩,⟨(-14),(-4)⟩,⟨(-4),4⟩]]

without_editor_info theorem star_10 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 10) (values x y) (constants 10) - value root_10 x y ^ 3 =
      value F x y * value starA_10 x y + values x y 10 * value starB_10 x y :=
  identity_power (neighbors 10) nodes (constants 10) F starA_10 starB_10 root_10 10 1 3 (by decide +kernel) x y

without_editor_info def root_11 : Poly := [[⟨1,0⟩],[⟨(-1),0⟩],[⟨0,1⟩],[⟨0,(-1)⟩]]

without_editor_info def starA_11 : Poly := [[⟨4,23⟩,⟨(-8),33⟩,⟨(-9),29⟩,⟨0,26⟩,⟨(-3),12⟩,⟨0,5⟩],[⟨(-15),(-5)⟩,⟨(-25),3⟩,⟨(-18),5⟩,⟨(-14),1⟩,⟨(-5),3⟩,⟨(-1),0⟩],[⟨(-15),(-3)⟩,⟨(-25),(-19)⟩,⟨(-18),(-15)⟩,⟨(-7),(-3)⟩,⟨(-2),(-2)⟩],[⟨(-2),(-10)⟩,⟨(-10),(-17)⟩,⟨(-6),(-7)⟩,⟨(-2),(-3)⟩],[⟨(-4),(-10)⟩,⟨2,(-8)⟩,⟨0,(-5)⟩],[⟨5,1⟩,⟨4,(-2)⟩,⟨1,0⟩],[⟨3,1⟩,⟨2,2⟩],[⟨0,1⟩]]

without_editor_info def starB_11 : Poly := [[⟨6,43⟩,⟨(-22),38⟩,⟨(-2),68⟩,⟨(-11),65⟩,⟨(-12),46⟩,⟨0,31⟩,⟨(-3),12⟩,⟨0,5⟩],[⟨(-25),12⟩,⟨(-40),22⟩,⟨(-39),17⟩,⟨(-47),14⟩,⟨(-24),13⟩,⟨(-15),1⟩,⟨(-5),3⟩,⟨(-1),0⟩],[⟨(-40),(-14)⟩,⟨(-38),(-30)⟩,⟨(-44),(-23)⟩,⟨(-36),(-21)⟩,⟨(-21),(-17)⟩,⟨(-7),(-3)⟩,⟨(-2),(-2)⟩],[⟨(-10),(-22)⟩,⟨(-23),(-29)⟩,⟨(-13),(-21)⟩,⟨(-16),(-24)⟩,⟨(-6),(-7)⟩,⟨(-2),(-3)⟩]]

without_editor_info theorem star_11 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 11) (values x y) (constants 11) - value root_11 x y ^ 3 =
      value F x y * value starA_11 x y + values x y 11 * value starB_11 x y :=
  identity_power (neighbors 11) nodes (constants 11) F starA_11 starB_11 root_11 11 1 3 (by decide +kernel) x y

without_editor_info def root_12 : Poly := [[⟨(-4),(-2)⟩,⟨(-8),(-4)⟩,⟨(-8),(-4)⟩,⟨(-4),(-2)⟩]]

without_editor_info def starA_12 : Poly := [[⟨24,24⟩,⟨96,36⟩,⟨44,(-56)⟩,⟨(-80),(-28)⟩,⟨(-20),92⟩,⟨32,52⟩],[⟨28,20⟩,⟨104,(-44)⟩,⟨(-84),(-264)⟩,⟨(-200),(-124)⟩,⟨(-24),36⟩,⟨8,4⟩],[⟨28,32⟩,⟨100,(-4)⟩,⟨(-36),(-144)⟩,⟨(-88),(-44)⟩,⟨(-4),16⟩],[⟨16,20⟩,⟨56,4⟩,⟨(-4),(-56)⟩,⟨(-20),(-16)⟩],[⟨4,8⟩,⟨16,8⟩,⟨4,(-4)⟩]]

without_editor_info def starB_12 : Poly := [[⟨(-8),8⟩,⟨(-8),188⟩,⟨296,688⟩,⟨560,976⟩,⟨564,1152⟩,⟨576,1032⟩,⟨332,532⟩,⟨88,188⟩,⟨24,48⟩],[⟨(-44),(-64)⟩,⟨(-180),(-132)⟩,⟨(-68),(-160)⟩,⟨(-156),(-528)⟩,⟨(-268),(-488)⟩,⟨(-76),(-272)⟩,⟨(-40),(-176)⟩,⟨(-32),(-52)⟩],[⟨(-12),0⟩,⟨(-36),108⟩,⟨96,264⟩,⟨48,228⟩,⟨60,276⟩,⟨96,168⟩,⟨36,36⟩],[⟨(-4),(-32)⟩,⟨(-32),(-100)⟩,⟨(-112),(-212)⟩,⟨(-184),(-164)⟩,⟨(-60),(-36)⟩,⟨(-16),(-20)⟩]]

without_editor_info theorem star_12 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 12) (values x y) (constants 12) - value root_12 x y ^ 3 =
      value F x y * value starA_12 x y + values x y 12 * value starB_12 x y :=
  identity_power (neighbors 12) nodes (constants 12) F starA_12 starB_12 root_12 12 1 3 (by decide +kernel) x y

without_editor_info def root_13 : Poly := [[⟨1,1⟩],[⟨0,1⟩],[⟨0,1⟩],[⟨(-1),0⟩]]

without_editor_info def starA_13 : Poly := [[⟨1,1⟩,⟨16,3⟩,⟨10,12⟩,⟨1,9⟩,⟨(-5),(-1)⟩,⟨(-4),(-2)⟩,⟨0,(-2)⟩],[⟨(-17),(-1)⟩,⟨(-2),(-3)⟩,⟨(-3),(-7)⟩,⟨4,1⟩,⟨4,0⟩,⟨1,3⟩],[⟨(-11),(-10)⟩,⟨2,2⟩,⟨0,0⟩,⟨0,2⟩,⟨(-1),(-1)⟩],[⟨(-3),(-6)⟩],[⟨0,(-3)⟩],[⟨1,0⟩]]

without_editor_info def starB_13 : Poly := [[⟨32,3⟩,⟨40,22⟩,⟨36,29⟩,⟨30,23⟩,⟨12,21⟩,⟨2,10⟩,⟨(-3),2⟩,⟨(-3),(-1)⟩,⟨0,(-1)⟩],[⟨41,23⟩,⟨34,38⟩,⟨24,41⟩,⟨13,33⟩,⟨(-4),17⟩,⟨(-9),4⟩,⟨(-4),(-1)⟩,⟨(-2),(-1)⟩],[⟨20,33⟩,⟨0,29⟩,⟨(-14),15⟩,⟨(-16),6⟩,⟨(-12),(-8)⟩,⟨(-7),(-5)⟩,⟨0,(-2)⟩,⟨(-1),(-1)⟩],[⟨(-7),17⟩,⟨(-17),2⟩,⟨(-18),(-10)⟩,⟨(-8),(-7)⟩,⟨(-1),(-8)⟩,⟨0,(-2)⟩,⟨2,0⟩]]

without_editor_info theorem star_13 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 13) (values x y) (constants 13) - value root_13 x y ^ 3 =
      value F x y * value starA_13 x y + values x y 13 * value starB_13 x y :=
  identity_power (neighbors 13) nodes (constants 13) F starA_13 starB_13 root_13 13 1 3 (by decide +kernel) x y

without_editor_info def root_14 : Poly := [[⟨2,2⟩]]

without_editor_info def starA_14 : Poly := [[⟨2,2⟩]]

without_editor_info def starB_14 : Poly := [[⟨0,4⟩,⟨0,(-2)⟩,⟨2,2⟩],[⟨4,2⟩,⟨2,2⟩],[⟨2,4⟩,⟨2,2⟩],[⟨(-2),2⟩]]

without_editor_info theorem star_14 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 14) (values x y) (constants 14) - value root_14 x y ^ 3 =
      value F x y * value starA_14 x y + values x y 14 * value starB_14 x y :=
  identity_power (neighbors 14) nodes (constants 14) F starA_14 starB_14 root_14 14 1 3 (by decide +kernel) x y

without_editor_info def root_15 : Poly := [[⟨(-1),(-2)⟩],[⟨(-2),2⟩],[⟨(-2),(-4)⟩],[⟨3,0⟩]]

without_editor_info def starA_15 : Poly := [[⟨(-54),(-117)⟩,⟨(-39),(-258)⟩,⟨39,(-435)⟩,⟨(-3),(-528)⟩,⟨162,(-444)⟩,⟨276,(-402)⟩,⟨192,(-228)⟩,⟨180,(-48)⟩,⟨78,(-30)⟩,⟨6,(-12)⟩],[⟨108,126⟩,⟨237,168⟩,⟨549,354⟩,⟨513,378⟩,⟨486,672⟩,⟨408,516⟩,⟨84,258⟩,⟨42,162⟩,⟨24,36⟩],[⟨(-186),(-192)⟩,⟨(-60),42⟩,⟨(-48),96⟩,⟨(-156),(-42)⟩,⟨(-192),(-24)⟩,⟨(-84),(-42)⟩,⟨(-72),(-66)⟩,⟨(-24),(-12)⟩],[⟨162,(-54)⟩,⟨(-18),(-18)⟩,⟨(-6),(-12)⟩,⟨6,(-30)⟩,⟨6,(-12)⟩,⟨18,6⟩,⟨6,0⟩],[⟨54,108⟩],[⟨(-27),0⟩]]

without_editor_info def starB_15 : Poly := [[⟨(-105),(-228)⟩,⟨(-27),(-405)⟩,⟨48,(-840)⟩,⟨78,(-1086)⟩,⟨723,(-1281)⟩,⟨921,(-1452)⟩,⟨1206,(-1050)⟩,⟨1308,(-702)⟩,⟨906,(-366)⟩,⟨564,(-66)⟩,⟨246,(-12)⟩,⟨54,(-6)⟩,⟨6,0⟩],[⟨(-48),(-6)⟩,⟨114,(-168)⟩,⟨210,57⟩,⟨(-27),579⟩,⟨141,1227⟩,⟨(-435),1362⟩,⟨(-774),1302⟩,⟨(-768),852⟩,⟨(-642),336⟩,⟨(-336),114⟩,⟨(-96),36⟩,⟨(-12),6⟩],[⟨(-288),(-216)⟩,⟨129,(-246)⟩,⟨(-63),(-531)⟩,⟨(-237),(-861)⟩,⟨(-138),(-801)⟩,⟨(-150),(-942)⟩,⟨(-102),(-798)⟩,⟨12,(-444)⟩,⟨54,(-222)⟩,⟨6,(-96)⟩,⟨(-6),(-18)⟩],[⟨45,(-162)⟩,⟨195,39⟩,⟨396,(-27)⟩,⟨621,(-147)⟩,⟨648,72⟩,⟨762,198⟩,⟨510,150⟩,⟨258,162⟩,⟨120,84⟩,⟨24,12⟩]]

without_editor_info theorem star_15 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 15) (values x y) (constants 15) - value root_15 x y ^ 3 =
      value F x y * value starA_15 x y + values x y 15 * value starB_15 x y :=
  identity_power (neighbors 15) nodes (constants 15) F starA_15 starB_15 root_15 15 1 3 (by decide +kernel) x y

without_editor_info def root_16 : Poly := [[],[⟨(-1),(-2)⟩],[⟨(-1),(-2)⟩],[⟨(-1),(-2)⟩]]

without_editor_info def starA_16 : Poly := [[⟨(-24),(-33)⟩,⟨42,(-48)⟩,⟨81,63⟩,⟨(-12),18⟩,⟨0,(-6)⟩],[⟨(-3),0⟩,⟨(-9),0⟩,⟨(-3),(-6)⟩,⟨9,6⟩],[⟨(-18),(-36)⟩],[⟨(-18),(-36)⟩],[⟨(-9),(-18)⟩],[⟨(-3),(-6)⟩]]

without_editor_info def starB_16 : Poly := [[⟨24,(-48)⟩,⟨129,54⟩,⟨54,63⟩,⟨60,27⟩,⟨45,57⟩,⟨(-12),12⟩,⟨0,(-6)⟩],[⟨(-51),(-120)⟩,⟨96,9⟩,⟨0,6⟩,⟨6,(-42)⟩,⟨48,39⟩,⟨(-9),6⟩],[⟨(-111),(-120)⟩,⟨27,(-39)⟩,⟨(-3),0⟩,⟨(-54),(-60)⟩,⟨39,3⟩,⟨0,6⟩],[⟨(-81),(-48)⟩,⟨(-30),(-63)⟩,⟨33,3⟩,⟨(-36),(-3)⟩,⟨0,(-12)⟩]]

without_editor_info theorem star_16 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 16) (values x y) (constants 16) - value root_16 x y ^ 3 =
      value F x y * value starA_16 x y + values x y 16 * value starB_16 x y :=
  identity_power (neighbors 16) nodes (constants 16) F starA_16 starB_16 root_16 16 1 3 (by decide +kernel) x y

without_editor_info def root_17 : Poly := [[⟨(-4),(-4)⟩,⟨(-6),(-4)⟩,⟨(-4),(-7)⟩,⟨(-3),(-2)⟩,⟨(-1),(-1)⟩,⟨4,3⟩,⟨1,2⟩,⟨1,1⟩]]

without_editor_info def starA_17 : Poly := [[⟨45,(-6)⟩,⟨72,(-76)⟩,⟨79,(-111)⟩,⟨(-16),(-74)⟩,⟨70,90⟩,⟨2,182⟩,⟨(-25),163⟩,⟨(-51),82⟩,⟨2,(-33)⟩,⟨(-8),(-57)⟩,⟨10,(-77)⟩,⟨22,(-10)⟩,⟨(-3),3⟩,⟨0,12⟩,⟨(-4),3⟩,⟨0,2⟩],[⟨(-5),(-5)⟩,⟨(-2),76⟩,⟨137,169⟩,⟨74,94⟩,⟨(-27),(-37)⟩,⟨(-95),(-3)⟩,⟨(-191),(-242)⟩,⟨(-44),(-95)⟩,⟨(-29),(-3)⟩,⟨55,19⟩,⟨65,83⟩,⟨20,36⟩,⟨(-3),(-2)⟩,⟨(-10),(-10)⟩,⟨(-3),(-7)⟩,⟨(-2),(-2)⟩],[⟨35,29⟩,⟨70,10⟩,⟨51,7⟩,⟨(-5),6⟩,⟨(-7),25⟩,⟨(-77),(-3)⟩,⟨(-61),(-32)⟩,⟨8,13⟩,⟨0,(-12)⟩,⟨34,2⟩,⟨17,10⟩,⟨0,(-1)⟩,⟨(-4),1⟩,⟨(-3),(-2)⟩,⟨(-1),0⟩],[⟨0,1⟩,⟨(-29),2⟩,⟨17,55⟩,⟨(-21),(-11)⟩,⟨17,(-1)⟩,⟨(-42),(-31)⟩,⟨45,(-43)⟩,⟨(-13),14⟩,⟨0,(-19)⟩,⟨12,31⟩,⟨(-14),1⟩,⟨4,6⟩,⟨(-3),(-5)⟩,⟨2,0⟩,⟨0,(-1)⟩]]

without_editor_info def starB_17 : Poly := [[⟨(-152),13⟩,⟨(-223),245⟩,⟨(-372),150⟩,⟨(-483),52⟩,⟨(-522),(-137)⟩,⟨(-182),(-366)⟩,⟨181,(-332)⟩,⟨371,(-78)⟩,⟨490,(-41)⟩,⟨401,273⟩,⟨(-29),113⟩,⟨(-60),56⟩,⟨(-206),(-1)⟩,⟨(-120),(-64)⟩,⟨(-39),(-27)⟩,⟨9,(-15)⟩,⟨25,10⟩,⟨12,3⟩,⟨5,3⟩,⟨1,0⟩],[⟨(-39),19⟩,⟨(-26),79⟩,⟨(-63),69⟩,⟨(-53),5⟩,⟨(-80),86⟩,⟨(-11),(-119)⟩,⟨178,114⟩,⟨(-47),(-118)⟩,⟨177,(-66)⟩,⟨(-9),12⟩,⟨(-17),(-84)⟩,⟨(-14),53⟩,⟨(-44),10⟩,⟨(-5),33⟩,⟨(-12),0⟩,⟨10,0⟩,⟨2,(-5)⟩,⟨3,(-1)⟩,⟨0,(-1)⟩],[⟨(-67),(-61)⟩,⟨(-88),(-28)⟩,⟨(-105),(-54)⟩,⟨62,51⟩,⟨(-4),23⟩,⟨247,62⟩,⟨41,85⟩,⟨(-1),(-132)⟩,⟨1,25⟩,⟨(-136),(-128)⟩,⟨6,18⟩,⟨(-25),9⟩,⟨32,29⟩,⟨6,20⟩,⟨7,(-2)⟩,⟨(-3),(-3)⟩,⟨0,(-3)⟩,⟨(-1),(-1)⟩],[⟨(-32),(-27)⟩,⟨(-27),30⟩,⟨(-12),(-52)⟩,⟨49,46⟩,⟨26,(-60)⟩,⟨98,66⟩,⟨(-45),(-30)⟩,⟨30,42⟩,⟨(-107),(-33)⟩,⟨12,(-1)⟩,⟨(-21),4⟩,⟨21,(-15)⟩,⟨17,16⟩,⟨3,(-4)⟩,⟨(-2),3⟩,⟨(-2),(-2)⟩,⟨(-1),0⟩],[⟨(-46),6⟩,⟨(-24),83⟩,⟨5,31⟩,⟨(-5),(-68)⟩,⟨(-46),(-52)⟩,⟨31,(-116)⟩,⟨61,16⟩,⟨(-58),19⟩,⟨37,29⟩,⟨(-16),52⟩,⟨(-18),(-18)⟩,⟨12,(-5)⟩,⟨(-3),(-11)⟩,⟨5,3⟩,⟨(-2),(-1)⟩,⟨0,1⟩],[⟨0,0⟩,⟨(-2),(-31)⟩,⟨(-55),(-37)⟩,⟨11,(-10)⟩,⟨1,18⟩,⟨31,(-11)⟩,⟨43,88⟩,⟨(-14),(-27)⟩,⟨19,19⟩,⟨(-31),(-19)⟩,⟨(-1),(-15)⟩,⟨(-6),(-2)⟩,⟨5,2⟩,⟨0,2⟩,⟨1,1⟩],[⟨(-31),(-29)⟩,⟨(-37),18⟩,⟨(-10),(-21)⟩,⟨18,17⟩,⟨(-11),(-42)⟩,⟨88,45⟩,⟨(-27),(-13)⟩,⟨19,0⟩,⟨(-19),12⟩,⟨(-15),(-14)⟩,⟨(-2),4⟩,⟨2,(-3)⟩,⟨2,2⟩,⟨1,0⟩]]

without_editor_info theorem star_17 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 17) (values x y) (constants 17) - value root_17 x y ^ 3 =
      value F x y * value starA_17 x y + values x y 17 * value starB_17 x y :=
  identity_power (neighbors 17) nodes (constants 17) F starA_17 starB_17 root_17 17 1 3 (by decide +kernel) x y

without_editor_info def root_18 : Poly := [[⟨6,6⟩,⟨(-34),(-9)⟩,⟨(-37),(-62)⟩,⟨(-4),(-57)⟩,⟨9,(-39)⟩,⟨26,(-22)⟩,⟨21,6⟩,⟨5,4⟩]]

without_editor_info def starA_18 : Poly := [[⟨701,580⟩,⟨(-3404),1976⟩,⟨(-23195),(-29003)⟩,⟨47169,(-51535)⟩,⟨208915,109696⟩,⟨213533,315857⟩,⟨60769,385914⟩,⟨(-169063),319317⟩,⟨(-387283),81910⟩,⟨(-395958),(-136665)⟩,⟨(-261543),(-193272)⟩,⟨(-121956),(-153957)⟩,⟨(-23040),(-76500)⟩,⟨8403,(-18150)⟩,⟨4869,(-540)⟩,⟨666,306⟩],[⟨(-530),258⟩,⟨(-1164),(-5523)⟩,⟨26759,11512⟩,⟨19945,72465⟩,⟨(-103063),32118⟩,⟨(-197661),(-108199)⟩,⟨(-197947),(-223448)⟩,⟨(-112938),(-285926)⟩,⟨52036,(-215099)⟩,⟨148876,(-68527)⟩,⟨140355,23850⟩,⟨90603,55188⟩,⟨33798,42126⟩,⟨3408,14835⟩,⟨(-1443),1983⟩,⟨(-324),18⟩],[⟨(-468),(-359)⟩,⟨2859,257⟩,⟨3696,12551⟩,⟨(-26971),588⟩,⟨(-49353),(-43726)⟩,⟨(-34787),(-72242)⟩,⟨(-2933),(-79955)⟩,⟨47046,(-52919)⟩,⟨72668,(-3374)⟩,⟨59640,23619⟩,⟨35805,27348⟩,⟨13173,18687⟩,⟨1170,6606⟩,⟨(-726),906⟩,⟨(-162),9⟩],[⟨174,(-54)⟩,⟨(-196),1325⟩,⟨(-6182),(-4967)⟩,⟨2263,(-11995)⟩,⟨22523,2462⟩,⟨30126,22077⟩,⟨28270,36831⟩,⟨10643,41592⟩,⟨(-12025),24651⟩,⟨(-19167),6027⟩,⟨(-16074),(-3411)⟩,⟨(-8946),(-6291)⟩,⟨(-2364),(-3504)⟩,⟨(-57),(-789)⟩,⟨51,(-60)⟩],[⟨0,3⟩,⟨5,(-9)⟩,⟨5,19⟩,⟨4,(-17)⟩,⟨2,15⟩],[⟨1,3⟩,⟨(-7),(-8)⟩,⟨9,15⟩,⟨(-13),(-15)⟩],[⟨2,1⟩,⟨(-6),(-4)⟩,⟨11,4⟩],[⟨1,0⟩,⟨(-3),2⟩],[⟨0,(-1)⟩]]

without_editor_info def starB_18 : Poly := [[⟨(-26),(-1186)⟩,⟨6993,6321⟩,⟨(-8948),26310⟩,⟨(-113504),(-33540)⟩,⟨(-221414),(-255455)⟩,⟨(-143895),(-508451)⟩,⟨198819,(-614587)⟩,⟨772967,(-388870)⟩,⟨1279510,174529⟩,⟨1389032,734594⟩,⟨1102030,1013447⟩,⟨599734,934275⟩,⟨147621,604724⟩,⟨(-79369),268566⟩,⟨(-119520),62901⟩,⟨(-76098),(-15360)⟩,⟨(-27108),(-19926)⟩,⟨(-4578),(-7203)⟩,⟨(-75),(-1131)⟩,⟨51,(-60)⟩],[⟨269,(-801)⟩,⟨4662,6365⟩,⟨(-18623),6987⟩,⟨(-60954),(-52758)⟩,⟨(-44798),(-124495)⟩,⟨32286,(-162375)⟩,⟨189292,(-134225)⟩,⟨382129,32530⟩,⟨456616,237921⟩,⟨392223,362077⟩,⟨234702,374615⟩,⟨54136,269216⟩,⟨(-50167),128529⟩,⟨(-70581),32916⟩,⟨(-49974),(-9489)⟩,⟨(-20805),(-14493)⟩,⟨(-4179),(-6090)⟩,⟨(-126),(-1071)⟩,⟨51,(-60)⟩],[⟨205,396⟩,⟨(-2224),(-2508)⟩,⟨7668,(-3966)⟩,⟨27680,23677⟩,⟨8242,50193⟩,⟨(-38332),22531⟩,⟨(-43094),(-7077)⟩,⟨(-21766),(-8981)⟩,⟨11642,8811⟩,⟨39441,54488⟩,⟨17042,74687⟩,⟨(-17599),50592⟩,⟨(-31071),20442⟩,⟨(-29334),(-1617)⟩,⟨(-15789),(-9258)⟩,⟨(-3891),(-5028)⟩,⟨(-177),(-1011)⟩,⟨51,(-60)⟩],[⟨49,310⟩,⟨(-2534),(-3029)⟩,⟨11689,(-2191)⟩,⟨24676,37036⟩,⟨(-30372),29329⟩,⟨(-63352),(-28974)⟩,⟨(-47147),(-51485)⟩,⟨(-21091),(-64724)⟩,⟨41550,(-30383)⟩,⟨62689,29969⟩,⟨34706,42459⟩,⟨10878,32070⟩,⟨(-7206),14883⟩,⟨(-10386),(-891)⟩,⟨(-3768),(-3279)⟩,⟨(-279),(-891)⟩,⟨51,(-60)⟩],[⟨(-34),(-615)⟩,⟨3624,3761⟩,⟨(-10474),9224⟩,⟨(-51478),(-38243)⟩,⟨(-31119),(-98360)⟩,⟨49948,(-89818)⟩,⟨130651,(-35799)⟩,⟨188537,53489⟩,⟨164132,122144⟩,⟨87209,113274⟩,⟨26916,70653⟩,⟨(-5880),28938⟩,⟨(-11292),2517⟩,⟨(-4155),(-2694)⟩,⟨(-330),(-831)⟩,⟨51,(-60)⟩],[⟨178,(-54)⟩,⟨(-209),1326⟩,⟨(-6156),(-4968)⟩,⟨2250,(-11980)⟩,⟨22541,2462⟩,⟨30119,22081⟩,⟨28270,36831⟩,⟨10643,41592⟩,⟨(-12025),24651⟩,⟨(-19167),6027⟩,⟨(-16074),(-3411)⟩,⟨(-8946),(-6291)⟩,⟨(-2364),(-3504)⟩,⟨(-57),(-789)⟩,⟨51,(-60)⟩],[⟨54,232⟩,⟨(-1094),(-1357)⟩,⟨3611,(-1451)⟩,⟨10529,9168⟩,⟨6706,18718⟩,⟨(-3363),20050⟩,⟨(-16781),14852⟩,⟨(-26740),684⟩,⟨(-23967),(-9252)⟩,⟨(-15279),(-10479)⟩,⟨(-7068),(-7863)⟩,⟨(-1572),(-3450)⟩,⟨54,(-738)⟩,⟨51,(-60)⟩]]

without_editor_info theorem star_18 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 18) (values x y) (constants 18) - value root_18 x y ^ 3 =
      value F x y * value starA_18 x y + values x y 18 * value starB_18 x y :=
  identity_power (neighbors 18) nodes (constants 18) F starA_18 starB_18 root_18 18 1 3 (by decide +kernel) x y

without_editor_info def root_19 : Poly := [[⟨2,(-2)⟩,⟨3,12⟩,⟨8,1⟩,⟨(-18),0⟩,⟨9,0⟩,⟨1,2⟩,⟨0,(-3)⟩,⟨1,2⟩],[⟨(-3),(-12)⟩,⟨(-16),(-2)⟩,⟨54,0⟩,⟨(-36),0⟩,⟨(-5),(-10)⟩,⟨0,18⟩,⟨(-7),(-14)⟩],[⟨8,1⟩,⟨(-54),0⟩,⟨54,0⟩,⟨10,20⟩,⟨0,(-45)⟩,⟨21,42⟩],[⟨18,0⟩,⟨(-36),0⟩,⟨(-10),(-20)⟩,⟨0,60⟩,⟨(-35),(-70)⟩],[⟨9,0⟩,⟨5,10⟩,⟨0,(-45)⟩,⟨35,70⟩],[⟨(-1),(-2)⟩,⟨0,18⟩,⟨(-21),(-42)⟩],[⟨0,(-3)⟩,⟨7,14⟩],[⟨(-1),(-2)⟩]]

without_editor_info def starA_19 : Poly := [[⟨34048254,14184123⟩,⟨14888511,6909180⟩,⟨110037672,63058797⟩,⟨34810389,36149400⟩,⟨123163257,96219114⟩,⟨28293945,70262706⟩,⟨41141418,37779600⟩,⟨22114953,65001687⟩,⟨(-11448627),(-12862155)⟩,⟨19622202,16414257⟩,⟨(-4654863),13338855⟩,⟨2808246,(-8727699)⟩,⟨272955,15339903⟩,⟨(-5357478),(-480327)⟩,⟨(-355782),(-2172804)⟩,⟨(-2277840),707745⟩,⟨135252,(-873297)⟩,⟨9918,31797⟩],[⟨18162,29169⟩,⟨(-164655),(-337707)⟩,⟨809505,1006542⟩,⟨(-3208503),(-813480)⟩,⟨6873411,(-2929431)⟩,⟨(-4803603),9985911⟩,⟨(-6509166),(-18145497)⟩,⟨26277840,25937865⟩,⟨(-32898564),(-15415668)⟩,⟨16460928,(-2745414)⟩,⟨(-813762),18139824⟩,⟨(-14143941),(-22718241)⟩,⟨8944896,7555380⟩,⟨(-3519813),314472⟩,⟨480624,(-4515540)⟩,⟨881790,2182188⟩,⟨(-61047),(-122094)⟩],[⟨20832,31647⟩,⟨(-143451),(-176013)⟩,⟨643581,4959⟩,⟨(-1489743),1942560⟩,⟨369810,(-5578893)⟩,⟨5685057,9609228⟩,⟨(-18194322),(-13360020)⟩,⟨24481539,6844779⟩,⟨(-12405033),6354630⟩,⟨(-1320693),(-17130909)⟩,⟨14899167,22757949⟩,⟨(-11812554),(-8958600)⟩,⟨4185048,(-182910)⟩,⟨(-1197684),4790736⟩,⟨(-1058148),(-3162816)⟩,⟨162792,325584⟩],[⟨2915397,36904902⟩,⟨(-102461688),(-42468885)⟩,⟨(-35484999),89473029⟩,⟨(-88468257),(-85466688)⟩,⟨(-8029983),37363374⟩,⟨10883829,(-11058195)⟩,⟨(-14194866),15905637⟩,⟨19511310,10983687⟩,⟨(-4051803),19561890⟩,⟨(-13448361),(-25828566)⟩,⟨15146454,13804836⟩,⟨(-8991273),(-3412095)⟩,⟨2141880,(-1501134)⟩,⟨(-1858656),2969814⟩,⟨(-1100535),(-3454158)⟩,⟨528714,520506⟩,⟨(-7344),(-4617)⟩],[⟨1836,(-702)⟩,⟨32517,122139⟩,⟨(-268416),(-512505)⟩,⟨1223817,871509⟩,⟨(-4137054),(-583671)⟩,⟨6845934,(-2527302)⟩,⟨(-2476140),7935117⟩,⟨(-5644953),(-12655080)⟩,⟨15162948,17336412⟩,⟨(-15273822),(-9273426)⟩,⟨5931237,(-763239)⟩,⟨(-2181219),5160894⟩,⟨(-881790),(-5164770)⟩,⟨610470,1220940⟩],[⟨(-6453),(-9585)⟩,⟨63405,71244⟩,⟨(-306054),(-94734)⟩,⟨1235640,(-339096)⟩,⟨(-2349432),2289924⟩,⟨91368,(-5502168)⟩,⟨5307399,8654247⟩,⟨(-12707163),(-12409614)⟩,⟨13981464,7542909⟩,⟨(-6046563),1169706⟩,⟨2255319,(-5065020)⟩,⟨610470,5755860⟩,⟨(-881790),(-1763580)⟩],[⟨34071429,14197677⟩,⟨6207501,(-103954722)⟩,⟨7241895,20429028⟩,⟨(-12812094),(-57179748)⟩,⟨(-2887902),(-5439393)⟩,⟨1445853,(-8476203)⟩,⟨3800991,757905⟩,⟨(-6450351),(-661053)⟩,⟨6365118,3447195⟩,⟨(-3620259),(-2269071)⟩,⟨3104022,(-3921447)⟩,⟨1802499,4868157⟩,⟨(-528714),(-520506)⟩,⟨7344,4617⟩],[⟨(-3054),2154⟩,⟨29316,(-52068)⟩,⟨(-78612),349836⟩,⟨(-306336),(-1036680)⟩,⟨1761018,2044623⟩,⟨(-4750644),(-3644394)⟩,⟨6587556,2870643⟩,⟨(-3694068),1100232⟩,⟨1522638,(-3495474)⟩,⟨162792,4860504⟩,⟨(-1058148),(-2116296)⟩],[⟨(-1497),5079⟩,⟨4473,(-62739)⟩,⟨100179,261054⟩,⟨(-618723),(-652464)⟩,⟨1986336,1401111⟩,⟨(-3240999),(-1293516)⟩,⟨2124225,(-711531)⟩,⟨(-967968),2276307⟩,⟨(-61047),(-3523284)⟩,⟨881790,1763580⟩],[⟨2885991,36919224⟩,⟨(-18048),(-40308)⟩,⟨148026,145581⟩,⟨(-614088),(-405837)⟩,⟨1234413,457272⟩,⟨(-971520),353391⟩,⟨506328,(-1215816)⟩,⟨17955,2128950⟩,⟨(-610470),(-1220940)⟩],[⟨1428,2883⟩,⟨(-21678),(-20244)⟩,⟨132150,83022⟩,⟨(-350472),(-121983)⟩,⟨344787,(-133035)⟩,⟨(-213294),520410⟩,⟨(-3990),(-1054500)⟩,⟨348840,697680⟩],[⟨1470,1320⟩,⟨(-17676),(-10674)⟩,⟨69786,23067⟩,⟨(-91506),36849⟩,⟨70398,(-173700)⟩,⟨630,419868⟩,⟨(-162792),(-325584)⟩],[⟨1107,648⟩,⟨(-8694),(-2754)⟩,⟨17091,(-7101)⟩,⟨(-17505),43506⟩,⟨(-63),(-130941)⟩,⟨61047,122094⟩],[⟨510,156⟩,⟨(-2004),852⟩,⟨3081,(-7689)⟩,⟨3,30786⟩,⟨(-17955),(-35910)⟩],[⟨111,(-48)⟩,⟨(-342),855⟩,⟨0,(-5130)⟩,⟨3990,7980⟩],[⟨18,(-45)⟩,⟨0,540⟩,⟨(-630),(-1260)⟩],[⟨0,(-27)⟩,⟨63,126⟩],[⟨(-3),(-6)⟩]]

without_editor_info def starB_19 : Poly := [[⟨(-68096484),(-28368198)⟩,⟨(-63825708),(-28002807)⟩,⟨(-200914419),(-118842393)⟩,⟨(-164771154),(-128449713)⟩,⟨(-205142871),(-179706237)⟩,⟨(-159835119),(-207512361)⟩,⟨(-63405588),(-98470419)⟩,⟨(-76992732),(-126769875)⟩,⟨(-5251713),(-48837600)⟩,⟨(-14051721),4016640⟩,⟨(-15730284),(-46387194)⟩,⟨4915203,(-3459876)⟩,⟨(-2589024),(-5310330)⟩,⟨7371147,(-15536550)⟩,⟨5579025,3527004⟩,⟨2623221,1433106⟩,⟨2142696,165525⟩,⟨(-145191),841539⟩,⟨(-9918),(-31824)⟩,⟨3,6⟩],[⟨(-34084146),(-14242137)⟩,⟨(-42947973),33464739⟩,⟨(-105423909),(-14693418)⟩,⟨(-104974053),13358970⟩,⟨(-157337013),(-39154020)⟩,⟨(-97905225),(-75503160)⟩,⟨(-77164464),(-16132761)⟩,⟨(-70762557),(-65443383)⟩,⟨12606018,(-7678869)⟩,⟨(-17457261),18490317⟩,⟨(-12132741),(-31563609)⟩,⟨13774857,4945872⟩,⟨(-10963623),139971⟩,⟨(-705516),(-10833960)⟩,⟨3564720,3022335⟩,⟨(-1176927),346722⟩,⟨21195,(-1074096)⟩,⟨29223,100728⟩,⟨(-57),(-123)⟩],[⟨(-39786906),(-68188641)⟩,⟨(-49639254),(-43330527)⟩,⟨(-10759626),(-57143418)⟩,⟨4220907,(-33735960)⟩,⟨(-7911801),(-17144178)⟩,⟨(-1773696),(-33855441)⟩,⟨5687466,15359862⟩,⟨(-27406365),(-12604530)⟩,⟨18047619,(-15378255)⟩,⟨(-6114861),15013530⟩,⟨(-8496435),(-23620803)⟩,⟨19345035,(-1345062)⟩,⟨(-2720739),8612607⟩,⟨2176368,(-3816690)⟩,⟨4534662,2095800⟩,⟨(-1169052),1603248⟩,⟨(-40158),(-269127)⟩,⟨504,1197⟩],[⟨(-25691988),(-107923950)⟩,⟨57527001,(-23168592)⟩,⟨61574409,(-164484567)⟩,⟨80414799,(-43382655)⟩,⟨28588194,(-60884019)⟩,⟨(-15193161),(-93270603)⟩,⟨8076720,(-7182486)⟩,⟨(-26545890),(-39647127)⟩,⟨4128813,(-25452495)⟩,⟨1691691,9407919⟩,⟨(-16238988),(-18914481)⟩,⟨14879061,(-3584052)⟩,⟨3350439,6419574⟩,⟨(-150075),(-5717529)⟩,⟨5685243,3246195⟩,⟨231189,2764686⟩,⟨(-524097),(-523233)⟩,⟨7344,4617⟩],[⟨(-8559873),(-90867606)⟩,⟨(-26761830),(-96601869)⟩,⟨(-42245763),(-152009487)⟩,⟨(-48298110),(-77881467)⟩,⟨(-100048383),(-111779685)⟩,⟨(-29222583),(-67993869)⟩,⟨(-29492562),(-26518275)⟩,⟨(-23764455),(-32704470)⟩,⟨10803567,1148388⟩,⟨(-7106103),8047998⟩,⟨(-707358),(-20007771)⟩,⟨11399616,1526373⟩,⟨(-1289991),1189641⟩,⟨2940462,(-723582)⟩,⟨2250660,2022225⟩,⟨(-515889),5481⟩,⟨4617,(-2727)⟩],[⟨82231962,(-25691988)⟩,⟨(-10172013),(-24780732)⟩,⟨47225145,17426358⟩,⟨(-18040020),(-4568193)⟩,⟨(-35634399),(-18421521)⟩,⟨(-15662223),(-22356270)⟩,⟨(-17100264),(-12273045)⟩,⟨2245185,(-1215333)⟩,⟨13977102,7461843⟩,⟨(-8813025),(-6748155)⟩,⟨(-3253611),(-8546730)⟩,⟨7268367,2326803⟩,⟨1710849,2023926⟩,⟨(-511272),2754⟩,⟨4617,(-2727)⟩],[⟨14152491,(-36963471)⟩,⟨(-2253528),59008797⟩,⟨15611643,29424534⟩,⟨28267170,44509041⟩,⟨(-2001414),40280238⟩,⟨(-8734503),(-5030061)⟩,⟨(-1769271),4928640⟩,⟨276969,(-4194579)⟩,⟨3592437,(-1160340)⟩,⟨(-5170296),1612605⟩,⟨(-1688217),(-3452862)⟩,⟨2007510,(-744351)⟩,⟨8208,528714⟩,⟨(-2727),(-7344)⟩],[⟨70942476,31142463⟩,⟨73877634,85144275⟩,⟨45961992,(-33005712)⟩,⟨44403792,54243735⟩,⟨(-10480728),(-19127721)⟩,⟨(-3366075),(-8253339)⟩,⟨5030061,(-3704442)⟩,⟨(-4928640),(-6697911)⟩,⟨4194579,4471548⟩,⟨1160340,4752777⟩,⟨(-1612605),(-6782901)⟩,⟨3452862,1764645⟩,⟨744351,2751861⟩,⟨(-528714),(-520506)⟩,⟨7344,4617⟩],[⟨51115962,14152491⟩,⟨(-30119862),(-42053541)⟩,⟨20215422,12725793⟩,⟨(-19127721),(-8646993)⟩,⟨(-8253339),(-4887264)⟩,⟨(-3704442),(-8734503)⟩,⟨(-6697911),(-1769271)⟩,⟨4471548,276969⟩,⟨4752777,3592437⟩,⟨(-6782901),(-5170296)⟩,⟨1764645,(-1688217)⟩,⟨2751861,2007510⟩,⟨(-520506),8208⟩,⟨4617,(-2727)⟩],[⟨34028313,(-2885850)⟩],[⟨0,0⟩,⟨2885850,36914163⟩],[⟨36914163,34028313⟩]]

without_editor_info theorem star_19 (x y : ℤ) :
    (3 : Eisenstein)^3 * rowProduct (neighbors 19) (values x y) (constants 19) - value root_19 x y ^ 3 =
      value F x y * value starA_19 x y + values x y 19 * value starB_19 x y :=
  identity_power (neighbors 19) nodes (constants 19) F starA_19 starB_19 root_19 19 3 3 (by decide +kernel) x y

without_editor_info def bezA_0 : Poly := [[⟨1,(-1)⟩]]

without_editor_info def bezB_0 : Poly := [[⟨6,0⟩,⟨3,0⟩,⟨1,(-1)⟩],[⟨1,(-1)⟩],[⟨1,(-1)⟩],[⟨1,(-1)⟩]]

without_editor_info def bezC_0 : Poly := [[⟨(-2),2⟩],[⟨(-1),1⟩],[⟨(-1),1⟩],[⟨(-1),1⟩]]

without_editor_info theorem bezout_0 (x y : ℤ) :
    value F x y * value bezA_0 x y + values x y 0 * value bezB_0 x y +
      values x y 8 * value bezC_0 x y = (6 : Eisenstein) :=
  bezout F (nodes 0) (nodes 8) bezA_0 bezB_0 bezC_0 6 (by decide +kernel) x y

without_editor_info def bezA_1 : Poly := [[⟨0,(-1)⟩]]

without_editor_info def bezB_1 : Poly := [[⟨2,0⟩,⟨1,(-1)⟩,⟨0,(-1)⟩],[⟨1,1⟩],[⟨1,0⟩],[⟨0,(-1)⟩]]

without_editor_info def bezC_1 : Poly := [[],[⟨(-1),(-1)⟩],[⟨(-1),0⟩],[⟨0,1⟩]]

without_editor_info theorem bezout_1 (x y : ℤ) :
    value F x y * value bezA_1 x y + values x y 0 * value bezB_1 x y +
      values x y 13 * value bezC_1 x y = (2 : Eisenstein) :=
  bezout F (nodes 0) (nodes 13) bezA_1 bezB_1 bezC_1 2 (by decide +kernel) x y

without_editor_info def bezA_2 : Poly := [[⟨(-1),(-2)⟩]]

without_editor_info def bezB_2 : Poly := [[⟨6,0⟩,⟨0,(-3)⟩,⟨(-1),(-2)⟩],[⟨(-1),(-2)⟩],[⟨(-1),1⟩],[⟨2,1⟩]]

without_editor_info def bezC_2 : Poly := [[⟨(-4),(-2)⟩],[⟨1,2⟩],[⟨1,(-1)⟩],[⟨(-2),(-1)⟩]]

without_editor_info theorem bezout_2 (x y : ℤ) :
    value F x y * value bezA_2 x y + values x y 0 * value bezB_2 x y +
      values x y 16 * value bezC_2 x y = (6 : Eisenstein) :=
  bezout F (nodes 0) (nodes 16) bezA_2 bezB_2 bezC_2 6 (by decide +kernel) x y

without_editor_info def bezA_3 : Poly := [[⟨0,1⟩]]

without_editor_info def bezB_3 : Poly := [[⟨5,(-7)⟩,⟨(-1),(-6)⟩,⟨0,1⟩],[⟨3,(-1)⟩,⟨(-4),(-4)⟩],[⟨0,(-2)⟩,⟨(-2),0⟩],[⟨(-1),(-1)⟩,⟨0,1⟩],[⟨(-1),(-1)⟩]]

without_editor_info def bezC_3 : Poly := [[⟨0,(-7)⟩],[⟨(-4),(-4)⟩],[⟨(-2),0⟩],[⟨0,1⟩]]

without_editor_info theorem bezout_3 (x y : ℤ) :
    value F x y * value bezA_3 x y + values x y 0 * value bezB_3 x y +
      values x y 17 * value bezC_3 x y = (12 : Eisenstein) :=
  bezout F (nodes 0) (nodes 17) bezA_3 bezB_3 bezC_3 12 (by decide +kernel) x y

without_editor_info def bezA_4 : Poly := [[⟨1,0⟩]]

without_editor_info def bezB_4 : Poly := [[⟨0,0⟩,⟨0,(-1)⟩,⟨1,0⟩]]

without_editor_info def bezC_4 : Poly := [[⟨(-1),0⟩],[],[],[⟨(-1),0⟩]]

without_editor_info theorem bezout_4 (x y : ℤ) :
    value F x y * value bezA_4 x y + values x y 1 * value bezB_4 x y +
      values x y 2 * value bezC_4 x y = (2 : Eisenstein) :=
  bezout F (nodes 1) (nodes 2) bezA_4 bezB_4 bezC_4 2 (by decide +kernel) x y

without_editor_info def bezA_5 : Poly := [[⟨1,0⟩]]

without_editor_info def bezB_5 : Poly := [[⟨0,0⟩,⟨0,(-1)⟩,⟨1,0⟩]]

without_editor_info def bezC_5 : Poly := [[],[⟨(-1),0⟩],[⟨1,0⟩],[⟨(-1),0⟩]]

without_editor_info theorem bezout_5 (x y : ℤ) :
    value F x y * value bezA_5 x y + values x y 1 * value bezB_5 x y +
      values x y 4 * value bezC_5 x y = (2 : Eisenstein) :=
  bezout F (nodes 1) (nodes 4) bezA_5 bezB_5 bezC_5 2 (by decide +kernel) x y

without_editor_info def bezA_6 : Poly := [[⟨1,0⟩]]

without_editor_info def bezB_6 : Poly := [[⟨0,0⟩,⟨0,(-1)⟩,⟨1,0⟩]]

without_editor_info def bezC_6 : Poly := [[],[⟨1,1⟩],[⟨0,1⟩],[⟨(-1),0⟩]]

without_editor_info theorem bezout_6 (x y : ℤ) :
    value F x y * value bezA_6 x y + values x y 1 * value bezB_6 x y +
      values x y 5 * value bezC_6 x y = (2 : Eisenstein) :=
  bezout F (nodes 1) (nodes 5) bezA_6 bezB_6 bezC_6 2 (by decide +kernel) x y

without_editor_info def bezA_7 : Poly := [[⟨0,(-1)⟩]]

without_editor_info def bezB_7 : Poly := [[⟨0,0⟩,⟨(-1),(-1)⟩,⟨0,(-1)⟩]]

without_editor_info def bezC_7 : Poly := [[⟨0,2⟩],[⟨1,0⟩],[⟨(-1),(-1)⟩],[⟨0,1⟩]]

without_editor_info theorem bezout_7 (x y : ℤ) :
    value F x y * value bezA_7 x y + values x y 1 * value bezB_7 x y +
      values x y 6 * value bezC_7 x y = (2 : Eisenstein) :=
  bezout F (nodes 1) (nodes 6) bezA_7 bezB_7 bezC_7 2 (by decide +kernel) x y

without_editor_info def bezA_8 : Poly := [[⟨1,0⟩]]

without_editor_info def bezB_8 : Poly := [[⟨0,0⟩,⟨0,(-1)⟩,⟨1,0⟩],[⟨(-1),0⟩],[⟨1,1⟩]]

without_editor_info def bezC_8 : Poly := [[],[⟨1,0⟩],[⟨(-1),(-1)⟩]]

without_editor_info theorem bezout_8 (x y : ℤ) :
    value F x y * value bezA_8 x y + values x y 1 * value bezB_8 x y +
      values x y 10 * value bezC_8 x y = (2 : Eisenstein) :=
  bezout F (nodes 1) (nodes 10) bezA_8 bezB_8 bezC_8 2 (by decide +kernel) x y

without_editor_info def bezA_9 : Poly := [[⟨0,(-1)⟩]]

without_editor_info def bezB_9 : Poly := [[⟨0,2⟩,⟨(-1),(-1)⟩,⟨0,(-1)⟩],[⟨1,0⟩],[⟨(-1),(-1)⟩],[⟨0,1⟩]]

without_editor_info def bezC_9 : Poly := [[⟨0,2⟩],[⟨1,0⟩],[⟨(-1),(-1)⟩],[⟨0,1⟩]]

without_editor_info theorem bezout_9 (x y : ℤ) :
    value F x y * value bezA_9 x y + values x y 1 * value bezB_9 x y +
      values x y 12 * value bezC_9 x y = (2 : Eisenstein) :=
  bezout F (nodes 1) (nodes 12) bezA_9 bezB_9 bezC_9 2 (by decide +kernel) x y

without_editor_info def bezA_10 : Poly := [[⟨1,1⟩]]

without_editor_info def bezB_10 : Poly := [[⟨2,2⟩,⟨1,0⟩,⟨1,1⟩],[⟨(-1),0⟩],[⟨0,(-1)⟩],[⟨1,1⟩]]

without_editor_info def bezC_10 : Poly := [[⟨(-2),(-2)⟩],[⟨1,0⟩],[⟨0,1⟩],[⟨(-1),(-1)⟩]]

without_editor_info theorem bezout_10 (x y : ℤ) :
    value F x y * value bezA_10 x y + values x y 1 * value bezB_10 x y +
      values x y 13 * value bezC_10 x y = (2 : Eisenstein) :=
  bezout F (nodes 1) (nodes 13) bezA_10 bezB_10 bezC_10 2 (by decide +kernel) x y

without_editor_info def bezA_11 : Poly := [[⟨1,0⟩]]

without_editor_info def bezB_11 : Poly := [[⟨2,2⟩,⟨0,(-1)⟩,⟨1,0⟩],[⟨1,1⟩],[⟨1,1⟩],[⟨1,1⟩]]

without_editor_info def bezC_11 : Poly := [[⟨(-2),(-2)⟩],[⟨(-1),(-1)⟩],[⟨(-1),(-1)⟩],[⟨(-1),(-1)⟩]]

without_editor_info theorem bezout_11 (x y : ℤ) :
    value F x y * value bezA_11 x y + values x y 1 * value bezB_11 x y +
      values x y 15 * value bezC_11 x y = (4 : Eisenstein) :=
  bezout F (nodes 1) (nodes 15) bezA_11 bezB_11 bezC_11 4 (by decide +kernel) x y

without_editor_info def bezA_12 : Poly := [[⟨1,0⟩]]

without_editor_info def bezB_12 : Poly := [[⟨0,1⟩,⟨(-1),(-1)⟩,⟨1,0⟩],[⟨0,(-1)⟩],[],[⟨0,1⟩,⟨(-1),0⟩],[⟨0,(-1)⟩]]

without_editor_info def bezC_12 : Poly := [[⟨(-1),0⟩],[],[],[⟨(-1),0⟩]]

without_editor_info theorem bezout_12 (x y : ℤ) :
    value F x y * value bezA_12 x y + values x y 1 * value bezB_12 x y +
      values x y 17 * value bezC_12 x y = (2 : Eisenstein) :=
  bezout F (nodes 1) (nodes 17) bezA_12 bezB_12 bezC_12 2 (by decide +kernel) x y

without_editor_info def bezA_13 : Poly := [[⟨(-1),0⟩]]

without_editor_info def bezB_13 : Poly := [[⟨(-2),(-3)⟩,⟨1,1⟩,⟨(-1),(-1)⟩],[],[],[⟨1,0⟩]]

without_editor_info def bezC_13 : Poly := [[⟨3,3⟩,⟨(-1),(-1)⟩,⟨1,1⟩]]

without_editor_info theorem bezout_13 (x y : ℤ) :
    value F x y * value bezA_13 x y + values x y 2 * value bezB_13 x y +
      values x y 9 * value bezC_13 x y = (4 : Eisenstein) :=
  bezout F (nodes 2) (nodes 9) bezA_13 bezB_13 bezC_13 4 (by decide +kernel) x y

without_editor_info def bezA_14 : Poly := [[⟨1,1⟩]]

without_editor_info def bezB_14 : Poly := [[⟨(-1),(-1)⟩],[],[],[⟨(-1),(-1)⟩]]

without_editor_info def bezC_14 : Poly := [[⟨0,2⟩,⟨0,(-1)⟩,⟨1,1⟩]]

without_editor_info theorem bezout_14 (x y : ℤ) :
    value F x y * value bezA_14 x y + values x y 2 * value bezB_14 x y +
      values x y 14 * value bezC_14 x y = (4 : Eisenstein) :=
  bezout F (nodes 2) (nodes 14) bezA_14 bezB_14 bezC_14 4 (by decide +kernel) x y

without_editor_info def bezA_15 : Poly := [[⟨1,1⟩,⟨1,1⟩],[],[],[],[⟨0,1⟩]]

without_editor_info def bezB_15 : Poly := [[⟨(-3),(-2)⟩,⟨(-1),(-1)⟩,⟨(-1),(-1)⟩,⟨(-1),(-1)⟩],[],[],[⟨(-1),(-2)⟩],[⟨(-1),(-2)⟩,⟨0,0⟩,⟨0,(-1)⟩],[],[],[⟨0,(-1)⟩]]

without_editor_info def bezC_15 : Poly := [[⟨1,(-1)⟩,⟨(-1),(-2)⟩,⟨(-1),(-1)⟩],[],[],[],[⟨1,0⟩,⟨0,(-1)⟩]]

without_editor_info theorem bezout_15 (x y : ℤ) :
    value F x y * value bezA_15 x y + values x y 2 * value bezB_15 x y +
      values x y 18 * value bezC_15 x y = (1 : Eisenstein) :=
  bezout F (nodes 2) (nodes 18) bezA_15 bezB_15 bezC_15 1 (by decide +kernel) x y

without_editor_info def bezA_16 : Poly := [[⟨1,0⟩]]

without_editor_info def bezB_16 : Poly := [[⟨(-1),0⟩,⟨0,1⟩,⟨0,1⟩],[⟨(-1),(-1)⟩,⟨(-1),(-1)⟩],[],[⟨(-1),0⟩]]

without_editor_info def bezC_16 : Poly := [[⟨(-1),0⟩,⟨(-1),0⟩]]

without_editor_info theorem bezout_16 (x y : ℤ) :
    value F x y * value bezA_16 x y + values x y 2 * value bezB_16 x y +
      values x y 19 * value bezC_16 x y = (1 : Eisenstein) :=
  bezout F (nodes 2) (nodes 19) bezA_16 bezB_16 bezC_16 1 (by decide +kernel) x y

without_editor_info def bezA_17 : Poly := [[⟨(-1),(-1)⟩]]

without_editor_info def bezB_17 : Poly := [[⟨(-2),(-4)⟩,⟨1,2⟩,⟨0,(-1)⟩],[⟨(-1),0⟩],[⟨0,(-1)⟩],[⟨1,1⟩]]

without_editor_info def bezC_17 : Poly := [[⟨4,6⟩,⟨(-1),(-2)⟩,⟨0,1⟩]]

without_editor_info theorem bezout_17 (x y : ℤ) :
    value F x y * value bezA_17 x y + values x y 3 * value bezB_17 x y +
      values x y 9 * value bezC_17 x y = (12 : Eisenstein) :=
  bezout F (nodes 3) (nodes 9) bezA_17 bezB_17 bezC_17 12 (by decide +kernel) x y

without_editor_info def bezA_18 : Poly := [[⟨0,(-1)⟩]]

without_editor_info def bezB_18 : Poly := [[⟨(-2),(-2)⟩,⟨1,2⟩,⟨1,(-1)⟩],[⟨1,(-1)⟩,⟨(-1),0⟩,⟨1,1⟩],[⟨1,0⟩],[⟨0,1⟩]]

without_editor_info def bezC_18 : Poly := [[⟨(-2),(-2)⟩,⟨1,1⟩,⟨0,(-1)⟩]]

without_editor_info theorem bezout_18 (x y : ℤ) :
    value F x y * value bezA_18 x y + values x y 3 * value bezB_18 x y +
      values x y 10 * value bezC_18 x y = (2 : Eisenstein) :=
  bezout F (nodes 3) (nodes 10) bezA_18 bezB_18 bezC_18 2 (by decide +kernel) x y

without_editor_info def bezA_19 : Poly := [[⟨1,2⟩]]

without_editor_info def bezB_19 : Poly := [[⟨(-2),(-4)⟩],[⟨2,1⟩],[⟨(-1),1⟩],[⟨(-1),(-2)⟩]]

without_editor_info def bezC_19 : Poly := [[⟨1,2⟩,⟨0,0⟩,⟨1,2⟩]]

without_editor_info theorem bezout_19 (x y : ℤ) :
    value F x y * value bezA_19 x y + values x y 3 * value bezB_19 x y +
      values x y 11 * value bezC_19 x y = (3 : Eisenstein) :=
  bezout F (nodes 3) (nodes 11) bezA_19 bezB_19 bezC_19 3 (by decide +kernel) x y

without_editor_info def bezA_20 : Poly := [[⟨1,1⟩]]

without_editor_info def bezB_20 : Poly := [[⟨(-2),(-2)⟩,⟨0,1⟩,⟨1,1⟩],[⟨1,0⟩],[⟨0,1⟩],[⟨(-1),(-1)⟩]]

without_editor_info def bezC_20 : Poly := [[⟨0,0⟩,⟨0,(-1)⟩,⟨(-1),(-1)⟩]]

without_editor_info theorem bezout_20 (x y : ℤ) :
    value F x y * value bezA_20 x y + values x y 3 * value bezB_20 x y +
      values x y 12 * value bezC_20 x y = (2 : Eisenstein) :=
  bezout F (nodes 3) (nodes 12) bezA_20 bezB_20 bezC_20 2 (by decide +kernel) x y

without_editor_info def bezA_21 : Poly := [[⟨2,1⟩]]

without_editor_info def bezB_21 : Poly := [[⟨(-3),(-6)⟩,⟨(-3),0⟩,⟨1,2⟩],[⟨1,(-1)⟩],[⟨1,2⟩],[⟨(-2),(-1)⟩]]

without_editor_info def bezC_21 : Poly := [[⟨(-4),(-5)⟩,⟨0,3⟩,⟨2,1⟩]]

without_editor_info theorem bezout_21 (x y : ℤ) :
    value F x y * value bezA_21 x y + values x y 3 * value bezB_21 x y +
      values x y 16 * value bezC_21 x y = (12 : Eisenstein) :=
  bezout F (nodes 3) (nodes 16) bezA_21 bezB_21 bezC_21 12 (by decide +kernel) x y

without_editor_info def bezA_22 : Poly := [[⟨0,3⟩,⟨1,2⟩],[],[],[],[⟨(-1),0⟩]]

without_editor_info def bezB_22 : Poly := [[⟨(-3),(-11)⟩,⟨(-1),(-2)⟩,⟨(-1),(-2)⟩,⟨(-1),(-2)⟩],[⟨5,5⟩],[⟨(-5),0⟩],[⟨0,(-5)⟩],[⟨2,0⟩,⟨(-1),(-1)⟩,⟨1,0⟩],[⟨0,1⟩],[⟨(-1),(-1)⟩],[⟨1,0⟩]]

without_editor_info def bezC_22 : Poly := [[⟨3,0⟩,⟨0,(-3)⟩,⟨(-1),(-2)⟩],[],[],[],[⟨0,0⟩,⟨1,0⟩]]

without_editor_info theorem bezout_22 (x y : ℤ) :
    value F x y * value bezA_22 x y + values x y 3 * value bezB_22 x y +
      values x y 18 * value bezC_22 x y = (8 : Eisenstein) :=
  bezout F (nodes 3) (nodes 18) bezA_22 bezB_22 bezC_22 8 (by decide +kernel) x y

without_editor_info def bezA_23 : Poly := [[⟨1,0⟩]]

without_editor_info def bezB_23 : Poly := [[⟨0,0⟩,⟨0,(-1)⟩,⟨1,0⟩],[⟨(-1),0⟩,⟨1,1⟩,⟨0,1⟩],[⟨1,0⟩],[⟨(-1),0⟩]]

without_editor_info def bezC_23 : Poly := [[⟨0,0⟩,⟨0,(-1)⟩,⟨1,0⟩]]

without_editor_info theorem bezout_23 (x y : ℤ) :
    value F x y * value bezA_23 x y + values x y 4 * value bezB_23 x y +
      values x y 10 * value bezC_23 x y = (2 : Eisenstein) :=
  bezout F (nodes 4) (nodes 10) bezA_23 bezB_23 bezC_23 2 (by decide +kernel) x y

without_editor_info def bezA_24 : Poly := [[⟨1,0⟩]]

without_editor_info def bezB_24 : Poly := [[⟨1,0⟩,⟨1,0⟩,⟨1,0⟩],[⟨(-1),0⟩],[⟨1,0⟩],[⟨(-1),0⟩]]

without_editor_info def bezC_24 : Poly := [[⟨(-1),0⟩,⟨(-1),0⟩,⟨(-1),0⟩]]

without_editor_info theorem bezout_24 (x y : ℤ) :
    value F x y * value bezA_24 x y + values x y 4 * value bezB_24 x y +
      values x y 12 * value bezC_24 x y = (2 : Eisenstein) :=
  bezout F (nodes 4) (nodes 12) bezA_24 bezB_24 bezC_24 2 (by decide +kernel) x y

without_editor_info def bezA_25 : Poly := [[⟨1,1⟩]]

without_editor_info def bezB_25 : Poly := [[],[⟨(-1),(-1)⟩],[⟨1,1⟩],[⟨(-1),(-1)⟩]]

without_editor_info def bezC_25 : Poly := [[⟨0,2⟩,⟨0,(-1)⟩,⟨1,1⟩]]

without_editor_info theorem bezout_25 (x y : ℤ) :
    value F x y * value bezA_25 x y + values x y 4 * value bezB_25 x y +
      values x y 14 * value bezC_25 x y = (4 : Eisenstein) :=
  bezout F (nodes 4) (nodes 14) bezA_25 bezB_25 bezC_25 4 (by decide +kernel) x y

without_editor_info def bezA_26 : Poly := [[⟨1,0⟩,⟨1,1⟩],[],[],[],[⟨0,1⟩]]

without_editor_info def bezB_26 : Poly := [[⟨(-1),1⟩,⟨(-2),(-1)⟩,⟨(-1),1⟩,⟨(-1),0⟩],[⟨0,(-1)⟩,⟨0,(-1)⟩,⟨0,(-1)⟩],[⟨1,1⟩],[⟨(-1),(-1)⟩],[⟨(-1),(-1)⟩,⟨(-1),(-1)⟩,⟨(-1),(-1)⟩],[⟨1,0⟩,⟨1,0⟩],[⟨0,1⟩],[⟨0,(-1)⟩]]

without_editor_info def bezC_26 : Poly := [[⟨0,(-1)⟩,⟨(-1),(-1)⟩,⟨(-1),(-1)⟩],[],[],[],[⟨1,0⟩,⟨0,(-1)⟩]]

without_editor_info theorem bezout_26 (x y : ℤ) :
    value F x y * value bezA_26 x y + values x y 4 * value bezB_26 x y +
      values x y 19 * value bezC_26 x y = (1 : Eisenstein) :=
  bezout F (nodes 4) (nodes 19) bezA_26 bezB_26 bezC_26 1 (by decide +kernel) x y

without_editor_info def bezA_27 : Poly := [[⟨1,0⟩]]

without_editor_info def bezB_27 : Poly := [[⟨(-1),0⟩,⟨(-1),0⟩,⟨(-1),0⟩],[⟨1,1⟩],[⟨0,1⟩],[⟨(-1),0⟩]]

without_editor_info def bezC_27 : Poly := [[⟨1,0⟩,⟨1,0⟩,⟨1,0⟩]]

without_editor_info theorem bezout_27 (x y : ℤ) :
    value F x y * value bezA_27 x y + values x y 5 * value bezB_27 x y +
      values x y 8 * value bezC_27 x y = (2 : Eisenstein) :=
  bezout F (nodes 5) (nodes 8) bezA_27 bezB_27 bezC_27 2 (by decide +kernel) x y

without_editor_info def bezA_28 : Poly := [[⟨1,0⟩]]

without_editor_info def bezB_28 : Poly := [[],[⟨1,1⟩],[⟨0,1⟩],[⟨(-1),0⟩]]

without_editor_info def bezC_28 : Poly := [[⟨1,0⟩,⟨0,0⟩,⟨1,0⟩]]

without_editor_info theorem bezout_28 (x y : ℤ) :
    value F x y * value bezA_28 x y + values x y 5 * value bezB_28 x y +
      values x y 11 * value bezC_28 x y = (1 : Eisenstein) :=
  bezout F (nodes 5) (nodes 11) bezA_28 bezB_28 bezC_28 1 (by decide +kernel) x y

without_editor_info def bezA_29 : Poly := [[⟨0,(-1)⟩]]

without_editor_info def bezB_29 : Poly := [[⟨(-2),(-2)⟩,⟨1,1⟩,⟨0,(-1)⟩],[⟨1,0⟩],[⟨1,1⟩],[⟨0,1⟩]]

without_editor_info def bezC_29 : Poly := [[⟨2,2⟩,⟨(-1),(-1)⟩,⟨0,1⟩]]

without_editor_info theorem bezout_29 (x y : ℤ) :
    value F x y * value bezA_29 x y + values x y 5 * value bezB_29 x y +
      values x y 12 * value bezC_29 x y = (4 : Eisenstein) :=
  bezout F (nodes 5) (nodes 12) bezA_29 bezB_29 bezC_29 4 (by decide +kernel) x y

without_editor_info def bezA_30 : Poly := [[⟨(-1),0⟩,⟨0,1⟩],[],[],[],[⟨(-1),0⟩]]

without_editor_info def bezB_30 : Poly := [[⟨(-2),(-3)⟩,⟨0,(-1)⟩,⟨0,(-1)⟩,⟨0,(-1)⟩],[⟨(-1),(-2)⟩],[⟨1,(-1)⟩],[⟨2,1⟩],[⟨(-1),(-1)⟩,⟨0,(-1)⟩,⟨1,0⟩],[⟨(-1),(-1)⟩],[⟨0,(-1)⟩],[⟨1,0⟩]]

without_editor_info def bezC_30 : Poly := [[⟨2,1⟩,⟨1,(-1)⟩,⟨0,(-1)⟩],[],[],[],[⟨1,0⟩,⟨1,0⟩]]

without_editor_info theorem bezout_30 (x y : ℤ) :
    value F x y * value bezA_30 x y + values x y 5 * value bezB_30 x y +
      values x y 18 * value bezC_30 x y = (2 : Eisenstein) :=
  bezout F (nodes 5) (nodes 18) bezA_30 bezB_30 bezC_30 2 (by decide +kernel) x y

without_editor_info def bezA_31 : Poly := [[⟨(-1),(-1)⟩,⟨0,(-1)⟩],[],[],[],[⟨(-1),(-1)⟩]]

without_editor_info def bezB_31 : Poly := [[⟨1,(-1)⟩,⟨2,1⟩,⟨2,1⟩,⟨1,1⟩],[⟨2,0⟩,⟨0,2⟩,⟨(-1),0⟩],[⟨2,0⟩],[⟨2,2⟩],[⟨1,0⟩,⟨1,0⟩,⟨1,0⟩],[⟨1,0⟩,⟨0,1⟩],[⟨1,0⟩],[⟨1,1⟩]]

without_editor_info def bezC_31 : Poly := [[⟨2,0⟩,⟨2,2⟩,⟨0,1⟩],[],[],[],[⟨1,0⟩,⟨1,1⟩]]

without_editor_info theorem bezout_31 (x y : ℤ) :
    value F x y * value bezA_31 x y + values x y 5 * value bezB_31 x y +
      values x y 19 * value bezC_31 x y = (1 : Eisenstein) :=
  bezout F (nodes 5) (nodes 19) bezA_31 bezB_31 bezC_31 1 (by decide +kernel) x y

without_editor_info def bezA_32 : Poly := [[⟨1,0⟩]]

without_editor_info def bezB_32 : Poly := [[⟨1,2⟩,⟨(-1),(-2)⟩,⟨(-1),0⟩],[⟨1,1⟩],[⟨0,(-1)⟩],[⟨(-1),0⟩]]

without_editor_info def bezC_32 : Poly := [[⟨(-3),(-2)⟩,⟨1,2⟩,⟨1,0⟩]]

without_editor_info theorem bezout_32 (x y : ℤ) :
    value F x y * value bezA_32 x y + values x y 6 * value bezB_32 x y +
      values x y 8 * value bezC_32 x y = (6 : Eisenstein) :=
  bezout F (nodes 6) (nodes 8) bezA_32 bezB_32 bezC_32 6 (by decide +kernel) x y

without_editor_info def bezA_33 : Poly := [[⟨(-1),(-2)⟩]]

without_editor_info def bezB_33 : Poly := [[⟨3,3⟩,⟨0,0⟩,⟨1,(-1)⟩],[⟨1,(-1)⟩],[⟨(-2),(-1)⟩],[⟨1,2⟩]]

without_editor_info def bezC_33 : Poly := [[⟨(-1),1⟩,⟨0,0⟩,⟨(-1),1⟩]]

without_editor_info theorem bezout_33 (x y : ℤ) :
    value F x y * value bezA_33 x y + values x y 6 * value bezB_33 x y +
      values x y 9 * value bezC_33 x y = (3 : Eisenstein) :=
  bezout F (nodes 6) (nodes 9) bezA_33 bezB_33 bezC_33 3 (by decide +kernel) x y

without_editor_info def bezA_34 : Poly := [[⟨1,1⟩]]

without_editor_info def bezB_34 : Poly := [[⟨(-2),(-2)⟩],[⟨(-2),(-1)⟩,⟨1,1⟩,⟨(-1),0⟩],[⟨1,0⟩],[⟨(-1),(-1)⟩]]

without_editor_info def bezC_34 : Poly := [[⟨0,2⟩,⟨0,(-1)⟩,⟨1,1⟩]]

without_editor_info theorem bezout_34 (x y : ℤ) :
    value F x y * value bezA_34 x y + values x y 6 * value bezB_34 x y +
      values x y 10 * value bezC_34 x y = (2 : Eisenstein) :=
  bezout F (nodes 6) (nodes 10) bezA_34 bezB_34 bezC_34 2 (by decide +kernel) x y

without_editor_info def bezA_35 : Poly := [[⟨(-3),(-3)⟩,⟨(-1),(-2)⟩],[],[],[],[⟨(-1),(-1)⟩]]

without_editor_info def bezB_35 : Poly := [[⟨7,10⟩,⟨1,2⟩,⟨1,2⟩,⟨1,2⟩],[⟨3,(-1)⟩],[⟨(-4),(-3)⟩],[⟨1,4⟩],[⟨4,3⟩,⟨(-1),0⟩,⟨1,1⟩],[⟨0,(-1)⟩],[⟨(-1),0⟩],[⟨1,1⟩]]

without_editor_info def bezC_35 : Poly := [[⟨(-3),0⟩,⟨0,3⟩,⟨1,2⟩],[],[],[],[⟨(-1),1⟩,⟨1,1⟩]]

without_editor_info theorem bezout_35 (x y : ℤ) :
    value F x y * value bezA_35 x y + values x y 6 * value bezB_35 x y +
      values x y 18 * value bezC_35 x y = (4 : Eisenstein) :=
  bezout F (nodes 6) (nodes 18) bezA_35 bezB_35 bezC_35 4 (by decide +kernel) x y

without_editor_info def bezA_36 : Poly := [[⟨(-1),(-1)⟩,⟨0,1⟩],[],[],[],[⟨(-1),(-1)⟩]]

without_editor_info def bezB_36 : Poly := [[⟨1,1⟩,⟨0,(-1)⟩,⟨0,(-1)⟩,⟨(-1),(-1)⟩],[⟨0,0⟩,⟨2,2⟩,⟨1,0⟩],[⟨(-2),0⟩],[⟨2,2⟩],[⟨1,0⟩,⟨1,0⟩,⟨1,0⟩],[⟨(-1),0⟩,⟨0,1⟩],[⟨(-1),0⟩],[⟨1,1⟩]]

without_editor_info def bezC_36 : Poly := [[⟨2,2⟩,⟨2,0⟩,⟨0,(-1)⟩],[],[],[],[⟨1,2⟩,⟨1,1⟩]]

without_editor_info theorem bezout_36 (x y : ℤ) :
    value F x y * value bezA_36 x y + values x y 6 * value bezB_36 x y +
      values x y 19 * value bezC_36 x y = (1 : Eisenstein) :=
  bezout F (nodes 6) (nodes 19) bezA_36 bezB_36 bezC_36 1 (by decide +kernel) x y

without_editor_info def bezA_37 : Poly := [[⟨1,0⟩]]

without_editor_info def bezB_37 : Poly := [[],[⟨0,(-1)⟩],[⟨(-1),(-1)⟩],[⟨(-1),0⟩]]

without_editor_info def bezC_37 : Poly := [[⟨1,0⟩,⟨0,0⟩,⟨1,0⟩]]

without_editor_info theorem bezout_37 (x y : ℤ) :
    value F x y * value bezA_37 x y + values x y 7 * value bezB_37 x y +
      values x y 11 * value bezC_37 x y = (1 : Eisenstein) :=
  bezout F (nodes 7) (nodes 11) bezA_37 bezB_37 bezC_37 1 (by decide +kernel) x y

without_editor_info def bezA_38 : Poly := [[⟨1,0⟩]]

without_editor_info def bezB_38 : Poly := [[⟨0,0⟩,⟨0,1⟩,⟨0,1⟩],[⟨0,(-1)⟩],[⟨(-1),(-1)⟩],[⟨(-1),0⟩]]

without_editor_info def bezC_38 : Poly := [[⟨(-1),0⟩,⟨(-1),0⟩]]

without_editor_info theorem bezout_38 (x y : ℤ) :
    value F x y * value bezA_38 x y + values x y 7 * value bezB_38 x y +
      values x y 17 * value bezC_38 x y = (1 : Eisenstein) :=
  bezout F (nodes 7) (nodes 17) bezA_38 bezB_38 bezC_38 1 (by decide +kernel) x y

without_editor_info def bezA_39 : Poly := [[⟨0,(-3)⟩]]

without_editor_info def bezB_39 : Poly := [[⟨(-2),(-4)⟩,⟨7,2⟩,⟨6,3⟩,⟨1,2⟩],[⟨3,0⟩,⟨6,6⟩,⟨0,3⟩],[⟨3,3⟩,⟨0,3⟩],[⟨0,3⟩]]

without_editor_info def bezC_39 : Poly := [[⟨2,4⟩,⟨2,(-2)⟩,⟨3,6⟩,⟨(-1),1⟩]]

without_editor_info theorem bezout_39 (x y : ℤ) :
    value F x y * value bezA_39 x y + values x y 8 * value bezB_39 x y +
      values x y 9 * value bezC_39 x y = (12 : Eisenstein) :=
  bezout F (nodes 8) (nodes 9) bezA_39 bezB_39 bezC_39 12 (by decide +kernel) x y

without_editor_info def bezA_40 : Poly := [[⟨3,0⟩]]

without_editor_info def bezB_40 : Poly := [[⟨0,0⟩,⟨7,5⟩,⟨5,7⟩,⟨(-1),1⟩],[⟨3,3⟩,⟨0,6⟩,⟨(-3),0⟩],[⟨0,3⟩,⟨(-3),0⟩],[⟨(-3),0⟩]]

without_editor_info def bezC_40 : Poly := [[⟨0,0⟩,⟨(-4),(-2)⟩,⟨(-2),(-7)⟩,⟨1,(-1)⟩]]

without_editor_info theorem bezout_40 (x y : ℤ) :
    value F x y * value bezA_40 x y + values x y 8 * value bezB_40 x y +
      values x y 16 * value bezC_40 x y = (6 : Eisenstein) :=
  bezout F (nodes 8) (nodes 16) bezA_40 bezB_40 bezC_40 6 (by decide +kernel) x y

without_editor_info def bezA_41 : Poly := [[⟨(-5),(-3)⟩,⟨(-5),(-8)⟩],[],[],[],[⟨1,3⟩]]

without_editor_info def bezB_41 : Poly := [[⟨10,9⟩,⟨7,3⟩,⟨1,13⟩,⟨(-3),(-6)⟩],[⟨(-1),5⟩,⟨(-12),(-2)⟩,⟨(-5),(-6)⟩],[⟨(-6),(-1)⟩,⟨(-5),(-6)⟩],[⟨(-5),(-6)⟩],[⟨0,0⟩,⟨(-3),(-2)⟩,⟨(-6),3⟩,⟨(-3),(-2)⟩],[⟨(-2),1⟩,⟨(-6),(-4)⟩,⟨(-1),(-3)⟩],[⟨(-3),(-2)⟩,⟨(-1),(-3)⟩],[⟨(-1),(-3)⟩]]

without_editor_info def bezC_41 : Poly := [[⟨25,5⟩,⟨3,19⟩,⟨2,2⟩],[],[],[],[⟨8,3⟩,⟨(-6),3⟩,⟨(-3),(-2)⟩]]

without_editor_info theorem bezout_41 (x y : ℤ) :
    value F x y * value bezA_41 x y + values x y 8 * value bezB_41 x y +
      values x y 17 * value bezC_41 x y = (6 : Eisenstein) :=
  bezout F (nodes 8) (nodes 17) bezA_41 bezB_41 bezC_41 6 (by decide +kernel) x y

without_editor_info def bezA_42 : Poly := [[⟨1,1⟩]]

without_editor_info def bezB_42 : Poly := [[⟨(-1),5⟩,⟨(-8),3⟩,⟨(-4),1⟩,⟨(-1),0⟩],[⟨0,4⟩,⟨0,4⟩,⟨0,1⟩],[⟨2,0⟩,⟨1,0⟩],[⟨(-1),(-1)⟩]]

without_editor_info def bezC_42 : Poly := [[⟨(-8),(-14)⟩,⟨(-4),(-15)⟩,⟨(-2),(-7)⟩,⟨0,(-1)⟩]]

without_editor_info theorem bezout_42 (x y : ℤ) :
    value F x y * value bezA_42 x y + values x y 9 * value bezB_42 x y +
      values x y 12 * value bezC_42 x y = (4 : Eisenstein) :=
  bezout F (nodes 9) (nodes 12) bezA_42 bezB_42 bezC_42 4 (by decide +kernel) x y

without_editor_info def bezA_43 : Poly := [[⟨1,1⟩]]

without_editor_info def bezB_43 : Poly := [[⟨(-9),(-9)⟩,⟨(-12),(-12)⟩,⟨(-6),(-6)⟩,⟨(-1),(-1)⟩],[⟨0,4⟩,⟨0,4⟩,⟨0,1⟩],[⟨2,0⟩,⟨1,0⟩],[⟨(-1),(-1)⟩]]

without_editor_info def bezC_43 : Poly := [[⟨(-6),8⟩,⟨(-11),4⟩,⟨(-5),2⟩,⟨(-1),0⟩]]

without_editor_info theorem bezout_43 (x y : ℤ) :
    value F x y * value bezA_43 x y + values x y 9 * value bezB_43 x y +
      values x y 14 * value bezC_43 x y = (4 : Eisenstein) :=
  bezout F (nodes 9) (nodes 14) bezA_43 bezB_43 bezC_43 4 (by decide +kernel) x y

without_editor_info def bezA_44 : Poly := [[⟨0,(-1)⟩]]

without_editor_info def bezB_44 : Poly := [[⟨(-4),(-1)⟩,⟨(-12),(-5)⟩,⟨(-6),0⟩,⟨(-1),0⟩],[⟨4,0⟩,⟨4,0⟩,⟨1,0⟩],[⟨(-2),(-2)⟩,⟨(-1),(-1)⟩],[⟨0,1⟩]]

without_editor_info def bezC_44 : Poly := [[⟨(-6),4⟩,⟨(-5),12⟩,⟨0,6⟩,⟨0,1⟩]]

without_editor_info theorem bezout_44 (x y : ℤ) :
    value F x y * value bezA_44 x y + values x y 9 * value bezB_44 x y +
      values x y 15 * value bezC_44 x y = (4 : Eisenstein) :=
  bezout F (nodes 9) (nodes 15) bezA_44 bezB_44 bezC_44 4 (by decide +kernel) x y

without_editor_info def bezA_45 : Poly := [[⟨4,5⟩],[],[],[⟨2,0⟩]]

without_editor_info def bezB_45 : Poly := [[⟨6,(-1)⟩,⟨1,(-3)⟩],[⟨0,(-1)⟩],[⟨(-3),(-4)⟩],[⟨2,0⟩,⟨0,(-2)⟩],[⟨2,0⟩],[⟨(-2),(-2)⟩]]

without_editor_info def bezC_45 : Poly := [[⟨(-6),5⟩,⟨(-1),3⟩,⟨4,5⟩],[⟨(-4),0⟩],[],[⟨(-2),0⟩,⟨0,2⟩,⟨2,0⟩],[⟨(-4),0⟩]]

without_editor_info theorem bezout_45 (x y : ℤ) :
    value F x y * value bezA_45 x y + values x y 10 * value bezB_45 x y +
      values x y 11 * value bezC_45 x y = (1 : Eisenstein) :=
  bezout F (nodes 10) (nodes 11) bezA_45 bezB_45 bezC_45 1 (by decide +kernel) x y

without_editor_info def bezA_46 : Poly := [[⟨93,106⟩,⟨134,114⟩],[],[],[],[⟨17,3⟩]]

without_editor_info def bezB_46 : Poly := [[⟨130,82⟩,⟨136,166⟩,⟨133,77⟩,⟨16,10⟩],[⟨32,(-106)⟩,⟨80,(-62)⟩,⟨6,16⟩],[⟨(-138),(-32)⟩,⟨36,(-30)⟩,⟨10,(-6)⟩],[],[⟨58,18⟩,⟨8,(-18)⟩,⟨(-8),(-15)⟩],[⟨(-2),(-10)⟩,⟨2,(-4)⟩],[⟨(-8),2⟩]]

without_editor_info def bezC_46 : Poly := [[⟨125,(-50)⟩,⟨(-98),(-156)⟩,⟨72,117⟩,⟨118,104⟩],[⟨(-188),(-90)⟩,⟨(-60),24⟩,⟨106,72⟩],[⟨0,0⟩,⟨131,36⟩],[⟨3,(-142)⟩],[⟨29,43⟩,⟨4,28⟩,⟨25,18⟩],[⟨(-28),32⟩,⟨16,30⟩],[⟨0,0⟩,⟨(-15),(-7)⟩],[⟨(-19),(-13)⟩]]

without_editor_info theorem bezout_46 (x y : ℤ) :
    value F x y * value bezA_46 x y + values x y 10 * value bezB_46 x y +
      values x y 13 * value bezC_46 x y = (8 : Eisenstein) :=
  bezout F (nodes 10) (nodes 13) bezA_46 bezB_46 bezC_46 8 (by decide +kernel) x y

without_editor_info def bezA_47 : Poly := [[⟨6254,1266⟩,⟨4115,(-2467)⟩,⟨1700,(-3887)⟩,⟨834,(-2354)⟩,⟨(-301),(-1580)⟩,⟨(-9),(-426)⟩],[⟨1844,(-836)⟩,⟨96,24⟩,⟨18,21⟩,⟨6,(-12)⟩],[⟨123,39⟩,⟨(-30),(-24)⟩,⟨33,72⟩],[⟨2271,549⟩,⟨(-247),130⟩],[⟨988,689⟩,⟨(-426),(-417)⟩]]

without_editor_info def bezB_47 : Poly := [[⟨5691,(-2011)⟩,⟨1864,(-2301)⟩,⟨2162,(-2529)⟩,⟨2166,829⟩,⟨(-505),331⟩,⟨33,(-21)⟩],[⟨171,(-3910)⟩,⟨2092,126⟩,⟨229,(-2896)⟩,⟨336,(-1658)⟩,⟨860,556⟩],[⟨(-4265),(-4607)⟩,⟨(-1609),(-1678)⟩,⟨(-2607),(-1560)⟩,⟨(-1068),(-1319)⟩,⟨12,18⟩],[⟨(-910),(-1373)⟩,⟨447,(-1842)⟩,⟨36,54⟩,⟨(-18),(-6)⟩],[⟨2870,649⟩,⟨6,30⟩,⟨39,(-33)⟩],[⟨(-1151),(-1573)⟩],[⟨(-299),(-988)⟩]]

without_editor_info def bezC_47 : Poly := [[⟨887,1148⟩,⟨(-3651),72⟩,⟨(-2288),5087⟩,⟨(-2133),5103⟩,⟨(-801),2333⟩,⟨301,1580⟩,⟨9,426⟩],[⟨2012,2358⟩,⟨1379,1330⟩,⟨3142,4313⟩,⟨1658,2849⟩,⟨1148,874⟩,⟨426,417⟩],[⟨79,(-241)⟩,⟨582,(-1065)⟩,⟨883,152⟩,⟨457,(-265)⟩,⟨417,(-9)⟩],[⟨(-860),(-3604)⟩,⟨641,88⟩,⟨(-589),(-116)⟩,⟨(-9),(-426)⟩],[⟨(-340),(-242)⟩,⟨(-449),1181⟩,⟨274,1148⟩,⟨9,426⟩],[⟨33,756⟩,⟨722,457⟩,⟨426,417⟩],[⟨40,(-256)⟩,⟨417,(-9)⟩],[⟨(-9),(-426)⟩]]

without_editor_info theorem bezout_47 (x y : ℤ) :
    value F x y * value bezA_47 x y + values x y 10 * value bezB_47 x y +
      values x y 17 * value bezC_47 x y = (2 : Eisenstein) :=
  bezout F (nodes 10) (nodes 17) bezA_47 bezB_47 bezC_47 2 (by decide +kernel) x y

without_editor_info def bezA_48 : Poly := [[⟨1,0⟩]]

without_editor_info def bezB_48 : Poly := [[⟨1,2⟩,⟨0,0⟩,⟨1,0⟩],[⟨0,1⟩],[⟨0,1⟩],[⟨0,1⟩]]

without_editor_info def bezC_48 : Poly := [[⟨0,(-2)⟩],[⟨0,(-1)⟩],[⟨0,(-1)⟩],[⟨0,(-1)⟩]]

without_editor_info theorem bezout_48 (x y : ℤ) :
    value F x y * value bezA_48 x y + values x y 11 * value bezB_48 x y +
      values x y 16 * value bezC_48 x y = (3 : Eisenstein) :=
  bezout F (nodes 11) (nodes 16) bezA_48 bezB_48 bezC_48 3 (by decide +kernel) x y

without_editor_info def bezA_49 : Poly := [[⟨3,0⟩]]

without_editor_info def bezB_49 : Poly := [[⟨(-1),1⟩,⟨6,3⟩,⟨5,4⟩,⟨2,1⟩],[⟨(-3),0⟩,⟨(-6),0⟩,⟨(-3),0⟩],[⟨3,0⟩,⟨3,0⟩],[⟨(-3),0⟩]]

without_editor_info def bezC_49 : Poly := [[⟨2,1⟩,⟨6,3⟩,⟨8,4⟩,⟨2,1⟩]]

without_editor_info theorem bezout_49 (x y : ℤ) :
    value F x y * value bezA_49 x y + values x y 12 * value bezB_49 x y +
      values x y 15 * value bezC_49 x y = (3 : Eisenstein) :=
  bezout F (nodes 12) (nodes 15) bezA_49 bezB_49 bezC_49 3 (by decide +kernel) x y

without_editor_info def bezA_50 : Poly := [[⟨0,(-1)⟩]]

without_editor_info def bezB_50 : Poly := [[⟨2,1⟩,⟨0,0⟩,⟨1,1⟩,⟨1,1⟩],[⟨0,0⟩,⟨0,0⟩,⟨0,1⟩],[⟨0,0⟩,⟨0,1⟩],[⟨0,1⟩]]

without_editor_info def bezC_50 : Poly := [[⟨(-2),(-2)⟩,⟨0,0⟩,⟨0,(-1)⟩,⟨(-1),(-1)⟩]]

without_editor_info theorem bezout_50 (x y : ℤ) :
    value F x y * value bezA_50 x y + values x y 13 * value bezB_50 x y +
      values x y 15 * value bezC_50 x y = (2 : Eisenstein) :=
  bezout F (nodes 13) (nodes 15) bezA_50 bezB_50 bezC_50 2 (by decide +kernel) x y

without_editor_info def bezA_51 : Poly := [[⟨0,(-1)⟩]]

without_editor_info def bezB_51 : Poly := [[⟨2,1⟩,⟨0,2⟩,⟨1,1⟩,⟨0,1⟩,⟨0,1⟩],[⟨0,0⟩,⟨0,0⟩,⟨0,1⟩],[⟨0,0⟩,⟨0,1⟩],[⟨0,1⟩]]

without_editor_info def bezC_51 : Poly := [[⟨0,2⟩,⟨0,0⟩,⟨(-1),0⟩,⟨0,1⟩]]

without_editor_info theorem bezout_51 (x y : ℤ) :
    value F x y * value bezA_51 x y + values x y 13 * value bezB_51 x y +
      values x y 18 * value bezC_51 x y = (2 : Eisenstein) :=
  bezout F (nodes 13) (nodes 18) bezA_51 bezB_51 bezC_51 2 (by decide +kernel) x y

without_editor_info def bezA_52 : Poly := []

without_editor_info def bezB_52 : Poly := [[⟨0,0⟩,⟨1,0⟩],[⟨1,1⟩]]

without_editor_info def bezC_52 : Poly := [[⟨1,0⟩]]

without_editor_info theorem bezout_52 (x y : ℤ) :
    value F x y * value bezA_52 x y + values x y 13 * value bezB_52 x y +
      values x y 19 * value bezC_52 x y = (1 : Eisenstein) :=
  bezout F (nodes 13) (nodes 19) bezA_52 bezB_52 bezC_52 1 (by decide +kernel) x y

without_editor_info def bezA_53 : Poly := [[⟨1,1⟩]]

without_editor_info def bezB_53 : Poly := [[⟨0,2⟩,⟨0,(-1)⟩,⟨1,1⟩],[⟨1,0⟩],[⟨1,1⟩],[⟨0,1⟩]]

without_editor_info def bezC_53 : Poly := [[],[⟨(-1),0⟩],[⟨(-1),(-1)⟩],[⟨0,(-1)⟩]]

without_editor_info theorem bezout_53 (x y : ℤ) :
    value F x y * value bezA_53 x y + values x y 14 * value bezB_53 x y +
      values x y 15 * value bezC_53 x y = (4 : Eisenstein) :=
  bezout F (nodes 14) (nodes 15) bezA_53 bezB_53 bezC_53 4 (by decide +kernel) x y

without_editor_info def bezA_54 : Poly := []

without_editor_info def bezB_54 : Poly := [[⟨0,0⟩,⟨1,0⟩]]

without_editor_info def bezC_54 : Poly := [[⟨1,0⟩]]

without_editor_info theorem bezout_54 (x y : ℤ) :
    value F x y * value bezA_54 x y + values x y 15 * value bezB_54 x y +
      values x y 17 * value bezC_54 x y = (1 : Eisenstein) :=
  bezout F (nodes 15) (nodes 17) bezA_54 bezB_54 bezC_54 1 (by decide +kernel) x y

without_editor_info def bezA_55 : Poly := [[⟨1,(-1)⟩,⟨2,2⟩],[],[],[],[⟨(-1),(-1)⟩]]

without_editor_info def bezB_55 : Poly := [[⟨11,(-1)⟩,⟨13,3⟩,⟨8,4⟩,⟨5,2⟩],[⟨(-1),(-3)⟩,⟨(-2),(-6)⟩,⟨(-1),(-3)⟩],[⟨(-3),(-2)⟩,⟨(-3),(-2)⟩],[⟨(-2),1⟩],[⟨3,(-1)⟩,⟨3,(-1)⟩,⟨2,0⟩,⟨1,0⟩],[⟨(-1),(-1)⟩,⟨(-2),(-2)⟩,⟨(-1),(-1)⟩],[⟨(-1),0⟩,⟨(-1),0⟩],[⟨0,1⟩]]

without_editor_info def bezC_55 : Poly := [[⟨10,11⟩,⟨10,8⟩,⟨3,0⟩],[],[],[],[⟨4,3⟩,⟨4,2⟩,⟨1,0⟩]]

without_editor_info theorem bezout_55 (x y : ℤ) :
    value F x y * value bezA_55 x y + values x y 15 * value bezB_55 x y +
      values x y 18 * value bezC_55 x y = (2 : Eisenstein) :=
  bezout F (nodes 15) (nodes 18) bezA_55 bezB_55 bezC_55 2 (by decide +kernel) x y

without_editor_info def bezA_56 : Poly := [[⟨9,9⟩]]

without_editor_info def bezB_56 : Poly := [[⟨(-1),8⟩,⟨(-13),(-13)⟩,⟨(-11),(-7)⟩,⟨(-15),(-6)⟩,⟨(-3),(-6)⟩],[⟨8,18⟩,⟨5,1⟩,⟨12,0⟩,⟨3,6⟩],[⟨9,9⟩,⟨0,9⟩],[⟨9,0⟩]]

without_editor_info def bezC_56 : Poly := [[⟨(-8),(-9)⟩,⟨(-23),(-1)⟩,⟨(-21),(-9)⟩,⟨(-3),(-6)⟩]]

without_editor_info theorem bezout_56 (x y : ℤ) :
    value F x y * value bezA_56 x y + values x y 16 * value bezB_56 x y +
      values x y 19 * value bezC_56 x y = (2 : Eisenstein) :=
  bezout F (nodes 16) (nodes 19) bezA_56 bezB_56 bezC_56 2 (by decide +kernel) x y

without_editor_info def bezA_57 : Poly := [[⟨12,8⟩,⟨(-18),(-61)⟩,⟨13,29⟩,⟨(-35),(-5)⟩,⟨(-18),(-13)⟩],[⟨68,98⟩,⟨(-56),(-32)⟩],[],[⟨17,(-8)⟩],[⟨18,13⟩]]

without_editor_info def bezB_57 : Poly := [[⟨(-84),(-44)⟩,⟨(-141),(-24)⟩,⟨(-67),18⟩,⟨(-71),5⟩,⟨(-36),20⟩,⟨47,11⟩,⟨14,8⟩,⟨16,(-12)⟩],[⟨(-44),0⟩,⟨(-30),68⟩,⟨44,42⟩],[],[⟨78,5⟩,⟨51,17⟩,⟨15,6⟩,⟨(-14),(-8)⟩,⟨(-16),12⟩],[⟨(-43),(-37)⟩,⟨(-31),(-8)⟩,⟨18,13⟩],[⟨(-10),(-36)⟩]]

without_editor_info def bezC_57 : Poly := [[⟨24,(-56)⟩,⟨92,(-43)⟩,⟨46,(-107)⟩,⟨89,(-60)⟩,⟨72,20⟩,⟨(-9),24⟩,⟨(-2),20⟩,⟨(-16),12⟩],[⟨(-108),(-164)⟩,⟨(-29),(-98)⟩,⟨(-82),(-119)⟩,⟨(-58),(-93)⟩,⟨37,14⟩,⟨6,14⟩,⟨28,16⟩],[⟨56,(-30)⟩,⟨81,98⟩,⟨(-33),31⟩,⟨(-7),(-4)⟩,⟨(-8),6⟩,⟨(-12),(-28)⟩],[⟨17,(-19)⟩],[⟨(-15),(-54)⟩,⟨53,18⟩],[⟨(-8),(-25)⟩,⟨18,13⟩],[⟨13,(-5)⟩]]

without_editor_info theorem bezout_57 (x y : ℤ) :
    value F x y * value bezA_57 x y + values x y 18 * value bezB_57 x y +
      values x y 19 * value bezC_57 x y = (4 : Eisenstein) :=
  bezout F (nodes 18) (nodes 19) bezA_57 bezB_57 bezC_57 4 (by decide +kernel) x y

without_editor_info def supportNumber : Eisenstein := 6

without_editor_info theorem constant_support : ∀ i : Fin 20, constants i * (![⟨54,0⟩,⟨0,54⟩,⟨(-54),(-54)⟩,⟨(-108),(-108)⟩,⟨54,0⟩,⟨(-108),(-108)⟩,⟨108,0⟩,⟨216,0⟩,⟨54,0⟩,⟨(-36),(-72)⟩,⟨108,0⟩,⟨(-216),(-216)⟩,⟨(-18),(-36)⟩,⟨(-216),(-216)⟩,⟨(-108),(-108)⟩,⟨0,(-36)⟩,⟨36,36⟩,⟨216,0⟩,⟨0,216⟩,⟨0,216⟩]) i = supportNumber^3 := by decide +kernel

without_editor_info def starDen : Fin 20 → Eisenstein := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,3]

without_editor_info def bezDen : Fin 58 → Eisenstein := ![6,2,6,12,2,2,2,2,2,2,2,4,2,4,4,1,1,12,2,3,2,12,8,2,2,4,1,2,1,4,2,1,6,3,2,4,1,1,1,12,6,6,4,4,4,1,8,2,3,3,2,2,1,4,1,2,2,4]

without_editor_info theorem star_support : ∀ i : Fin 20, starDen i * (![216,216,216,216,216,216,216,216,216,216,216,216,216,216,216,216,216,216,216,72]) i = supportNumber^3 := by decide +kernel

without_editor_info theorem bez_support : ∀ e : Fin 58, bezDen e * (![36,108,36,18,108,108,108,108,108,108,108,54,108,54,54,216,216,18,108,72,108,18,27,108,108,54,216,108,216,54,108,216,36,72,108,54,216,216,216,18,36,36,54,54,54,216,27,108,72,72,108,108,216,54,216,108,108,54]) e = supportNumber^3 := by decide +kernel

without_editor_info theorem outside {x y : ℤ} (hf : equation x y = 0) (π : Eisenstein) [Fact (Prime π)]
    (h3 : ¬ π ∣ 3) (hN : ¬ π ∣ supportNumber) : graphSum edges (values x y) constants (tame π h3) = 0 := by
  have hc : ∀ i, ¬ π ∣ constants i := fun i => not_dvd_of_support π supportNumber _ _ 3 hN (constant_support i)
  have hs : ∀ i, ¬ π ∣ starDen i := fun i => not_dvd_of_support π supportNumber _ _ 3 hN (star_support i)
  have hb : ∀ e, ¬ π ∣ bezDen e := fun e => not_dvd_of_support π supportNumber _ _ 3 hN (bez_support e)
  apply graph_tame_vanish_lists edges (values x y) constants neighbors adjacency_checked π h3 hc
  · intro i hi
    rw [adjacency_checked]
    apply neighborList_not_dvd edges (values x y) π ?_ i hi
    intro e
    fin_cases e
    · exact separate_of_identity π (curve_zero hf) (hb 0) (bezout_0 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 1) (bezout_1 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 2) (bezout_2 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 3) (bezout_3 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 4) (bezout_4 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 5) (bezout_5 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 6) (bezout_6 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 7) (bezout_7 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 8) (bezout_8 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 9) (bezout_9 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 10) (bezout_10 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 11) (bezout_11 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 12) (bezout_12 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 13) (bezout_13 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 14) (bezout_14 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 15) (bezout_15 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 16) (bezout_16 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 17) (bezout_17 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 18) (bezout_18 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 19) (bezout_19 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 20) (bezout_20 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 21) (bezout_21 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 22) (bezout_22 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 23) (bezout_23 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 24) (bezout_24 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 25) (bezout_25 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 26) (bezout_26 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 27) (bezout_27 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 28) (bezout_28 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 29) (bezout_29 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 30) (bezout_30 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 31) (bezout_31 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 32) (bezout_32 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 33) (bezout_33 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 34) (bezout_34 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 35) (bezout_35 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 36) (bezout_36 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 37) (bezout_37 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 38) (bezout_38 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 39) (bezout_39 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 40) (bezout_40 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 41) (bezout_41 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 42) (bezout_42 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 43) (bezout_43 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 44) (bezout_44 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 45) (bezout_45 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 46) (bezout_46 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 47) (bezout_47 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 48) (bezout_48 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 49) (bezout_49 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 50) (bezout_50 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 51) (bezout_51 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 52) (bezout_52 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 53) (bezout_53 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 54) (bezout_54 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 55) (bezout_55 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 56) (bezout_56 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 57) (bezout_57 x y)
  · intro i hi
    fin_cases i
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 0) (star_0 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 1) (star_1 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 2) (star_2 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 3) (star_3 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 4) (star_4 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 5) (star_5 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 6) (star_6 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 7) (star_7 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 8) (star_8 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 9) (star_9 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 10) (star_10 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 11) (star_11 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 12) (star_12 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 13) (star_13 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 14) (star_14 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 15) (star_15 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 16) (star_16 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 17) (star_17 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 18) (star_18 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 19) (star_19 x y)

end GraphCert.Generated.g5786bb6f19cbbfc7842a018a.Proof



set_option Elab.async false

open CubicSpecial

open GraphCert.Cubic

namespace GraphCert.Generated.g5786bb6f19cbbfc7842a018a.Proof.At2

without_editor_info instance : Fact (Nat.Prime 2) := ⟨by decide⟩

without_editor_info instance : Fact (Prime (2 : Eisenstein)) := ⟨prime_integer_of_mod_three (by decide) (by decide)⟩

without_editor_info instance : Fact (Prime ((2 : ℕ) : Eisenstein)) := ⟨by simpa only [Nat.cast_ofNat] using (inferInstance : Fact (Prime (2 : Eisenstein))).out⟩

without_editor_info theorem away_three : ¬ (2 : Eisenstein) ∣ 3 := primary_prime_away_three (inferInstance : Fact (Prime (2 : Eisenstein))).out ⟨1, by decide⟩

without_editor_info def constantCertificates : Fin 20 → TameCertificate := (fun i => (#[⟨2,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨2,⟨(-1),(-1)⟩,⟨0,1⟩,⟨0,0⟩,2,⟨2,2⟩⟩,⟨2,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨1,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨2,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨1,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨1,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨2,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨1,⟨1,2⟩,⟨1,0⟩,⟨0,(-1)⟩,0,⟨0,1⟩⟩,⟨1,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨2,⟨1,2⟩,⟨1,0⟩,⟨0,(-1)⟩,0,⟨0,1⟩⟩,⟨0,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨1,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨1,⟨3,3⟩,⟨0,1⟩,⟨2,0⟩,2,⟨2,2⟩⟩,⟨1,⟨0,(-3)⟩,⟨1,1⟩,⟨(-1),0⟩,1,⟨0,0⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨(-1),(-1)⟩,⟨0,1⟩,⟨0,0⟩,2,⟨2,2⟩⟩,⟨0,⟨(-1),(-1)⟩,⟨0,1⟩,⟨0,0⟩,2,⟨2,2⟩⟩] : Array (TameCertificate))[i.val]'(by simpa using i.isLt))

without_editor_info theorem constants_checked : ∀ i : Fin 20, (constantCertificates i).check 2 (constants i) := by decide +kernel

without_editor_info def envelopes0 : Fin 20 → WildEnvelope := (fun i => (#[⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![1,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![1,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info def certificates0 : Fin 20 → TameCertificate := (fun i => (#[⟨0,⟨1,1⟩,⟨0,1⟩,⟨1,0⟩,2,⟨1,1⟩⟩,⟨0,⟨1,1⟩,⟨0,1⟩,⟨1,0⟩,2,⟨1,1⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨1,1⟩,⟨0,1⟩,⟨1,0⟩,2,⟨1,1⟩⟩,⟨0,⟨1,1⟩,⟨0,1⟩,⟨1,0⟩,2,⟨1,1⟩⟩,⟨0,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨0,⟨1,1⟩,⟨0,1⟩,⟨1,0⟩,2,⟨1,1⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨1,1⟩,⟨0,1⟩,⟨1,0⟩,2,⟨1,1⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨0,⟨1,1⟩,⟨0,1⟩,⟨1,0⟩,2,⟨1,1⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩] : Array (TameCertificate))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks0 : ∀ i : Fin 20, inertEnvelopeCheck (envelopes0 i) 2 (residueE (2^1) (values 1 0 i)) 1 (real i) (certificates0 i) := by decide +kernel

without_editor_info theorem linear0 : ∀ i : Fin 20, ∀ j : Fin 4,
    tameForm ((envelopes0 i).directions j)
      (graphStar edges (fun i => (envelopes0 i).base) (fun i => (constantCertificates i).vector) i) = 0 := by
  have h : ∀ i : Fin 20, ∀ j : Fin 4, (envelopes0 i).directions j = 0 ∨
      tameForm ((envelopes0 i).directions j)
        (graphStar edges (fun i => (envelopes0 i).base) (fun i => (constantCertificates i).vector) i) = 0 := by
    simp only [graphStar_neighbors edges neighbors adjacency_checked]
    decide +kernel
  intro i j
  rcases h i j with hz | hz
  · simp [hz, tameForm]
  · exact hz

without_editor_info theorem cross0 : ∀ e : Fin 58, ∀ j k : Fin 4,
    tameForm ((envelopes0 (edges e).src).directions j) ((envelopes0 (edges e).dst).directions k) = 0 := by
  have h := listEdges_all (m := 58) edgeList (by decide)
    (fun e => (envelopes0 e.src).directions = 0 ∨
      (envelopes0 e.dst).directions = 0 ∨
      (∀ j k : Fin 4, tameForm ((envelopes0 e.src).directions j) ((envelopes0 e.dst).directions k) = 0))
    (by decide +kernel)
  intro e j k
  have h := h e
  change (envelopes0 (edges e).src).directions = 0 ∨
    (envelopes0 (edges e).dst).directions = 0 ∨
    (∀ j k : Fin 4, tameForm ((envelopes0 (edges e).src).directions j) ((envelopes0 (edges e).dst).directions k) = 0) at h
  rcases h with hz | hz | hz
  · rw [hz]; simp [tameForm]
  · rw [hz]; simp [tameForm]
  · exact hz j k

without_editor_info theorem value0 : vectorGraph edges (fun i => (envelopes0 i).base) (fun i => (constantCertificates i).vector) tameBilinear = 2 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell0 {x y : ℤ} (hf : equation x y = 0)
    (hx : (2 : ℤ)^1 ∣ x-1) (hy : (2 : ℤ)^1 ∣ y-0) : graphSum edges (values x y) constants (tame (2 : Eisenstein) away_three) = 2 :=
  inert_cell edges values constants real values_congr values_real 2 away_three (by decide) 1 0 1 envelopes0 constantCertificates certificates0 2 constants_checked checks0 linear0 cross0 value0 (all_nonzero hf) hx hy

without_editor_info def envelopes1 : Fin 20 → WildEnvelope := (fun i => (#[⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info def certificates1 : Fin 20 → TameCertificate := (fun i => (#[⟨0,⟨1,1⟩,⟨0,1⟩,⟨1,0⟩,2,⟨1,1⟩⟩,⟨0,⟨3,3⟩,⟨0,1⟩,⟨2,0⟩,2,⟨2,2⟩⟩,⟨1,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨3,1⟩,⟨0,1⟩,⟨1,(-1)⟩,2,⟨2,1⟩⟩,⟨0,⟨3,0⟩,⟨1,0⟩,⟨(-1),0⟩,0,⟨1,0⟩⟩,⟨0,⟨2,1⟩,⟨1,1⟩,⟨0,(-1)⟩,1,⟨1,0⟩⟩,⟨0,⟨2,3⟩,⟨1,1⟩,⟨1,(-1)⟩,1,⟨1,1⟩⟩,⟨0,⟨1,3⟩,⟨0,1⟩,⟨2,1⟩,2,⟨1,2⟩⟩,⟨0,⟨2,1⟩,⟨1,1⟩,⟨0,(-1)⟩,1,⟨1,0⟩⟩,⟨1,⟨1,1⟩,⟨0,1⟩,⟨1,0⟩,2,⟨1,1⟩⟩,⟨0,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨0,⟨3,0⟩,⟨1,0⟩,⟨(-1),0⟩,0,⟨1,0⟩⟩,⟨0,⟨3,0⟩,⟨1,0⟩,⟨(-1),0⟩,0,⟨1,0⟩⟩,⟨1,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨2,3⟩,⟨1,1⟩,⟨1,(-1)⟩,1,⟨1,1⟩⟩,⟨0,⟨3,2⟩,⟨1,0⟩,⟨(-1),(-1)⟩,0,⟨1,1⟩⟩,⟨0,⟨2,3⟩,⟨1,1⟩,⟨1,(-1)⟩,1,⟨1,1⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨2,1⟩,⟨1,1⟩,⟨0,(-1)⟩,1,⟨1,0⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩] : Array (TameCertificate))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks1 : ∀ i : Fin 20, inertEnvelopeCheck (envelopes1 i) 2 (residueE (2^2) (values 2 0 i)) 2 (real i) (certificates1 i) := by decide +kernel

without_editor_info theorem zeroDirections1 : ∀ i : Fin 20, ∀ j : Fin 4,
    (envelopes1 i).directions j=0 := by decide +kernel

without_editor_info theorem linear1 : ∀ i : Fin 20, ∀ j : Fin 4,
    tameForm ((envelopes1 i).directions j)
      (graphStar edges (fun i => (envelopes1 i).base) (fun i => (constantCertificates i).vector) i) = 0 := by
  intro i k
  rw [zeroDirections1 i k]
  simp [tameForm]

without_editor_info theorem cross1 : ∀ e : Fin 58, ∀ j k : Fin 4,
    tameForm ((envelopes1 (edges e).src).directions j) ((envelopes1 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections1 ((edges e).src) i]
  simp [tameForm]

without_editor_info theorem value1 : vectorGraph edges (fun i => (envelopes1 i).base) (fun i => (constantCertificates i).vector) tameBilinear = 2 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell1 {x y : ℤ} (hf : equation x y = 0)
    (hx : (2 : ℤ)^2 ∣ x-2) (hy : (2 : ℤ)^2 ∣ y-0) : graphSum edges (values x y) constants (tame (2 : Eisenstein) away_three) = 2 :=
  inert_cell edges values constants real values_congr values_real 2 away_three (by decide) 2 0 2 envelopes1 constantCertificates certificates1 2 constants_checked checks1 linear1 cross1 value1 (all_nonzero hf) hx hy

without_editor_info def envelopes2 : Fin 20 → WildEnvelope := (fun i => (#[⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info def certificates2 : Fin 20 → TameCertificate := (fun i => (#[⟨0,⟨3,1⟩,⟨0,1⟩,⟨1,(-1)⟩,2,⟨2,1⟩⟩,⟨0,⟨1,7⟩,⟨0,1⟩,⟨4,3⟩,2,⟨1,2⟩⟩,⟨2,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨5,1⟩,⟨0,1⟩,⟨1,(-2)⟩,2,⟨1,1⟩⟩,⟨0,⟨5,0⟩,⟨1,0⟩,⟨(-2),0⟩,0,⟨0,0⟩⟩,⟨0,⟨4,1⟩,⟨1,1⟩,⟨(-1),(-2)⟩,1,⟨0,0⟩⟩,⟨0,⟨4,7⟩,⟨1,1⟩,⟨2,(-2)⟩,1,⟨0,1⟩⟩,⟨0,⟨3,7⟩,⟨0,1⟩,⟨4,2⟩,2,⟨2,2⟩⟩,⟨0,⟨6,1⟩,⟨1,1⟩,⟨(-2),(-3)⟩,1,⟨1,0⟩⟩,⟨2,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨4,3⟩,⟨1,1⟩,⟨0,(-2)⟩,1,⟨0,1⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨3,0⟩,⟨1,0⟩,⟨(-1),0⟩,0,⟨1,0⟩⟩,⟨1,⟨3,0⟩,⟨1,0⟩,⟨(-1),0⟩,0,⟨1,0⟩⟩,⟨0,⟨0,7⟩,⟨1,1⟩,⟨4,0⟩,1,⟨0,1⟩⟩,⟨0,⟨1,4⟩,⟨1,0⟩,⟨0,(-2)⟩,0,⟨0,0⟩⟩,⟨0,⟨6,5⟩,⟨1,1⟩,⟨0,(-3)⟩,1,⟨1,0⟩⟩,⟨0,⟨3,0⟩,⟨1,0⟩,⟨(-1),0⟩,0,⟨1,0⟩⟩,⟨0,⟨0,5⟩,⟨1,1⟩,⟨3,0⟩,1,⟨0,0⟩⟩,⟨0,⟨5,0⟩,⟨1,0⟩,⟨(-2),0⟩,0,⟨0,0⟩⟩] : Array (TameCertificate))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks2 : ∀ i : Fin 20, inertEnvelopeCheck (envelopes2 i) 2 (residueE (2^3) (values 4 6 i)) 3 (real i) (certificates2 i) := by decide +kernel

without_editor_info theorem zeroDirections2 : ∀ i : Fin 20, ∀ j : Fin 4,
    (envelopes2 i).directions j=0 := by decide +kernel

without_editor_info theorem linear2 : ∀ i : Fin 20, ∀ j : Fin 4,
    tameForm ((envelopes2 i).directions j)
      (graphStar edges (fun i => (envelopes2 i).base) (fun i => (constantCertificates i).vector) i) = 0 := by
  intro i k
  rw [zeroDirections2 i k]
  simp [tameForm]

without_editor_info theorem cross2 : ∀ e : Fin 58, ∀ j k : Fin 4,
    tameForm ((envelopes2 (edges e).src).directions j) ((envelopes2 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections2 ((edges e).src) i]
  simp [tameForm]

without_editor_info theorem value2 : vectorGraph edges (fun i => (envelopes2 i).base) (fun i => (constantCertificates i).vector) tameBilinear = 2 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell2 {x y : ℤ} (hf : equation x y = 0)
    (hx : (2 : ℤ)^3 ∣ x-4) (hy : (2 : ℤ)^3 ∣ y-6) : graphSum edges (values x y) constants (tame (2 : Eisenstein) away_three) = 2 :=
  inert_cell edges values constants real values_congr values_real 2 away_three (by decide) 4 6 3 envelopes2 constantCertificates certificates2 2 constants_checked checks2 linear2 cross2 value2 (all_nonzero hf) hx hy

without_editor_info def envelopes3 : Fin 20 → WildEnvelope := (fun i => (#[⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![1,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info def certificates3 : Fin 20 → TameCertificate := (fun i => (#[⟨0,⟨7,1⟩,⟨0,1⟩,⟨1,(-3)⟩,2,⟨2,1⟩⟩,⟨0,⟨5,7⟩,⟨0,1⟩,⟨4,1⟩,2,⟨1,2⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨1,1⟩,⟨0,1⟩,⟨1,0⟩,2,⟨1,1⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨0,⟨0,7⟩,⟨1,1⟩,⟨4,0⟩,1,⟨0,1⟩⟩,⟨0,⟨7,7⟩,⟨0,1⟩,⟨4,0⟩,2,⟨2,2⟩⟩,⟨0,⟨6,1⟩,⟨1,1⟩,⟨(-2),(-3)⟩,1,⟨1,0⟩⟩,⟨2,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨0,⟨4,7⟩,⟨1,1⟩,⟨2,(-2)⟩,1,⟨0,1⟩⟩,⟨0,⟨5,0⟩,⟨1,0⟩,⟨(-2),0⟩,0,⟨0,0⟩⟩,⟨0,⟨3,0⟩,⟨1,0⟩,⟨(-1),0⟩,0,⟨1,0⟩⟩,⟨1,⟨3,0⟩,⟨1,0⟩,⟨(-1),0⟩,0,⟨1,0⟩⟩,⟨0,⟨4,7⟩,⟨1,1⟩,⟨2,(-2)⟩,1,⟨0,1⟩⟩,⟨0,⟨5,0⟩,⟨1,0⟩,⟨(-2),0⟩,0,⟨0,0⟩⟩,⟨0,⟨6,1⟩,⟨1,1⟩,⟨(-2),(-3)⟩,1,⟨1,0⟩⟩,⟨0,⟨7,0⟩,⟨1,0⟩,⟨(-3),0⟩,0,⟨1,0⟩⟩,⟨0,⟨4,5⟩,⟨1,1⟩,⟨1,(-2)⟩,1,⟨0,0⟩⟩,⟨0,⟨5,0⟩,⟨1,0⟩,⟨(-2),0⟩,0,⟨0,0⟩⟩] : Array (TameCertificate))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks3 : ∀ i : Fin 20, inertEnvelopeCheck (envelopes3 i) 2 (residueE (2^3) (values 0 2 i)) 3 (real i) (certificates3 i) := by decide +kernel

without_editor_info theorem noLoops : ∀ e : Fin 58, (edges e).src ≠ (edges e).dst := by
  exact listEdges_all (m := 58) edgeList (by decide)
    (fun e => e.src ≠ e.dst) (by decide +kernel)

without_editor_info theorem fixedDirections3 : ∀ i : Fin 20,
    i=2 ∨ (envelopes3 i).directions=0 := by decide +kernel

without_editor_info theorem linear3 : ∀ i : Fin 20, ∀ j : Fin 4,
    tameForm ((envelopes3 i).directions j)
      (graphStar edges (fun i => (envelopes3 i).base) (fun i => (constantCertificates i).vector) i) = 0 := by
  have h : ∀ k : Fin 4, tameForm ((envelopes3 2).directions k)
      (graphStar edges (fun i => (envelopes3 i).base) (fun i => (constantCertificates i).vector) 2)=0 := by
    simp only [graphStar_neighbors edges neighbors adjacency_checked]
    decide +kernel
  intro i k
  rcases fixedDirections3 i with rfl | hz
  · exact h k
  · rw [hz]; simp [tameForm]

without_editor_info theorem cross3 : ∀ e : Fin 58, ∀ j k : Fin 4,
    tameForm ((envelopes3 (edges e).src).directions j) ((envelopes3 (edges e).dst).directions k) = 0 := by
  intro e i k
  rcases fixedDirections3 (edges e).src with hs | hz
  · rcases fixedDirections3 (edges e).dst with ht | hz
    · exact False.elim (noLoops e (hs.trans ht.symm))
    · rw [hz]; simp [tameForm]
  · rw [hz]; simp [tameForm]

without_editor_info theorem value3 : vectorGraph edges (fun i => (envelopes3 i).base) (fun i => (constantCertificates i).vector) tameBilinear = 2 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell3 {x y : ℤ} (hf : equation x y = 0)
    (hx : (2 : ℤ)^3 ∣ x-0) (hy : (2 : ℤ)^3 ∣ y-2) : graphSum edges (values x y) constants (tame (2 : Eisenstein) away_three) = 2 :=
  inert_cell edges values constants real values_congr values_real 2 away_three (by decide) 0 2 3 envelopes3 constantCertificates certificates3 2 constants_checked checks3 linear3 cross3 value3 (all_nonzero hf) hx hy

without_editor_info noncomputable def localSum (x y : ℤ) : ZMod 3 := graphSum edges (values x y) constants (tame (2 : Eisenstein) away_three)

without_editor_info def residues : Fin 4 → ℤ × ℤ × ℕ := (fun i => (#[(1,0,1),(2,0,2),(4,6,3),(0,2,3)] : Array (ℤ × ℤ × ℕ))[i.val]'(by simpa using i.isLt))

without_editor_info def targets : Fin 4 → ZMod 3 := (fun i => (#[2,2,2,2] : Array (ZMod 3))[i.val]'(by simpa using i.isLt))

without_editor_info theorem cell_value (i : Fin 4) {x y : ℤ} (hf : equation x y = 0)
    (hx : (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1)
    (hy : (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1) : localSum x y = targets i := by
  fin_cases i
  · exact cell0 hf hx hy
  · exact cell1 hf hx hy
  · exact cell2 hf hx hy
  · exact cell3 hf hx hy

without_editor_info theorem covered0 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (2 : ℤ)^1 ∣ x-1) (hy : (2 : ℤ)^1 ∣ y-0) : ∃ i : Fin 4, (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨0,hx,hy⟩

without_editor_info theorem covered1 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (2 : ℤ)^2 ∣ x-2) (hy : (2 : ℤ)^2 ∣ y-0) : ∃ i : Fin 4, (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨1,hx,hy⟩

without_editor_info theorem covered2 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (2 : ℤ)^3 ∣ x-4) (hy : (2 : ℤ)^3 ∣ y-6) : ∃ i : Fin 4, (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨2,hx,hy⟩

without_editor_info theorem covered3 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (2 : ℤ)^3 ∣ x-0) (hy : (2 : ℤ)^3 ∣ y-2) : ∃ i : Fin 4, (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨3,hx,hy⟩

without_editor_info theorem branch0 {x y : ℤ} (hf : equation x y = 0)
    (hx : (2 : ℤ)^2 ∣ x-0) (hy : (2 : ℤ)^2 ∣ y-2) : ∃ i : Fin 4, (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 4, (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    2 (by decide) 4 0 2 [(0,2),(4,6)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · intro X Y hF hX hY
    apply covered3 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered2 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch1 {x y : ℤ} (hf : equation x y = 0)
    (hx : (2 : ℤ)^1 ∣ x-0) (hy : (2 : ℤ)^1 ∣ y-0) : ∃ i : Fin 4, (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 4, (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    2 (by decide) 2 0 0 [(0,2),(2,0)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · intro X Y hF hX hY
    apply branch0 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered1 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch2 {x y : ℤ} (hf : equation x y = 0)
    (hx : (2 : ℤ)^0 ∣ x-0) (hy : (2 : ℤ)^0 ∣ y-0) : ∃ i : Fin 4, (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 4, (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    2 (by decide) 1 0 0 [(0,0),(1,0)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · intro X Y hF hX hY
    apply branch1 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered0 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem local_cover {x y : ℤ} (hf : equation x y = 0) : ∃ i : Fin 4, (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := branch2 hf (by simp) (by simp)

end GraphCert.Generated.g5786bb6f19cbbfc7842a018a.Proof.At2



set_option Elab.async false

open CubicSpecial

open GraphCert.Cubic

namespace GraphCert.Generated.g5786bb6f19cbbfc7842a018a.Proof.At3

without_editor_info def constantsClass : Fin 20 → WildVector := (fun i => (#[![0,0,2,0],![0,2,2,0],![0,1,2,0],![0,1,1,0],![0,0,2,0],![0,1,1,0],![0,0,1,0],![0,0,0,0],![0,0,2,0],![1,1,1,0],![0,0,1,0],![0,1,0,0],![1,1,2,0],![0,1,0,0],![0,1,1,0],![2,1,1,0],![2,0,1,0],![0,0,0,0],![0,2,0,0],![0,2,0,0]] : Array (WildVector))[i.val]'(by simpa using i.isLt))

without_editor_info theorem constants_checked : ∀ i : Fin 20, computeWildClass 32 (constants i) = some (constantsClass i) := by decide +kernel

without_editor_info def envelopes0 : Fin 20 → WildEnvelope := (fun i => (#[⟨![1,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,1],![![0,0,1,1],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks0 : ∀ i : Fin 20, wildEnvelopeCheck (envelopes0 i) (residueE (3^3) (values 25 14 i)) 3 (real i) := by decide +kernel

without_editor_info theorem noLoops : ∀ e : Fin 58, (edges e).src ≠ (edges e).dst := by
  exact listEdges_all (m := 58) edgeList (by decide)
    (fun e => e.src ≠ e.dst) (by decide +kernel)

without_editor_info theorem fixedDirections0 : ∀ i : Fin 20,
    i=16 ∨ (envelopes0 i).directions=0 := by decide +kernel

without_editor_info theorem linear0 : ∀ i : Fin 20, ∀ j : Fin 4,
    wildForm ((envelopes0 i).directions j)
      (graphStar edges (fun i => (envelopes0 i).base) constantsClass i) = 0 := by
  have h : ∀ k : Fin 4, wildForm ((envelopes0 16).directions k)
      (graphStar edges (fun i => (envelopes0 i).base) constantsClass 16)=0 := by
    simp only [graphStar_neighbors edges neighbors adjacency_checked]
    decide +kernel
  intro i k
  rcases fixedDirections0 i with rfl | hz
  · exact h k
  · rw [hz]; simp [wildForm]

without_editor_info theorem cross0 : ∀ e : Fin 58, ∀ j k : Fin 4,
    wildForm ((envelopes0 (edges e).src).directions j) ((envelopes0 (edges e).dst).directions k) = 0 := by
  intro e i k
  rcases fixedDirections0 (edges e).src with hs | hz
  · rcases fixedDirections0 (edges e).dst with ht | hz
    · exact False.elim (noLoops e (hs.trans ht.symm))
    · rw [hz]; simp [wildForm]
  · rw [hz]; simp [wildForm]

without_editor_info theorem value0 : vectorGraph edges (fun i => (envelopes0 i).base) constantsClass wildBilinear = 0 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell0 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-25) (hy : (3 : ℤ)^3 ∣ y-14) : graphSum edges (values x y) constants wild = 0 :=
  wild_cell edges values constants real values_congr values_real 25 14 3 envelopes0 constantsClass 0 constants_checked checks0 linear0 cross0 value0 (all_nonzero hf) hx hy

without_editor_info def envelopes1 : Fin 20 → WildEnvelope := (fun i => (#[⟨![1,1,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,2,0],![![0,0,1,1],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks1 : ∀ i : Fin 20, wildEnvelopeCheck (envelopes1 i) (residueE (3^3) (values 16 23 i)) 3 (real i) := by decide +kernel

without_editor_info theorem fixedDirections1 : ∀ i : Fin 20,
    i=16 ∨ (envelopes1 i).directions=0 := by decide +kernel

without_editor_info theorem linear1 : ∀ i : Fin 20, ∀ j : Fin 4,
    wildForm ((envelopes1 i).directions j)
      (graphStar edges (fun i => (envelopes1 i).base) constantsClass i) = 0 := by
  have h : ∀ k : Fin 4, wildForm ((envelopes1 16).directions k)
      (graphStar edges (fun i => (envelopes1 i).base) constantsClass 16)=0 := by
    simp only [graphStar_neighbors edges neighbors adjacency_checked]
    decide +kernel
  intro i k
  rcases fixedDirections1 i with rfl | hz
  · exact h k
  · rw [hz]; simp [wildForm]

without_editor_info theorem cross1 : ∀ e : Fin 58, ∀ j k : Fin 4,
    wildForm ((envelopes1 (edges e).src).directions j) ((envelopes1 (edges e).dst).directions k) = 0 := by
  intro e i k
  rcases fixedDirections1 (edges e).src with hs | hz
  · rcases fixedDirections1 (edges e).dst with ht | hz
    · exact False.elim (noLoops e (hs.trans ht.symm))
    · rw [hz]; simp [wildForm]
  · rw [hz]; simp [wildForm]

without_editor_info theorem value1 : vectorGraph edges (fun i => (envelopes1 i).base) constantsClass wildBilinear = 0 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell1 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-16) (hy : (3 : ℤ)^3 ∣ y-23) : graphSum edges (values x y) constants wild = 0 :=
  wild_cell edges values constants real values_congr values_real 16 23 3 envelopes1 constantsClass 0 constants_checked checks1 linear1 cross1 value1 (all_nonzero hf) hx hy

without_editor_info def envelopes2 : Fin 20 → WildEnvelope := (fun i => (#[⟨![1,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,1,1],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks2 : ∀ i : Fin 20, wildEnvelopeCheck (envelopes2 i) (residueE (3^3) (values 7 5 i)) 3 (real i) := by decide +kernel

without_editor_info theorem fixedDirections2 : ∀ i : Fin 20,
    i=16 ∨ (envelopes2 i).directions=0 := by decide +kernel

without_editor_info theorem linear2 : ∀ i : Fin 20, ∀ j : Fin 4,
    wildForm ((envelopes2 i).directions j)
      (graphStar edges (fun i => (envelopes2 i).base) constantsClass i) = 0 := by
  have h : ∀ k : Fin 4, wildForm ((envelopes2 16).directions k)
      (graphStar edges (fun i => (envelopes2 i).base) constantsClass 16)=0 := by
    simp only [graphStar_neighbors edges neighbors adjacency_checked]
    decide +kernel
  intro i k
  rcases fixedDirections2 i with rfl | hz
  · exact h k
  · rw [hz]; simp [wildForm]

without_editor_info theorem cross2 : ∀ e : Fin 58, ∀ j k : Fin 4,
    wildForm ((envelopes2 (edges e).src).directions j) ((envelopes2 (edges e).dst).directions k) = 0 := by
  intro e i k
  rcases fixedDirections2 (edges e).src with hs | hz
  · rcases fixedDirections2 (edges e).dst with ht | hz
    · exact False.elim (noLoops e (hs.trans ht.symm))
    · rw [hz]; simp [wildForm]
  · rw [hz]; simp [wildForm]

without_editor_info theorem value2 : vectorGraph edges (fun i => (envelopes2 i).base) constantsClass wildBilinear = 0 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell2 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-7) (hy : (3 : ℤ)^3 ∣ y-5) : graphSum edges (values x y) constants wild = 0 :=
  wild_cell edges values constants real values_congr values_real 7 5 3 envelopes2 constantsClass 0 constants_checked checks2 linear2 cross2 value2 (all_nonzero hf) hx hy

without_editor_info def envelopes3 : Fin 20 → WildEnvelope := (fun i => (#[⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,1,0],![1,1,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,1,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks3 : ∀ i : Fin 20, wildEnvelopeCheck (envelopes3 i) (residueE (3^3) (values 22 26 i)) 3 (real i) := by decide +kernel

without_editor_info theorem fixedDirections3 : ∀ i : Fin 20,
    i=11 ∨ (envelopes3 i).directions=0 := by decide +kernel

without_editor_info theorem linear3 : ∀ i : Fin 20, ∀ j : Fin 4,
    wildForm ((envelopes3 i).directions j)
      (graphStar edges (fun i => (envelopes3 i).base) constantsClass i) = 0 := by
  have h : ∀ k : Fin 4, wildForm ((envelopes3 11).directions k)
      (graphStar edges (fun i => (envelopes3 i).base) constantsClass 11)=0 := by
    simp only [graphStar_neighbors edges neighbors adjacency_checked]
    decide +kernel
  intro i k
  rcases fixedDirections3 i with rfl | hz
  · exact h k
  · rw [hz]; simp [wildForm]

without_editor_info theorem cross3 : ∀ e : Fin 58, ∀ j k : Fin 4,
    wildForm ((envelopes3 (edges e).src).directions j) ((envelopes3 (edges e).dst).directions k) = 0 := by
  intro e i k
  rcases fixedDirections3 (edges e).src with hs | hz
  · rcases fixedDirections3 (edges e).dst with ht | hz
    · exact False.elim (noLoops e (hs.trans ht.symm))
    · rw [hz]; simp [wildForm]
  · rw [hz]; simp [wildForm]

without_editor_info theorem value3 : vectorGraph edges (fun i => (envelopes3 i).base) constantsClass wildBilinear = 0 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell3 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-22) (hy : (3 : ℤ)^3 ∣ y-26) : graphSum edges (values x y) constants wild = 0 :=
  wild_cell edges values constants real values_congr values_real 22 26 3 envelopes3 constantsClass 0 constants_checked checks3 linear3 cross3 value3 (all_nonzero hf) hx hy

without_editor_info def envelopes4 : Fin 20 → WildEnvelope := (fun i => (#[⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,1,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,1,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks4 : ∀ i : Fin 20, wildEnvelopeCheck (envelopes4 i) (residueE (3^3) (values 13 8 i)) 3 (real i) := by decide +kernel

without_editor_info theorem fixedDirections4 : ∀ i : Fin 20,
    i=11 ∨ (envelopes4 i).directions=0 := by decide +kernel

without_editor_info theorem linear4 : ∀ i : Fin 20, ∀ j : Fin 4,
    wildForm ((envelopes4 i).directions j)
      (graphStar edges (fun i => (envelopes4 i).base) constantsClass i) = 0 := by
  have h : ∀ k : Fin 4, wildForm ((envelopes4 11).directions k)
      (graphStar edges (fun i => (envelopes4 i).base) constantsClass 11)=0 := by
    simp only [graphStar_neighbors edges neighbors adjacency_checked]
    decide +kernel
  intro i k
  rcases fixedDirections4 i with rfl | hz
  · exact h k
  · rw [hz]; simp [wildForm]

without_editor_info theorem cross4 : ∀ e : Fin 58, ∀ j k : Fin 4,
    wildForm ((envelopes4 (edges e).src).directions j) ((envelopes4 (edges e).dst).directions k) = 0 := by
  intro e i k
  rcases fixedDirections4 (edges e).src with hs | hz
  · rcases fixedDirections4 (edges e).dst with ht | hz
    · exact False.elim (noLoops e (hs.trans ht.symm))
    · rw [hz]; simp [wildForm]
  · rw [hz]; simp [wildForm]

without_editor_info theorem value4 : vectorGraph edges (fun i => (envelopes4 i).base) constantsClass wildBilinear = 0 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell4 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-13) (hy : (3 : ℤ)^3 ∣ y-8) : graphSum edges (values x y) constants wild = 0 :=
  wild_cell edges values constants real values_congr values_real 13 8 3 envelopes4 constantsClass 0 constants_checked checks4 linear4 cross4 value4 (all_nonzero hf) hx hy

without_editor_info def envelopes5 : Fin 20 → WildEnvelope := (fun i => (#[⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,1,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,1,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks5 : ∀ i : Fin 20, wildEnvelopeCheck (envelopes5 i) (residueE (3^3) (values 4 17 i)) 3 (real i) := by decide +kernel

without_editor_info theorem fixedDirections5 : ∀ i : Fin 20,
    i=11 ∨ (envelopes5 i).directions=0 := by decide +kernel

without_editor_info theorem linear5 : ∀ i : Fin 20, ∀ j : Fin 4,
    wildForm ((envelopes5 i).directions j)
      (graphStar edges (fun i => (envelopes5 i).base) constantsClass i) = 0 := by
  have h : ∀ k : Fin 4, wildForm ((envelopes5 11).directions k)
      (graphStar edges (fun i => (envelopes5 i).base) constantsClass 11)=0 := by
    simp only [graphStar_neighbors edges neighbors adjacency_checked]
    decide +kernel
  intro i k
  rcases fixedDirections5 i with rfl | hz
  · exact h k
  · rw [hz]; simp [wildForm]

without_editor_info theorem cross5 : ∀ e : Fin 58, ∀ j k : Fin 4,
    wildForm ((envelopes5 (edges e).src).directions j) ((envelopes5 (edges e).dst).directions k) = 0 := by
  intro e i k
  rcases fixedDirections5 (edges e).src with hs | hz
  · rcases fixedDirections5 (edges e).dst with ht | hz
    · exact False.elim (noLoops e (hs.trans ht.symm))
    · rw [hz]; simp [wildForm]
  · rw [hz]; simp [wildForm]

without_editor_info theorem value5 : vectorGraph edges (fun i => (envelopes5 i).base) constantsClass wildBilinear = 0 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell5 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-4) (hy : (3 : ℤ)^3 ∣ y-17) : graphSum edges (values x y) constants wild = 0 :=
  wild_cell edges values constants real values_congr values_real 4 17 3 envelopes5 constantsClass 0 constants_checked checks5 linear5 cross5 value5 (all_nonzero hf) hx hy

without_editor_info def envelopes6 : Fin 20 → WildEnvelope := (fun i => (#[⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks6 : ∀ i : Fin 20, wildEnvelopeCheck (envelopes6 i) (residueE (3^3) (values 19 2 i)) 3 (real i) := by decide +kernel

without_editor_info theorem zeroDirections6 : ∀ i : Fin 20, ∀ j : Fin 4,
    (envelopes6 i).directions j=0 := by decide +kernel

without_editor_info theorem linear6 : ∀ i : Fin 20, ∀ j : Fin 4,
    wildForm ((envelopes6 i).directions j)
      (graphStar edges (fun i => (envelopes6 i).base) constantsClass i) = 0 := by
  intro i k
  rw [zeroDirections6 i k]
  simp [wildForm]

without_editor_info theorem cross6 : ∀ e : Fin 58, ∀ j k : Fin 4,
    wildForm ((envelopes6 (edges e).src).directions j) ((envelopes6 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections6 ((edges e).src) i]
  simp [wildForm]

without_editor_info theorem value6 : vectorGraph edges (fun i => (envelopes6 i).base) constantsClass wildBilinear = 0 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell6 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-19) (hy : (3 : ℤ)^3 ∣ y-2) : graphSum edges (values x y) constants wild = 0 :=
  wild_cell edges values constants real values_congr values_real 19 2 3 envelopes6 constantsClass 0 constants_checked checks6 linear6 cross6 value6 (all_nonzero hf) hx hy

without_editor_info def envelopes7 : Fin 20 → WildEnvelope := (fun i => (#[⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks7 : ∀ i : Fin 20, wildEnvelopeCheck (envelopes7 i) (residueE (3^3) (values 10 11 i)) 3 (real i) := by decide +kernel

without_editor_info theorem zeroDirections7 : ∀ i : Fin 20, ∀ j : Fin 4,
    (envelopes7 i).directions j=0 := by decide +kernel

without_editor_info theorem linear7 : ∀ i : Fin 20, ∀ j : Fin 4,
    wildForm ((envelopes7 i).directions j)
      (graphStar edges (fun i => (envelopes7 i).base) constantsClass i) = 0 := by
  intro i k
  rw [zeroDirections7 i k]
  simp [wildForm]

without_editor_info theorem cross7 : ∀ e : Fin 58, ∀ j k : Fin 4,
    wildForm ((envelopes7 (edges e).src).directions j) ((envelopes7 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections7 ((edges e).src) i]
  simp [wildForm]

without_editor_info theorem value7 : vectorGraph edges (fun i => (envelopes7 i).base) constantsClass wildBilinear = 0 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell7 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-10) (hy : (3 : ℤ)^3 ∣ y-11) : graphSum edges (values x y) constants wild = 0 :=
  wild_cell edges values constants real values_congr values_real 10 11 3 envelopes7 constantsClass 0 constants_checked checks7 linear7 cross7 value7 (all_nonzero hf) hx hy

without_editor_info def envelopes8 : Fin 20 → WildEnvelope := (fun i => (#[⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks8 : ∀ i : Fin 20, wildEnvelopeCheck (envelopes8 i) (residueE (3^3) (values 1 20 i)) 3 (real i) := by decide +kernel

without_editor_info theorem zeroDirections8 : ∀ i : Fin 20, ∀ j : Fin 4,
    (envelopes8 i).directions j=0 := by decide +kernel

without_editor_info theorem linear8 : ∀ i : Fin 20, ∀ j : Fin 4,
    wildForm ((envelopes8 i).directions j)
      (graphStar edges (fun i => (envelopes8 i).base) constantsClass i) = 0 := by
  intro i k
  rw [zeroDirections8 i k]
  simp [wildForm]

without_editor_info theorem cross8 : ∀ e : Fin 58, ∀ j k : Fin 4,
    wildForm ((envelopes8 (edges e).src).directions j) ((envelopes8 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections8 ((edges e).src) i]
  simp [wildForm]

without_editor_info theorem value8 : vectorGraph edges (fun i => (envelopes8 i).base) constantsClass wildBilinear = 0 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell8 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-1) (hy : (3 : ℤ)^3 ∣ y-20) : graphSum edges (values x y) constants wild = 0 :=
  wild_cell edges values constants real values_congr values_real 1 20 3 envelopes8 constantsClass 0 constants_checked checks8 linear8 cross8 value8 (all_nonzero hf) hx hy

without_editor_info noncomputable def localSum (x y : ℤ) : ZMod 3 := graphSum edges (values x y) constants wild

without_editor_info def residues : Fin 9 → ℤ × ℤ × ℕ := (fun i => (#[(25,14,3),(16,23,3),(7,5,3),(22,26,3),(13,8,3),(4,17,3),(19,2,3),(10,11,3),(1,20,3)] : Array (ℤ × ℤ × ℕ))[i.val]'(by simpa using i.isLt))

without_editor_info def targets : Fin 9 → ZMod 3 := (fun i => (#[0,0,0,0,0,0,0,0,0] : Array (ZMod 3))[i.val]'(by simpa using i.isLt))

without_editor_info theorem cell_value (i : Fin 9) {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1)
    (hy : (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1) : localSum x y = targets i := by
  fin_cases i
  · exact cell0 hf hx hy
  · exact cell1 hf hx hy
  · exact cell2 hf hx hy
  · exact cell3 hf hx hy
  · exact cell4 hf hx hy
  · exact cell5 hf hx hy
  · exact cell6 hf hx hy
  · exact cell7 hf hx hy
  · exact cell8 hf hx hy

without_editor_info theorem covered0 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-25) (hy : (3 : ℤ)^3 ∣ y-14) : ∃ i : Fin 9, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨0,hx,hy⟩

without_editor_info theorem covered1 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-16) (hy : (3 : ℤ)^3 ∣ y-23) : ∃ i : Fin 9, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨1,hx,hy⟩

without_editor_info theorem covered2 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-7) (hy : (3 : ℤ)^3 ∣ y-5) : ∃ i : Fin 9, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨2,hx,hy⟩

without_editor_info theorem covered3 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-22) (hy : (3 : ℤ)^3 ∣ y-26) : ∃ i : Fin 9, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨3,hx,hy⟩

without_editor_info theorem covered4 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-13) (hy : (3 : ℤ)^3 ∣ y-8) : ∃ i : Fin 9, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨4,hx,hy⟩

without_editor_info theorem covered5 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-4) (hy : (3 : ℤ)^3 ∣ y-17) : ∃ i : Fin 9, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨5,hx,hy⟩

without_editor_info theorem covered6 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-19) (hy : (3 : ℤ)^3 ∣ y-2) : ∃ i : Fin 9, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨6,hx,hy⟩

without_editor_info theorem covered7 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-10) (hy : (3 : ℤ)^3 ∣ y-11) : ∃ i : Fin 9, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨7,hx,hy⟩

without_editor_info theorem covered8 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-1) (hy : (3 : ℤ)^3 ∣ y-20) : ∃ i : Fin 9, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨8,hx,hy⟩

without_editor_info theorem branch0 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^2 ∣ x-1) (hy : (3 : ℤ)^2 ∣ y-2) : ∃ i : Fin 9, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 9, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    3 (by decide) 9 1 2 [(1,20),(10,11),(19,2)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · intro X Y hF hX hY
    apply covered8 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered7 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered6 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch1 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^2 ∣ x-4) (hy : (3 : ℤ)^2 ∣ y-8) : ∃ i : Fin 9, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 9, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    3 (by decide) 9 4 8 [(4,17),(13,8),(22,26)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · intro X Y hF hX hY
    apply covered5 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered4 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered3 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch2 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^2 ∣ x-7) (hy : (3 : ℤ)^2 ∣ y-5) : ∃ i : Fin 9, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 9, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    3 (by decide) 9 7 5 [(7,5),(16,23),(25,14)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · intro X Y hF hX hY
    apply covered2 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered1 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered0 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch3 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^1 ∣ x-1) (hy : (3 : ℤ)^1 ∣ y-2) : ∃ i : Fin 9, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 9, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    3 (by decide) 3 1 2 [(1,2),(4,8),(7,5)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · intro X Y hF hX hY
    apply branch0 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply branch1 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply branch2 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch4 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^0 ∣ x-0) (hy : (3 : ℤ)^0 ∣ y-0) : ∃ i : Fin 9, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 9, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    3 (by decide) 1 0 0 [(1,2)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl
  · intro X Y hF hX hY
    apply branch3 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem local_cover {x y : ℤ} (hf : equation x y = 0) : ∃ i : Fin 9, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := branch4 hf (by simp) (by simp)

end GraphCert.Generated.g5786bb6f19cbbfc7842a018a.Proof.At3

open CubicSpecial GraphCert.Cubic

namespace GraphCert.Generated.g5786bb6f19cbbfc7842a018a.Proof



without_editor_info def supportPrimes : Fin 1 → PrimaryPrime := ![⟨2, (inferInstance : Fact (Prime (2 : Eisenstein))).out, ⟨1, by decide⟩⟩]

without_editor_info theorem supportPrimes_injective : Function.Injective supportPrimes := by
  intro i j h
  have h' := congrArg (fun p : PrimaryPrime => (p.val.re,p.val.im)) h
  have hi : ∀ i j : Fin 1, ((supportPrimes i).val.re,(supportPrimes i).val.im)=
      ((supportPrimes j).val.re,(supportPrimes j).val.im) → i=j := by decide +kernel
  exact hi i j h'

without_editor_info theorem cubic_reciprocity {x y : ℤ} (hf : equation x y=0) :
    At2.localSum x y + At3.localSum x y=0 := by
  have h := finite_relation edges (values x y) constants (all_nonzero hf) constants_nonzero
    supportPrimes supportPrimes_injective supportNumber (by decide +kernel)
    (fun π hN => outside hf π.val (primaryPrime_ne_three π) hN)
  have ht0 : tameAt (supportPrimes 0)=tame 2 At2.away_three := by rfl
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero] at h
  change (graphSum edges (values x y) constants (tameAt (supportPrimes 0))+0)+graphSum edges (values x y) constants wild=0 at h
  rw [ht0] at h
  have combine (a0 w : ZMod 3)
      (hh : (a0+0)+w=0) : (a0)+w=0 := by
    linear_combination hh
  exact combine _ _ h

end GraphCert.Generated.g5786bb6f19cbbfc7842a018a.Proof

namespace GraphCert.Generated.g5786bb6f19cbbfc7842a018a.Proof

without_editor_info theorem no_solution {x y : ℤ} (hf : equation x y = 0) : False := by
  have h := cubic_reciprocity hf
  have h2 : At2.localSum x y = 2 := by
    obtain ⟨i, hx, hy⟩ := At2.local_cover hf
    have hv := At2.cell_value i hf hx hy
    have ht : ∀ i, At2.targets i = 2 := by decide +kernel
    simpa only [hv] using ht i
  have h3 : At3.localSum x y = 0 := by
    obtain ⟨i, hx, hy⟩ := At3.local_cover hf
    have hv := At3.cell_value i hf hx hy
    have ht : ∀ i, At3.targets i = 0 := by decide +kernel
    simpa only [hv] using ht i
  all_goals
    rw [h2, h3] at h
    exact absurd h (by decide +kernel)

end GraphCert.Generated.g5786bb6f19cbbfc7842a018a.Proof

namespace OriginalEquation
def f (x y : ℤ) : ℤ := x^4 + x + y^3 + y^2 + y + 2
theorem no_integer_solutions : ¬ ∃ x y : ℤ, f x y = 0 := by
  rintro ⟨x, y, hf⟩
  apply GraphCert.Generated.g5786bb6f19cbbfc7842a018a.Proof.no_solution (x := x) (y := y)
  change GraphCert.Generated.g5786bb6f19cbbfc7842a018a.Proof.equation x y = 0
  convert hf using 1 <;>
    simp [f, GraphCert.Generated.g5786bb6f19cbbfc7842a018a.Proof.equation, GraphCert.Generated.g5786bb6f19cbbfc7842a018a.Proof.F,
      GraphCert.Cubic.Polynomial.value, GraphCert.Cubic.Polynomial.eval, CubicSpecial.Dense.eval] <;> ring
end OriginalEquation


-- Canonical equation: q = 7533420/1.
theorem E7533420_1 : ¬ ∃ x y : ℤ, x^4 + x + y^3 + y^2 + y + 2 = 0 := by
  rintro ⟨x, y, h⟩
  apply OriginalEquation.no_integer_solutions
  refine ⟨x, y, ?_⟩
  dsimp [OriginalEquation.f]
  linear_combination h

#print axioms E7533420_1
