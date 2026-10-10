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

                                              
                                                                      
                                                                       

set_option Elab.async false
set_option linter.all false
                                         
elab "without_editor_info " c:command : command =>
  Lean.Elab.withEnableInfoTree false (Lean.Elab.Command.elabCommand c)

  
                                                                       
                                                                         
                                                                         
                                                                               
                                                                            
                                                                             
                                                                                
  

set_option backward.isDefEq.respectTransparency false

                                                                       
                                                                          

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

namespace GraphCert.Generated.g6681fe82262d85cf066bd0fe.Proof

without_editor_info def F : Poly := [[⟨(-1),0⟩,⟨1,0⟩,⟨0,0⟩,⟨1,0⟩],[⟨1,0⟩],[],[],[⟨8,0⟩]]

without_editor_info def nodes : Fin 25 → Poly := ![[[⟨1,1⟩,⟨(-1),0⟩]],[[⟨0,1⟩,⟨(-1),0⟩]],[[⟨0,(-1)⟩,⟨(-1),0⟩]],[[⟨(-1),0⟩,⟨(-1),0⟩]],[[⟨1,1⟩],[⟨2,0⟩]],[[⟨0,1⟩],[⟨2,0⟩]],[[⟨0,(-1)⟩],[⟨2,0⟩]],[[⟨(-1),(-1)⟩],[⟨2,0⟩]],[[⟨2,1⟩],[⟨2,0⟩]],[[⟨1,(-1)⟩],[⟨2,0⟩]],[[⟨0,0⟩,⟨(-1),0⟩],[⟨2,0⟩]],[[⟨0,0⟩,⟨0,(-1)⟩],[⟨2,0⟩]],[[⟨0,0⟩,⟨1,1⟩],[⟨2,0⟩]],[[⟨1,1⟩,⟨0,(-1)⟩],[⟨2,0⟩]],[[⟨1,1⟩,⟨1,1⟩],[⟨2,0⟩]],[[⟨0,1⟩,⟨1,0⟩],[⟨2,0⟩]],[[⟨0,(-1)⟩,⟨(-1),0⟩],[⟨2,0⟩]],[[⟨0,(-1)⟩,⟨0,(-1)⟩],[⟨2,0⟩]],[[⟨0,(-1)⟩,⟨1,1⟩],[⟨2,0⟩]],[[⟨(-1),(-1)⟩,⟨1,0⟩],[⟨2,0⟩]],[[⟨(-1),(-1)⟩,⟨(-1),0⟩]],[[⟨1,1⟩,⟨(-1),0⟩],[⟨2,0⟩]],[[⟨1,2⟩],[⟨3,0⟩]],[[⟨(-1),(-2)⟩],[⟨3,0⟩]],[[],[⟨1,0⟩]]]

without_editor_info def constants : Fin 25 → Eisenstein := ![⟨1,(-1)⟩,⟨2,0⟩,⟨(-3),(-3)⟩,⟨(-1),(-1)⟩,⟨1,0⟩,⟨(-1),(-1)⟩,⟨(-1),(-1)⟩,⟨(-1),(-1)⟩,⟨0,(-2)⟩,⟨0,(-4)⟩,⟨0,(-1)⟩,⟨0,(-12)⟩,⟨2,(-2)⟩,⟨(-2),(-1)⟩,⟨(-3),0⟩,⟨(-1),(-1)⟩,⟨(-4),(-4)⟩,⟨(-1),(-2)⟩,⟨0,(-3)⟩,⟨0,(-1)⟩,⟨4,0⟩,⟨(-2),(-2)⟩,⟨(-6),0⟩,⟨(-4),(-8)⟩,⟨1,0⟩]

without_editor_info def edgeList : List (GraphEdge 25) := [⟨0,4,1⟩,⟨0,10,1⟩,⟨0,11,2⟩,⟨0,15,2⟩,⟨0,16,1⟩,⟨1,4,1⟩,⟨1,5,2⟩,⟨1,6,1⟩,⟨1,15,2⟩,⟨1,19,1⟩,⟨1,24,2⟩,⟨2,6,2⟩,⟨2,10,2⟩,⟨2,12,1⟩,⟨2,19,1⟩,⟨2,21,2⟩,⟨3,13,2⟩,⟨3,16,1⟩,⟨3,18,1⟩,⟨3,21,2⟩,⟨4,15,1⟩,⟨4,17,2⟩,⟨4,18,1⟩,⟨4,20,2⟩,⟨4,21,2⟩,⟨5,11,1⟩,⟨5,12,1⟩,⟨5,21,2⟩,⟨6,10,2⟩,⟨6,11,1⟩,⟨6,13,2⟩,⟨6,14,1⟩,⟨6,16,1⟩,⟨6,19,1⟩,⟨6,20,1⟩,⟨7,11,2⟩,⟨7,12,2⟩,⟨7,16,1⟩,⟨7,20,2⟩,⟨8,11,2⟩,⟨8,14,2⟩,⟨8,17,2⟩,⟨8,19,1⟩,⟨9,12,1⟩,⟨9,14,1⟩,⟨9,15,2⟩,⟨9,17,1⟩,⟨10,20,2⟩,⟨10,22,1⟩,⟨10,23,2⟩,⟨11,12,1⟩,⟨12,15,1⟩,⟨13,14,1⟩,⟨13,19,1⟩,⟨13,24,1⟩,⟨14,16,2⟩,⟨14,17,1⟩,⟨14,19,2⟩,⟨14,22,2⟩,⟨15,16,1⟩,⟨15,17,2⟩,⟨15,18,1⟩,⟨15,20,1⟩,⟨17,18,1⟩,⟨17,21,1⟩,⟨17,23,1⟩,⟨18,24,2⟩,⟨19,20,2⟩,⟨19,21,2⟩,⟨20,24,1⟩]

without_editor_info def edges : Fin 70 → GraphEdge 25 := listEdges edgeList (by decide)

without_editor_info def neighbors : Fin 25 → List (Fin 25 × ℕ) := ![[(4,1),(10,1),(11,2),(15,2),(16,1)],[(4,1),(5,2),(6,1),(15,2),(19,1),(24,2)],[(6,2),(10,2),(12,1),(19,1),(21,2)],[(13,2),(16,1),(18,1),(21,2)],[(0,2),(1,2),(15,1),(17,2),(18,1),(20,2),(21,2)],[(1,1),(11,1),(12,1),(21,2)],[(1,2),(2,1),(10,2),(11,1),(13,2),(14,1),(16,1),(19,1),(20,1)],[(11,2),(12,2),(16,1),(20,2)],[(11,2),(14,2),(17,2),(19,1)],[(12,1),(14,1),(15,2),(17,1)],[(0,2),(2,1),(6,1),(20,2),(22,1),(23,2)],[(0,1),(5,2),(6,2),(7,1),(8,1),(12,1)],[(2,2),(5,2),(7,1),(9,2),(11,2),(15,1)],[(3,1),(6,1),(14,1),(19,1),(24,1)],[(6,2),(8,1),(9,2),(13,2),(16,2),(17,1),(19,2),(22,2)],[(0,1),(1,1),(4,2),(9,1),(12,2),(16,1),(17,2),(18,1),(20,1)],[(0,2),(3,2),(6,2),(7,2),(14,1),(15,2)],[(4,1),(8,1),(9,2),(14,2),(15,1),(18,1),(21,1),(23,1)],[(3,2),(4,2),(15,2),(17,2),(24,2)],[(1,2),(2,2),(6,2),(8,2),(13,2),(14,1),(20,2),(21,2)],[(4,1),(6,2),(7,1),(10,1),(15,2),(19,1),(24,1)],[(2,1),(3,1),(4,1),(5,1),(17,2),(19,1)],[(10,2),(14,1)],[(10,1),(17,2)],[(1,1),(13,2),(18,1),(20,2)]]

without_editor_info theorem adjacency_checked : ∀ i : Fin 25, neighbors i = neighborList edges i := by
  simp only [edges, neighborList_listEdges]
  decide +kernel

without_editor_info def equation (x y : ℤ) : ℤ := (value F x y).re

without_editor_info def values (x y : ℤ) (i : Fin 25) : Eisenstein := value (nodes i) x y

without_editor_info theorem curve_zero {x y : ℤ} (hf : equation x y = 0) : value F x y = 0 := by
  ext
  · exact hf
  · simp [value, eval, CubicSpecial.Dense.eval, F]

without_editor_info theorem equation_congr {M x y a b : ℤ} (hx : M ∣ x-a) (hy : M ∣ y-b) :
    M ∣ equation x y-equation a b := real_congr F hx hy

without_editor_info theorem values_congr (M : ℕ) (x y a b : ℤ) (hx : (M : ℤ) ∣ x-a) (hy : (M : ℤ) ∣ y-b) :
    ∀ i : Fin 25, (M : Eisenstein) ∣ values x y i-values a b i :=
  fun i => value_congr (nodes i) M hx hy

without_editor_info def real : Fin 25 → Bool := ![false,false,false,true,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,true]

without_editor_info theorem values_real (i : Fin 25) (h : real i = true) (x y : ℤ) : (values x y i).im = 0 := by
  fin_cases i <;> simp [real] at h <;> simp [values, value, eval, CubicSpecial.Dense.eval, nodes]

without_editor_info theorem nonzero_0 {x y : ℤ} (hf : equation x y = 0) : values x y 0 ≠ 0 :=
  nonzero_of_mod F (nodes 0) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_1 {x y : ℤ} (hf : equation x y = 0) : values x y 1 ≠ 0 :=
  nonzero_of_mod F (nodes 1) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_2 {x y : ℤ} (hf : equation x y = 0) : values x y 2 ≠ 0 :=
  nonzero_of_mod F (nodes 2) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_3 {x y : ℤ} (hf : equation x y = 0) : values x y 3 ≠ 0 :=
  nonzero_of_mod F (nodes 3) 5 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_4 {x y : ℤ} (hf : equation x y = 0) : values x y 4 ≠ 0 :=
  nonzero_of_mod F (nodes 4) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_5 {x y : ℤ} (hf : equation x y = 0) : values x y 5 ≠ 0 :=
  nonzero_of_mod F (nodes 5) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_6 {x y : ℤ} (hf : equation x y = 0) : values x y 6 ≠ 0 :=
  nonzero_of_mod F (nodes 6) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_7 {x y : ℤ} (hf : equation x y = 0) : values x y 7 ≠ 0 :=
  nonzero_of_mod F (nodes 7) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_8 {x y : ℤ} (hf : equation x y = 0) : values x y 8 ≠ 0 :=
  nonzero_of_mod F (nodes 8) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_9 {x y : ℤ} (hf : equation x y = 0) : values x y 9 ≠ 0 :=
  nonzero_of_mod F (nodes 9) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_10 {x y : ℤ} (hf : equation x y = 0) : values x y 10 ≠ 0 :=
  nonzero_of_mod F (nodes 10) 5 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_11 {x y : ℤ} (hf : equation x y = 0) : values x y 11 ≠ 0 :=
  nonzero_of_mod F (nodes 11) 3 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_12 {x y : ℤ} (hf : equation x y = 0) : values x y 12 ≠ 0 :=
  nonzero_of_mod F (nodes 12) 3 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_13 {x y : ℤ} (hf : equation x y = 0) : values x y 13 ≠ 0 :=
  nonzero_of_mod F (nodes 13) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_14 {x y : ℤ} (hf : equation x y = 0) : values x y 14 ≠ 0 :=
  nonzero_of_mod F (nodes 14) 4 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_15 {x y : ℤ} (hf : equation x y = 0) : values x y 15 ≠ 0 :=
  nonzero_of_mod F (nodes 15) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_16 {x y : ℤ} (hf : equation x y = 0) : values x y 16 ≠ 0 :=
  nonzero_of_mod F (nodes 16) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_17 {x y : ℤ} (hf : equation x y = 0) : values x y 17 ≠ 0 :=
  nonzero_of_mod F (nodes 17) 4 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_18 {x y : ℤ} (hf : equation x y = 0) : values x y 18 ≠ 0 :=
  nonzero_of_mod F (nodes 18) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_19 {x y : ℤ} (hf : equation x y = 0) : values x y 19 ≠ 0 :=
  nonzero_of_mod F (nodes 19) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_20 {x y : ℤ} (hf : equation x y = 0) : values x y 20 ≠ 0 :=
  nonzero_of_mod F (nodes 20) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_21 {x y : ℤ} (hf : equation x y = 0) : values x y 21 ≠ 0 :=
  nonzero_of_mod F (nodes 21) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_22 {x y : ℤ} (hf : equation x y = 0) : values x y 22 ≠ 0 :=
  nonzero_of_mod F (nodes 22) 3 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_23 {x y : ℤ} (hf : equation x y = 0) : values x y 23 ≠ 0 :=
  nonzero_of_mod F (nodes 23) 3 (by decide +kernel) (curve_zero hf)

without_editor_info theorem nonzero_24 {x y : ℤ} (hf : equation x y = 0) : values x y 24 ≠ 0 :=
  nonzero_of_mod F (nodes 24) 2 (by decide +kernel) (curve_zero hf)

without_editor_info theorem all_nonzero {x y : ℤ} (hf : equation x y = 0) : ∀ i : Fin 25, values x y i ≠ 0 := by
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
  · exact nonzero_20 hf
  · exact nonzero_21 hf
  · exact nonzero_22 hf
  · exact nonzero_23 hf
  · exact nonzero_24 hf

without_editor_info theorem constants_nonzero : ∀ i : Fin 25, constants i ≠ 0 := by decide +kernel

without_editor_info def root_0 : Poly := [[⟨(-2),(-1)⟩],[⟨(-2),(-2)⟩],[⟨0,(-4)⟩],[⟨(-8),(-8)⟩]]

without_editor_info def starA_0 : Poly := [[⟨(-32),(-4)⟩,⟨34,14⟩,⟨(-34),(-26)⟩,⟨20,28⟩],[⟨(-52),(-16)⟩,⟨20,(-24)⟩,⟨(-16),4⟩,⟨8,0⟩],[⟨(-32),0⟩,⟨(-16),(-32)⟩],[⟨(-32),(-64)⟩],[⟨(-96),(-96)⟩],[⟨(-64),0⟩]]

without_editor_info def starB_0 : Poly := [[⟨2,31⟩,⟨49,(-19)⟩,⟨(-59),(-40)⟩,⟨16,(-10)⟩,⟨(-49),(-8)⟩,⟨21,30⟩],[⟨6,26⟩,⟨4,(-40)⟩,⟨14,6⟩,⟨(-28),(-74)⟩,⟨(-16),26⟩,⟨12,2⟩],[⟨28,56⟩,⟨60,36⟩,⟨40,(-76)⟩,⟨(-84),(-72)⟩,⟨8,16⟩],[⟨(-48),72⟩,⟨240,168⟩,⟨0,(-192)⟩,⟨(-40),(-8)⟩]]

without_editor_info theorem star_0 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 0) (values x y) (constants 0) - value root_0 x y ^ 3 =
      value F x y * value starA_0 x y + values x y 0 * value starB_0 x y :=
  identity_power (neighbors 0) nodes (constants 0) F starA_0 starB_0 root_0 0 1 3 (by decide +kernel) x y

without_editor_info def root_1 : Poly := [[⟨2,0⟩],[⟨(-2),(-2)⟩],[],[⟨(-8),0⟩]]

without_editor_info def starA_1 : Poly := [[⟨(-27),(-18)⟩,⟨3,(-21)⟩,⟨(-13),1⟩,⟨0,(-5)⟩,⟨(-6),0⟩],[⟨8,0⟩,⟨(-22),4⟩,⟨(-6),0⟩,⟨(-10),4⟩],[⟨(-56),12⟩,⟨(-20),(-16)⟩,⟨8,28⟩,⟨4,0⟩],[⟨32,24⟩,⟨8,64⟩,⟨24,0⟩],[⟨0,48⟩,⟨48,0⟩],[⟨96,0⟩]]

without_editor_info def starB_1 : Poly := [[⟨17,35⟩,⟨(-15),(-47)⟩,⟨6,31⟩,⟨(-3),(-46)⟩,⟨(-8),12⟩,⟨0,(-11)⟩,⟨(-6),0⟩],[⟨(-17),(-59)⟩,⟨16,50⟩,⟨0,(-45)⟩,⟨(-24),12⟩,⟨(-10),(-14)⟩,⟨(-10),4⟩],[⟨50,62⟩,⟨(-76),(-104)⟩,⟨(-20),38⟩,⟨(-48),(-40)⟩,⟨8,32⟩,⟨4,0⟩],[⟨(-164),(-164)⟩,⟨64,152⟩,⟨(-24),(-60)⟩,⟨8,88⟩,⟨24,0⟩]]

without_editor_info theorem star_1 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 1) (values x y) (constants 1) - value root_1 x y ^ 3 =
      value F x y * value starA_1 x y + values x y 1 * value starB_1 x y :=
  identity_power (neighbors 1) nodes (constants 1) F starA_1 starB_1 root_1 1 1 3 (by decide +kernel) x y

without_editor_info def root_2 : Poly := [[⟨3,0⟩],[⟨4,2⟩],[⟨4,(-4)⟩]]

without_editor_info def starA_2 : Poly := [[⟨(-42),36⟩,⟨(-12),(-60)⟩,⟨78,114⟩,⟨(-72),(-60)⟩,⟨18,6⟩],[⟨(-48),60⟩,⟨36,(-72)⟩,⟨24,144⟩,⟨(-24),(-48)⟩],[⟨(-48),24⟩,⟨120,(-48)⟩,⟨(-48),24⟩],[⟨(-96),(-48)⟩,⟨144,96⟩],[⟨(-96),(-96)⟩]]

without_editor_info def starB_2 : Poly := [[⟨(-105),(-69)⟩,⟨90,(-75)⟩,⟨81,180⟩,⟨0,(-30)⟩,⟨15,102⟩,⟨(-63),(-72)⟩,⟨18,6⟩],[⟨(-84),(-114)⟩,⟨198,12⟩,⟨0,120⟩,⟨102,42⟩,⟨(-30),78⟩,⟨(-12),(-36)⟩],[⟨(-180),(-216)⟩,⟨180,(-60)⟩,⟨156,96⟩,⟨0,84⟩,⟨(-48),(-36)⟩,⟨0,12⟩],[⟨(-408),(-504)⟩,⟨96,(-360)⟩,⟨480,360⟩,⟨(-144),48⟩,⟨24,(-48)⟩]]

without_editor_info theorem star_2 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 2) (values x y) (constants 2) - value root_2 x y ^ 3 =
      value F x y * value starA_2 x y + values x y 2 * value starB_2 x y :=
  identity_power (neighbors 2) nodes (constants 2) F starA_2 starB_2 root_2 2 1 3 (by decide +kernel) x y

without_editor_info def root_3 : Poly := [[⟨3,6⟩],[⟨(-4),4⟩],[⟨8,16⟩],[⟨8,16⟩]]

without_editor_info def starA_3 : Poly := [[⟨(-360),90⟩,⟨36,234⟩,⟨54,(-54)⟩,⟨(-72),(-144)⟩],[⟨(-408),480⟩,⟨84,168⟩,⟨0,0⟩,⟨(-24),(-48)⟩],[⟨(-408),1128⟩],[⟨288,1440⟩],[⟨576,1152⟩],[⟨192,384⟩]]

without_editor_info def starB_3 : Poly := [[⟨252,(-252)⟩,⟨(-567),108⟩,⟨387,180⟩,⟨(-432),0⟩,⟨234,90⟩,⟨(-99),(-144)⟩],[⟨264,(-606)⟩,⟨(-450),882⟩,⟨156,(-336)⟩,⟨(-234),342⟩,⟨78,(-6)⟩,⟨(-24),(-48)⟩],[⟨0,(-972)⟩,⟨108,1188⟩,⟨(-432),108⟩,⟨108,216⟩],[⟨576,(-1224)⟩,⟨(-288),72⟩,⟨288,1224⟩]]

without_editor_info theorem star_3 (x y : ℤ) :
    (3 : Eisenstein)^3 * rowProduct (neighbors 3) (values x y) (constants 3) - value root_3 x y ^ 3 =
      value F x y * value starA_3 x y + values x y 3 * value starB_3 x y :=
  identity_power (neighbors 3) nodes (constants 3) F starA_3 starB_3 root_3 3 3 3 (by decide +kernel) x y

without_editor_info def root_4 : Poly := [[⟨2,1⟩,⟨(-3),(-1)⟩,⟨0,(-2)⟩]]

without_editor_info def starA_4 : Poly := [[⟨1,5⟩,⟨(-21),(-13)⟩,⟨5,(-2)⟩,⟨(-34),(-10)⟩,⟨(-22),(-48)⟩,⟨27,(-12)⟩,⟨21,21⟩,⟨(-5),7⟩,⟨(-5),(-4)⟩,⟨0,(-1)⟩],[⟨0,8⟩,⟨(-12),4⟩,⟨(-24),0⟩,⟨(-36),(-24)⟩,⟨(-24),(-24)⟩,⟨(-12),(-24)⟩,⟨0,(-8)⟩,⟨0,(-4)⟩],[⟨0,8⟩,⟨(-16),0⟩,⟨(-24),(-8)⟩,⟨(-32),(-32)⟩,⟨(-8),(-24)⟩,⟨0,(-16)⟩,⟨8,0⟩]]

without_editor_info def starB_4 : Poly := [[⟨(-1),2⟩,⟨5,12⟩,⟨(-34),(-10)⟩,⟨(-9),(-44)⟩,⟨22,(-5)⟩,⟨11,(-19)⟩,⟨50,7⟩,⟨44,39⟩,⟨13,35⟩,⟨(-10),8⟩,⟨(-5),(-4)⟩,⟨1,0⟩],[⟨(-1),2⟩,⟨(-21),(-14)⟩,⟨6,(-25)⟩,⟨18,6⟩,⟨(-6),(-8)⟩,⟨14,(-31)⟩,⟨41,14⟩,⟨21,14⟩,⟨10,11⟩,⟨5,5⟩,⟨0,2⟩],[⟨0,10⟩,⟨0,(-2)⟩,⟨(-30),50⟩,⟨(-148),(-92)⟩,⟨(-76),(-152)⟩,⟨54,(-70)⟩,⟨48,6⟩,⟨40,10⟩,⟨18,26⟩,⟨(-2),4⟩],[⟨(-12),4⟩,⟨12,52⟩,⟨(-156),(-64)⟩,⟨(-8),(-128)⟩,⟨40,24⟩,⟨(-60),(-24)⟩,⟨(-28),(-84)⟩,⟨44,(-4)⟩,⟨12,16⟩,⟨0,4⟩]]

without_editor_info theorem star_4 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 4) (values x y) (constants 4) - value root_4 x y ^ 3 =
      value F x y * value starA_4 x y + values x y 4 * value starB_4 x y :=
  identity_power (neighbors 4) nodes (constants 4) F starA_4 starB_4 root_4 4 1 3 (by decide +kernel) x y

without_editor_info def root_5 : Poly := [[⟨0,0⟩,⟨0,(-1)⟩,⟨1,1⟩]]

without_editor_info def starA_5 : Poly := [[⟨1,1⟩,⟨(-1),1⟩,⟨(-2),(-2)⟩,⟨1,0⟩]]

without_editor_info def starB_5 : Poly := [[⟨0,(-1)⟩,⟨2,2⟩,⟨(-1),1⟩,⟨(-1),0⟩,⟨(-1),(-1)⟩],[⟨2,1⟩,⟨0,3⟩,⟨(-2),(-2)⟩,⟨1,1⟩],[⟨6,4⟩,⟨(-2),4⟩,⟨0,(-4)⟩,⟨0,2⟩],[⟨4,(-4)⟩,⟨12,4⟩,⟨8,8⟩,⟨(-4),0⟩]]

without_editor_info theorem star_5 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 5) (values x y) (constants 5) - value root_5 x y ^ 3 =
      value F x y * value starA_5 x y + values x y 5 * value starB_5 x y :=
  identity_power (neighbors 5) nodes (constants 5) F starA_5 starB_5 root_5 5 1 3 (by decide +kernel) x y

without_editor_info def root_6 : Poly := [[⟨1,2⟩,⟨0,(-1)⟩,⟨1,(-1)⟩]]

without_editor_info def starA_6 : Poly := [[⟨(-2),(-5)⟩,⟨(-1),(-1)⟩,⟨(-10),14⟩,⟨11,6⟩,⟨29,37⟩,⟨6,(-5)⟩,⟨14,6⟩,⟨0,(-3)⟩,⟨1,2⟩,⟨0,(-1)⟩],[⟨0,(-4)⟩,⟨(-8),(-8)⟩,⟨(-28),4⟩,⟨(-20),20⟩,⟨4,56⟩,⟨32,40⟩,⟨24,28⟩,⟨8,(-4)⟩],[⟨0,(-16)⟩,⟨(-32),(-40)⟩,⟨(-40),(-32)⟩,⟨(-64),(-8)⟩,⟨(-8),32⟩,⟨0,24⟩,⟨24,16⟩],[⟨16,(-16)⟩,⟨(-16),(-32)⟩,⟨(-32),(-64)⟩,⟨(-64),(-32)⟩,⟨(-32),(-16)⟩,⟨(-16),16⟩],[⟨0,(-32)⟩,⟨0,(-32)⟩,⟨(-32),(-64)⟩,⟨(-32),(-32)⟩,⟨(-32),(-32)⟩]]

without_editor_info def starB_6 : Poly := [[⟨0,1⟩,⟨6,1⟩,⟨(-12),(-3)⟩,⟨9,5⟩,⟨(-21),6⟩,⟨41,(-5)⟩,⟨(-13),1⟩,⟨2,(-42)⟩,⟨(-16),(-4)⟩,⟨(-7),(-13)⟩,⟨(-3),2⟩,⟨2,1⟩],[⟨3,2⟩,⟨(-14),(-19)⟩,⟨12,18⟩,⟨(-21),(-25)⟩,⟨56,45⟩,⟨(-35),(-54)⟩,⟨52,12⟩,⟨(-47),(-42)⟩,⟨7,(-7)⟩,⟨(-19),(-6)⟩,⟨(-2),4⟩],[⟨10,(-6)⟩,⟨(-26),0⟩,⟨40,20⟩,⟨(-32),42⟩,⟨102,8⟩,⟨10,58⟩,⟨52,(-68)⟩,⟨(-6),(-2)⟩,⟨(-24),(-54)⟩,⟨(-14),(-6)⟩],[⟨(-8),(-4)⟩,⟨(-4),36⟩,⟨(-8),(-40)⟩,⟨52,152⟩,⟨(-28),(-28)⟩,⟨192,172⟩,⟨24,(-24)⟩,⟨80,12⟩,⟨(-12),(-24)⟩,⟨0,4⟩]]

without_editor_info theorem star_6 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 6) (values x y) (constants 6) - value root_6 x y ^ 3 =
      value F x y * value starA_6 x y + values x y 6 * value starB_6 x y :=
  identity_power (neighbors 6) nodes (constants 6) F starA_6 starB_6 root_6 6 1 3 (by decide +kernel) x y

without_editor_info def root_7 : Poly := [[⟨2,1⟩,⟨(-1),(-1)⟩,⟨0,1⟩]]

without_editor_info def starA_7 : Poly := [[⟨2,5⟩,⟨3,(-3)⟩,⟨(-9),(-6)⟩,⟨(-2),3⟩,⟨1,1⟩],[⟨4,0⟩,⟨0,(-8)⟩,⟨(-4),(-4)⟩]]

without_editor_info def starB_7 : Poly := [[⟨1,0⟩,⟨(-1),0⟩,⟨6,6⟩,⟨2,(-6)⟩,⟨(-9),(-3)⟩,⟨0,5⟩,⟨1,1⟩],[⟨5,5⟩,⟨5,0⟩,⟨2,(-5)⟩,⟨(-9),(-11)⟩,⟨(-5),2⟩,⟨2,2⟩],[⟨10,(-4)⟩,⟨(-8),(-18)⟩,⟨(-2),(-2)⟩,⟨2,(-8)⟩,⟨(-4),(-6)⟩],[⟨(-8),(-28)⟩,⟨(-20),(-4)⟩,⟨28,8⟩,⟨0,(-20)⟩,⟨(-4),(-4)⟩]]

without_editor_info theorem star_7 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 7) (values x y) (constants 7) - value root_7 x y ^ 3 =
      value F x y * value starA_7 x y + values x y 7 * value starB_7 x y :=
  identity_power (neighbors 7) nodes (constants 7) F starA_7 starB_7 root_7 7 1 3 (by decide +kernel) x y

without_editor_info def root_8 : Poly := [[⟨(-2),(-6)⟩,⟨4,1⟩,⟨0,1⟩]]

without_editor_info def starA_8 : Poly := [[⟨(-28),8⟩,⟨(-88),(-112)⟩,⟨27,(-78)⟩,⟨9,16⟩,⟨(-2),0⟩],[⟨(-16),(-24)⟩,⟨(-48),(-80)⟩,⟨(-56),(-88)⟩],[⟨(-16),(-32)⟩,⟨(-32),(-80)⟩],[⟨0,(-32)⟩]]

without_editor_info def starB_8 : Poly := [[⟨(-52),(-84)⟩,⟨124,(-40)⟩,⟨109,173⟩,⟨(-69),19⟩,⟨64,14⟩,⟨26,72⟩,⟨(-10),(-4)⟩],[⟨84,52⟩,⟨(-16),160⟩,⟨(-167),(-77)⟩,⟨89,9⟩,⟨(-30),90⟩,⟨(-44),(-28)⟩],[⟨(-96),(-16)⟩,⟨(-88),(-192)⟩,⟨200,114⟩,⟨(-164),82⟩,⟨(-128),(-108)⟩],[⟨64,(-48)⟩,⟨160,272⟩,⟨(-428),(-56)⟩,⟨(-244),(-304)⟩,⟨8,0⟩]]

without_editor_info theorem star_8 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 8) (values x y) (constants 8) - value root_8 x y ^ 3 =
      value F x y * value starA_8 x y + values x y 8 * value starB_8 x y :=
  identity_power (neighbors 8) nodes (constants 8) F starA_8 starB_8 root_8 8 1 3 (by decide +kernel) x y

without_editor_info def root_9 : Poly := [[⟨(-2),(-4)⟩,⟨2,2⟩,⟨0,(-2)⟩]]

without_editor_info def starA_9 : Poly := [[⟨12,12⟩,⟨(-8),(-20)⟩,⟨4,24⟩,⟨8,0⟩],[⟨0,(-16)⟩]]

without_editor_info def starB_9 : Poly := [[⟨4,(-16)⟩,⟨20,28⟩,⟨(-12),(-32)⟩,⟨8,40⟩,⟨12,(-4)⟩],[⟨(-20),(-8)⟩,⟨(-28),(-12)⟩,⟨0,52⟩,⟨32,0⟩],[⟨16,40⟩,⟨56,80⟩,⟨104,24⟩,⟨16,(-16)⟩],[⟨16,(-16)⟩,⟨64,(-16)⟩,⟨(-16),(-96)⟩,⟨(-32),0⟩]]

without_editor_info theorem star_9 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 9) (values x y) (constants 9) - value root_9 x y ^ 3 =
      value F x y * value starA_9 x y + values x y 9 * value starB_9 x y :=
  identity_power (neighbors 9) nodes (constants 9) F starA_9 starB_9 root_9 9 1 3 (by decide +kernel) x y

without_editor_info def root_10 : Poly := [[⟨4,2⟩,⟨0,(-3)⟩,⟨2,1⟩,⟨0,(-3)⟩]]

without_editor_info def starA_10 : Poly := [[⟨0,72⟩,⟨72,72⟩,⟨0,90⟩,⟨126,108⟩,⟨18,36⟩,⟨54,54⟩]]

without_editor_info def starB_10 : Poly := [[⟨84,24⟩,⟨(-42),(-102)⟩,⟨111,150⟩,⟨39,(-138)⟩,⟨(-6),96⟩,⟨75,(-48)⟩,⟨(-36),36⟩,⟨27,0⟩,⟨(-27),0⟩],[⟨36,36⟩,⟨126,54⟩,⟨(-36),(-72)⟩,⟨126,180⟩,⟨36,(-162)⟩,⟨(-72),72⟩,⟨54,0⟩,⟨(-54),0⟩],[⟨252,180⟩,⟨(-72),(-288)⟩,⟨108,360⟩,⟨144,(-324)⟩,⟨(-216),72⟩,⟨108,0⟩,⟨(-108),0⟩],[⟨0,(-72)⟩,⟨(-72),(-288)⟩,⟨(-432),(-360)⟩,⟨(-72),0⟩,⟨(-288),(-360)⟩,⟨(-216),0⟩]]

without_editor_info theorem star_10 (x y : ℤ) :
    (2 : Eisenstein)^3 * rowProduct (neighbors 10) (values x y) (constants 10) - value root_10 x y ^ 3 =
      value F x y * value starA_10 x y + values x y 10 * value starB_10 x y :=
  identity_power (neighbors 10) nodes (constants 10) F starA_10 starB_10 root_10 10 2 3 (by decide +kernel) x y

without_editor_info def root_11 : Poly := [[⟨4,2⟩,⟨0,0⟩,⟨(-4),(-2)⟩]]

without_editor_info def starA_11 : Poly := [[⟨24,48⟩,⟨0,(-24)⟩,⟨24,(-48)⟩,⟨(-48),48⟩],[⟨48,0⟩,⟨48,96⟩,⟨(-48),0⟩],[⟨96,0⟩,⟨96,192⟩,⟨(-96),0⟩],[⟨192,0⟩,⟨0,192⟩]]

without_editor_info def starB_11 : Poly := [[⟨36,(-12)⟩,⟨(-36),72⟩,⟨(-144),(-96)⟩,⟨144,(-24)⟩,⟨(-72),(-24)⟩,⟨72,72⟩],[⟨24,24⟩,⟨48,168⟩,⟨(-240),(-240)⟩,⟨144,96⟩,⟨48,(-96)⟩],[⟨144,(-48)⟩,⟨(-96),240⟩,⟨(-96),(-288)⟩,⟨(-192),(-192)⟩,⟨96,96⟩],[⟨0,0⟩,⟨(-96),96⟩,⟨(-192),192⟩,⟨192,(-192)⟩]]

without_editor_info theorem star_11 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 11) (values x y) (constants 11) - value root_11 x y ^ 3 =
      value F x y * value starA_11 x y + values x y 11 * value starB_11 x y :=
  identity_power (neighbors 11) nodes (constants 11) F starA_11 starB_11 root_11 11 1 3 (by decide +kernel) x y

without_editor_info def root_12 : Poly := [[⟨2,(-2)⟩,⟨0,0⟩,⟨(-2),2⟩]]

without_editor_info def starA_12 : Poly := [[⟨(-24),(-48)⟩,⟨(-36),(-36)⟩,⟨60,72⟩,⟨(-120),48⟩,⟨132,12⟩,⟨(-36),(-48)⟩],[⟨0,0⟩,⟨(-96),(-120)⟩,⟨(-40),256⟩,⟨240,24⟩,⟨(-48),(-72)⟩,⟨(-16),(-8)⟩],[⟨0,(-96)⟩,⟨(-272),32⟩,⟨304,320⟩,⟨128,(-80)⟩,⟨(-64),(-80)⟩],[⟨(-64),(-32)⟩,⟨(-64),160⟩,⟨352,224⟩,⟨(-32),(-160)⟩],[⟨(-128),(-64)⟩,⟨128,256⟩,⟨64,(-64)⟩]]

without_editor_info def starB_12 : Poly := [[⟨12,24⟩,⟨(-48),(-66)⟩,⟨42,216⟩,⟨162,(-234)⟩,⟨(-144),90⟩,⟨(-48),(-180)⟩,⟨(-12),120⟩,⟨48,12⟩],[⟨24,(-36)⟩,⟨(-176),68⟩,⟨356,124⟩,⟨(-252),(-192)⟩,⟨228,24⟩,⟨(-256),(-56)⟩,⟨48,96⟩,⟨8,(-8)⟩],[⟨(-80),(-40)⟩,⟨160,104⟩,⟨(-40),(-200)⟩,⟨(-8),272⟩,⟨(-152),(-400)⟩,⟨(-112),112⟩,⟨96,48⟩],[⟨128,208⟩,⟨128,64⟩,⟨(-512),(-400)⟩,⟨800,304⟩,⟨(-496),(-368)⟩,⟨64,224⟩]]

without_editor_info theorem star_12 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 12) (values x y) (constants 12) - value root_12 x y ^ 3 =
      value F x y * value starA_12 x y + values x y 12 * value starB_12 x y :=
  identity_power (neighbors 12) nodes (constants 12) F starA_12 starB_12 root_12 12 1 3 (by decide +kernel) x y

without_editor_info def root_13 : Poly := [[⟨0,0⟩,⟨2,1⟩]]

without_editor_info def starA_13 : Poly := [[⟨0,0⟩,⟨0,(-3)⟩]]

without_editor_info def starB_13 : Poly := [[⟨0,0⟩,⟨(-3),(-3)⟩,⟨3,0⟩,⟨(-3),0⟩],[⟨(-2),(-1)⟩,⟨5,(-2)⟩,⟨7,8⟩],[⟨0,(-6)⟩,⟨10,2⟩,⟨(-2),2⟩],[⟨8,4⟩,⟨8,16⟩]]

without_editor_info theorem star_13 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 13) (values x y) (constants 13) - value root_13 x y ^ 3 =
      value F x y * value starA_13 x y + values x y 13 * value starB_13 x y :=
  identity_power (neighbors 13) nodes (constants 13) F starA_13 starB_13 root_13 13 1 3 (by decide +kernel) x y

without_editor_info def root_14 : Poly := [[⟨(-36),(-36)⟩,⟨(-6),(-48)⟩,⟨(-48),(-78)⟩,⟨(-6),(-30)⟩]]

without_editor_info def starA_14 : Poly := [[⟨33840,12708⟩,⟨105696,21096⟩,⟨114660,(-40752)⟩,⟨123408,12924⟩,⟨34740,(-34740)⟩,⟨(-32868),11160⟩,⟨(-41616),39384⟩,⟨3780,31788⟩,⟨11088,6192⟩,⟨(-648),(-864)⟩],[⟨93024,79344⟩,⟨9216,(-89208)⟩,⟨(-28440),(-121752)⟩,⟨(-182952),(-208872)⟩,⟨(-169848),(-103032)⟩,⟨(-140760),(-5688)⟩,⟨5400,83448⟩,⟨23688,18576⟩,⟨864,(-1296)⟩],[⟨179856,166464⟩,⟨112896,(-92160)⟩,⟨39168,(-188352)⟩,⟨(-144000),(-331920)⟩,⟨(-256896),(-262656)⟩,⟨(-168480),(-10800)⟩,⟨13680,61056⟩,⟨8352,5040⟩],[⟨305856,337536⟩,⟨342720,16128⟩,⟨254880,(-160416)⟩,⟨(-33984),(-462816)⟩,⟨(-311328),(-347328)⟩,⟨(-118656),8640⟩,⟨12096,25920⟩,⟨864,0⟩],[⟨429696,608256⟩,⟨673920,337536⟩,⟨580032,(-28224)⟩,⟨42624,(-543168)⟩,⟨(-277056),(-287424)⟩,⟨(-44352),20160⟩,⟨5184,5184⟩],[⟨438912,914688⟩,⟨971136,811008⟩,⟨846720,132480⟩,⟨46080,(-489600)⟩,⟨(-163584),(-147456)⟩,⟨(-6912),10368⟩],[⟨258048,1087488⟩,⟨1034496,1209600⟩,⟨836352,237312⟩,⟨23040,(-292608)⟩,⟨(-48384),(-41472)⟩],[⟨(-59904),976896⟩,⟨723456,1184256⟩,⟨506880,211968⟩,⟨13824,(-82944)⟩],[⟨(-304128),589824⟩,⟨248832,691200⟩,⟨138240,82944⟩],[⟨(-294912),184320⟩,⟨0,165888⟩],[⟨(-110592),0⟩]]

without_editor_info def starB_14 : Poly := [[⟨12276,25308⟩,⟨(-166320),(-64368)⟩,⟨(-257760),(-7740)⟩,⟨(-577584),(-217584)⟩,⟨(-576792),(-167220)⟩,⟨(-581364),(-303876)⟩,⟨(-315504),(-184572)⟩,⟨(-154800),(-164628)⟩,⟨(-35532),(-67824)⟩,⟨(-23868),(-32472)⟩,⟨(-7056),4680⟩,⟨864,216⟩],[⟨12564,(-22500)⟩,⟨(-72180),(-173340)⟩,⟨94572,(-173952)⟩,⟨156888,(-348012)⟩,⟨413820,(-207036)⟩,⟨396684,(-234288)⟩,⟨234108,(-133200)⟩,⟨102816,(-25992)⟩,⟨12456,(-36648)⟩,⟨(-28800),(-21816)⟩,⟨864,3456⟩],[⟨120744,48312⟩,⟨44712,78840⟩,⟨317736,501840⟩,⟨252432,606168⟩,⟨440712,962280⟩,⟨447192,551664⟩,⟨157320,208368⟩,⟨85824,5472⟩,⟨(-5472),(-59472)⟩,⟨(-11952),(-1872)⟩],[⟨57168,105840⟩,⟨(-504720),(-318384)⟩,⟨(-551952),(-22464)⟩,⟨(-1056096),(-514800)⟩,⟨(-526608),175824⟩,⟨(-118224),68544⟩,⟨178416,158400⟩,⟨132480,16416⟩,⟨(-22176),(-34848)⟩,⟨0,864⟩]]

without_editor_info theorem star_14 (x y : ℤ) :
    (2 : Eisenstein)^3 * rowProduct (neighbors 14) (values x y) (constants 14) - value root_14 x y ^ 3 =
      value F x y * value starA_14 x y + values x y 14 * value starB_14 x y :=
  identity_power (neighbors 14) nodes (constants 14) F starA_14 starB_14 root_14 14 2 3 (by decide +kernel) x y

without_editor_info def root_15 : Poly := [[⟨0,0⟩,⟨6,4⟩,⟨0,(-2)⟩,⟨(-2),2⟩]]

without_editor_info def starA_15 : Poly := [[⟨6,(-46)⟩,⟨90,6⟩,⟨44,(-46)⟩,⟨60,46⟩,⟨46,56⟩,⟨48,6⟩,⟨(-32),(-2)⟩,⟨2,(-8)⟩,⟨(-2),(-2)⟩],[⟨(-80),(-36)⟩,⟨(-124),(-240)⟩,⟨40,(-232)⟩,⟨204,(-108)⟩,⟨232,100⟩,⟨64,84⟩,⟨(-20),(-4)⟩,⟨(-4),(-8)⟩],[⟨(-160),(-128)⟩,⟨(-80),(-368)⟩,⟨144,(-264)⟩,⟨368,(-56)⟩,⟨280,184⟩,⟨56,80⟩,⟨(-8),0⟩],[⟨(-176),(-208)⟩,⟨48,(-320)⟩,⟨208,(-176)⟩,⟨400,64⟩,⟨176,176⟩,⟨16,32⟩],[⟨(-96),(-192)⟩,⟨128,(-128)⟩,⟨160,(-64)⟩,⟨256,128⟩,⟨32,64⟩],[⟨0,(-64)⟩,⟨64,0⟩,⟨64,0⟩,⟨64,64⟩]]

without_editor_info def starB_15 : Poly := [[⟨(-52),(-6)⟩,⟨(-78),(-136)⟩,⟨51,(-31)⟩,⟨55,33⟩,⟨246,349⟩,⟨(-69),(-50)⟩,⟨(-185),13⟩,⟨(-12),17⟩,⟨20,(-35)⟩,⟨0,8⟩,⟨2,2⟩],[⟨4,(-18)⟩,⟨66,(-10)⟩,⟨160,60⟩,⟨42,82⟩,⟨6,412⟩,⟨0,114⟩,⟨(-248),(-112)⟩,⟨(-98),(-54)⟩,⟨30,(-10)⟩,⟨0,4⟩],[⟨40,92⟩,⟨(-92),36⟩,⟨120,88⟩,⟨44,(-16)⟩,⟨(-152),192⟩,⟨(-104),236⟩,⟨(-232),(-152)⟩,⟨(-128),(-128)⟩,⟨12,(-16)⟩],[⟨(-112),152⟩,⟨(-600),(-328)⟩,⟨(-248),(-296)⟩,⟨56,(-392)⟩,⟨136,(-128)⟩,⟨(-88),168⟩,⟨(-56),(-56)⟩,⟨(-64),(-64)⟩,⟨0,(-8)⟩]]

without_editor_info theorem star_15 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 15) (values x y) (constants 15) - value root_15 x y ^ 3 =
      value F x y * value starA_15 x y + values x y 15 * value starB_15 x y :=
  identity_power (neighbors 15) nodes (constants 15) F starA_15 starB_15 root_15 15 1 3 (by decide +kernel) x y

without_editor_info def root_16 : Poly := [[⟨4,(-4)⟩,⟨(-12),0⟩,⟨12,12⟩,⟨(-4),(-8)⟩]]

without_editor_info def starA_16 : Poly := [[⟨0,(-208)⟩,⟨(-360),360⟩,⟨1256,344⟩,⟨(-1392),(-1464)⟩,⟨408,1312⟩,⟨296,(-424)⟩,⟨(-48),88⟩,⟨0,(-8)⟩],[⟨32,16⟩,⟨0,(-32)⟩,⟨128,16⟩,⟨256,256⟩,⟨(-48),208⟩,⟨(-160),(-32)⟩,⟨(-16),(-48)⟩],[⟨(-32),(-32)⟩,⟨96,(-32)⟩,⟨224,192⟩,⟨(-32),256⟩,⟨(-192),(-32)⟩,⟨(-64),(-96)⟩],[⟨64,0⟩,⟨128,128⟩,⟨0,192⟩,⟨(-128),0⟩,⟨(-64),(-64)⟩]]

without_editor_info def starB_16 : Poly := [[⟨20,192⟩,⟨632,(-340)⟩,⟨(-2580),(-1208)⟩,⟨3348,4564⟩,⟨264,(-4860)⟩,⟨(-4532),624⟩,⟨3712,2276⟩,⟨(-968),(-1832)⟩,⟨136,464⟩,⟨0,(-8)⟩],[⟨152,0⟩,⟨(-1056),(-784)⟩,⟨1656,2960⟩,⟨960,(-3520)⟩,⟨(-5136),(-248)⟩,⟨4736,3376⟩,⟨(-1184),(-2728)⟩,⟨48,848⟩,⟨(-16),(-64)⟩],[⟨(-304),(-384)⟩,⟨768,1920⟩,⟨1360,(-2432)⟩,⟨(-5472),(-992)⟩,⟨5568,4528⟩,⟨(-1184),(-3680)⟩,⟨(-320),1456⟩,⟨(-96),(-224)⟩],[⟨(-64),768⟩,⟨1408,(-1504)⟩,⟨(-4992),(-1664)⟩,⟨6048,5792⟩,⟨(-896),(-4480)⟩,⟨(-1248),2176⟩,⟨(-128),(-448)⟩]]

without_editor_info theorem star_16 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 16) (values x y) (constants 16) - value root_16 x y ^ 3 =
      value F x y * value starA_16 x y + values x y 16 * value starB_16 x y :=
  identity_power (neighbors 16) nodes (constants 16) F starA_16 starB_16 root_16 16 1 3 (by decide +kernel) x y

without_editor_info def root_17 : Poly := [[⟨0,0⟩,⟨0,3⟩,⟨(-3),0⟩,⟨(-3),(-3)⟩]]

without_editor_info def starA_17 : Poly := [[⟨144,(-213)⟩,⟨636,27⟩,⟨699,519⟩,⟨291,507⟩,⟨21,240⟩,⟨(-63),12⟩],[⟨732,(-294)⟩,⟨1368,438⟩,⟨1128,924⟩,⟨66,756⟩,⟨(-228),(-24)⟩,⟨(-6),(-12)⟩],[⟨816,(-936)⟩,⟨2040,0⟩,⟨1452,1080⟩,⟨(-36),456⟩,⟨(-72),(-36)⟩],[⟨456,(-1704)⟩,⟨1968,(-576)⟩,⟨1032,744⟩,⟨(-48),120⟩],[⟨(-144),(-1920)⟩,⟨1104,(-672)⟩,⟨336,240⟩],[⟨(-384),(-1248)⟩,⟨288,(-288)⟩],[⟨(-192),(-384)⟩]]

without_editor_info def starB_17 : Poly := [[⟨348,153⟩,⟨(-114),330⟩,⟨(-324),(-285)⟩,⟨(-465),(-285)⟩,⟨(-165),(-711)⟩,⟨282,(-90)⟩,⟨198,51⟩,⟨21,90⟩,⟨(-27),(-27)⟩],[⟨288,27⟩,⟨(-231),210⟩,⟨(-678),(-519)⟩,⟨(-765),(-555)⟩,⟨(-732),(-897)⟩,⟨42,(-582)⟩,⟨348,126⟩,⟨(-6),60⟩],[⟨480,150⟩,⟨(-462),624⟩,⟨(-1176),(-558)⟩,⟨(-810),90⟩,⟨(-1500),(-882)⟩,⟨(-120),(-744)⟩,⟨168,84⟩],[⟨1152,636⟩,⟨(-36),1920⟩,⟨(-1008),84⟩,⟨(-828),804⟩,⟨(-1512),(-732)⟩,⟨0,(-288)⟩]]

without_editor_info theorem star_17 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 17) (values x y) (constants 17) - value root_17 x y ^ 3 =
      value F x y * value starA_17 x y + values x y 17 * value starB_17 x y :=
  identity_power (neighbors 17) nodes (constants 17) F starA_17 starB_17 root_17 17 1 3 (by decide +kernel) x y

without_editor_info def root_18 : Poly := [[⟨0,0⟩,⟨0,0⟩,⟨0,(-6)⟩]]

without_editor_info def starA_18 : Poly := [[⟨48,36⟩,⟨204,0⟩,⟨(-12),(-144)⟩,⟨48,96⟩,⟨228,(-60)⟩,⟨(-72),(-192)⟩,⟨(-12),0⟩],[⟨96,120⟩,⟨432,240⟩,⟨528,(-216)⟩,⟨48,(-720)⟩,⟨(-240),(-432)⟩,⟨(-96),(-48)⟩],[⟨144,48⟩,⟨480,(-192)⟩,⟨288,(-768)⟩,⟨(-288),(-768)⟩,⟨(-240),(-240)⟩],[⟨192,0⟩,⟨192,(-384)⟩,⟨(-192),(-768)⟩,⟨(-192),(-384)⟩],[⟨0,(-192)⟩,⟨0,(-384)⟩,⟨0,(-192)⟩]]

without_editor_info def starB_18 : Poly := [[⟨12,48⟩,⟨240,192⟩,⟨120,(-264)⟩,⟨(-456),(-372)⟩,⟨(-240),60⟩,⟨(-240),12⟩,⟨144,480⟩,⟨204,120⟩,⟨0,(-12)⟩],[⟨36,24⟩,⟨(-60),(-360)⟩,⟨(-708),(-432)⟩,⟨(-168),564⟩,⟨108,264⟩,⟨(-336),324⟩,⟨288,432⟩,⟨72,(-24)⟩],[⟨72,(-48)⟩,⟨(-360),(-144)⟩,⟨(-72),960⟩,⟨984,792⟩,⟨(-120),(-432)⟩,⟨(-24),456⟩,⟨288,192⟩],[⟨(-240),(-96)⟩,⟨(-240),672⟩,⟨1776,1440⟩,⟨1056,(-864)⟩,⟨(-1104),(-864)⟩,⟨(-96),384⟩]]

without_editor_info theorem star_18 (x y : ℤ) :
    (2 : Eisenstein)^3 * rowProduct (neighbors 18) (values x y) (constants 18) - value root_18 x y ^ 3 =
      value F x y * value starA_18 x y + values x y 18 * value starB_18 x y :=
  identity_power (neighbors 18) nodes (constants 18) F starA_18 starB_18 root_18 18 2 3 (by decide +kernel) x y

without_editor_info def root_19 : Poly := [[⟨8,(-8)⟩,⟨(-16),12⟩,⟨(-12),(-32)⟩,⟨12,20⟩]]

without_editor_info def starA_19 : Poly := [[⟨(-1630),(-3102)⟩,⟨3146,8876⟩,⟨(-11440),(-13354)⟩,⟨20914,15932⟩,⟨(-17324),(-7368)⟩,⟨8304,(-860)⟩,⟨(-3660),(-160)⟩,⟨1028,1302⟩,⟨6,(-436)⟩,⟨(-132),70⟩,⟨34,10⟩,⟨(-2),(-2)⟩],[⟨(-32),(-348)⟩,⟨(-740),(-508)⟩,⟨(-712),(-284)⟩,⟨(-856),372⟩,⟨320,656⟩,⟨16,204⟩,⟨156,(-68)⟩,⟨(-316),(-160)⟩,⟨(-36),68⟩,⟨0,32⟩,⟨4,0⟩],[⟨(-264),(-528)⟩,⟨(-1040),(-352)⟩,⟨(-944),24⟩,⟨(-600),1248⟩,⟨784,1104⟩,⟨424,568⟩,⟨360,(-80)⟩,⟨(-248),(-104)⟩,⟨16,56⟩,⟨0,8⟩],[⟨(-416),(-448)⟩,⟨(-832),64⟩,⟨(-672),464⟩,⟨160,1696⟩,⟨1008,1024⟩,⟨704,576⟩,⟨304,(-192)⟩,⟨(-128),(-32)⟩,⟨16,16⟩],[⟨(-288),(-160)⟩,⟨(-288),288⟩,⟨(-128),544⟩,⟨576,1120⟩,⟨704,480⟩,⟨512,224⟩,⟨96,(-192)⟩,⟨(-32),0⟩],[⟨(-64),0⟩,⟨0,128⟩,⟨64,192⟩,⟨256,256⟩,⟨192,64⟩,⟨128,0⟩,⟨0,(-64)⟩]]

without_editor_info def starB_19 : Poly := [[⟨27,(-64)⟩,⟨4089,1929⟩,⟨(-15393),(-5649)⟩,⟨27249,(-3179)⟩,⟨(-23800),30258⟩,⟨(-2651),(-53524)⟩,⟨27768,48162⟩,⟨(-23254),(-22101)⟩,⟨8162,5191⟩,⟨(-1232),(-1203)⟩,⟨165,532⟩,⟨108,(-102)⟩,⟨(-34),(-8)⟩,⟨2,2⟩],[⟨(-2898),(-1316)⟩,⟨11638,2504⟩,⟨(-22338),8282⟩,⟨16944,(-36294)⟩,⟨16074,65976⟩,⟨(-41676),(-60376)⟩,⟨36490,27254⟩,⟨(-14862),(-6712)⟩,⟨3218,2016⟩,⟨(-348),(-1086)⟩,⟨(-110),194⟩,⟨64,(-24)⟩,⟨(-8),(-4)⟩],[⟨(-2444),3288⟩,⟨7988,(-13032)⟩,⟨3124,40484⟩,⟨(-33104),(-69132)⟩,⟨63188,66276⟩,⟨(-53400),(-32864)⟩,⟨23656,4348⟩,⟨(-7932),(-3232)⟩,⟨1216,2568⟩,⟨352,(-508)⟩,⟨(-160),(-16)⟩,⟨16,0⟩],[⟨6784,11920⟩,⟨(-13696),(-36760)⟩,⟨44720,52400⟩,⟨(-85560),(-64160)⟩,⟨69536,29824⟩,⟨(-33880),2784⟩,⟨14224,(-240)⟩,⟨(-5384),(-5880)⟩,⟨(-400),1840⟩,⟨496,(-64)⟩,⟨(-80),(-48)⟩]]

without_editor_info theorem star_19 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 19) (values x y) (constants 19) - value root_19 x y ^ 3 =
      value F x y * value starA_19 x y + values x y 19 * value starB_19 x y :=
  identity_power (neighbors 19) nodes (constants 19) F starA_19 starB_19 root_19 19 1 3 (by decide +kernel) x y

without_editor_info def root_20 : Poly := [[],[⟨(-4),0⟩],[⟨0,(-8)⟩]]

without_editor_info def starA_20 : Poly := [[⟨(-20),28⟩,⟨28,20⟩,⟨(-20),4⟩,⟨8,8⟩,⟨(-16),8⟩],[⟨(-56),(-80)⟩,⟨(-40),(-16)⟩,⟨(-24),(-24)⟩,⟨(-8),24⟩,⟨(-8),0⟩],[⟨32,(-32)⟩,⟨0,0⟩,⟨16,(-16)⟩,⟨(-32),0⟩],[⟨64,32⟩,⟨(-32),(-96)⟩],[⟨(-64),(-64)⟩,⟨128,0⟩],[⟨128,0⟩]]

without_editor_info def starB_20 : Poly := [[⟨(-28),(-48)⟩,⟨56,76⟩,⟨(-60),(-52)⟩,⟨76,64⟩,⟨(-44),(-20)⟩,⟨32,24⟩,⟨(-16),8⟩],[⟨108,72⟩,⟨(-120),(-24)⟩,⟨40,(-40)⟩,⟨(-84),16⟩,⟨0,(-24)⟩,⟨0,32⟩,⟨(-8),0⟩],[⟨(-40),48⟩,⟨(-96),(-144)⟩,⟨112,80⟩,⟨(-88),(-64)⟩,⟨48,16⟩,⟨(-32),0⟩],[⟨(-80),32⟩,⟨128,(-64)⟩,⟨(-64),64⟩,⟨(-48),(-128)⟩]]

without_editor_info theorem star_20 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 20) (values x y) (constants 20) - value root_20 x y ^ 3 =
      value F x y * value starA_20 x y + values x y 20 * value starB_20 x y :=
  identity_power (neighbors 20) nodes (constants 20) F starA_20 starB_20 root_20 20 1 3 (by decide +kernel) x y

without_editor_info def root_21 : Poly := [[⟨2,(-2)⟩,⟨2,4⟩,⟨(-4),(-2)⟩]]

without_editor_info def starA_21 : Poly := [[⟨(-20),(-20)⟩,⟨24,(-24)⟩,⟨24,48⟩,⟨(-20),4⟩],[⟨8,0⟩,⟨0,(-8)⟩,⟨(-8),(-8)⟩]]

without_editor_info def starB_21 : Poly := [[⟨26,22⟩,⟨(-58),16⟩,⟨(-58),(-144)⟩,⟨166,80⟩,⟨(-48),78⟩,⟨(-44),(-44)⟩],[⟨(-24),(-4)⟩,⟨(-20),(-84)⟩,⟨152,84⟩,⟨(-84),72⟩,⟨(-88),(-92)⟩],[⟨0,(-40)⟩,⟨120,72⟩,⟨(-112),56⟩,⟨(-136),(-160)⟩,⟨0,(-8)⟩],[⟨80,64⟩,⟨(-96),48⟩,⟨(-144),(-240)⟩,⟨32,(-32)⟩]]

without_editor_info theorem star_21 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 21) (values x y) (constants 21) - value root_21 x y ^ 3 =
      value F x y * value starA_21 x y + values x y 21 * value starB_21 x y :=
  identity_power (neighbors 21) nodes (constants 21) F starA_21 starB_21 root_21 21 1 3 (by decide +kernel) x y

without_editor_info def root_22 : Poly := [[⟨0,(-6)⟩,⟨6,3⟩,⟨0,(-9)⟩]]

without_editor_info def starA_22 : Poly := [[⟨324,648⟩,⟨0,0⟩,⟨729,1458⟩,⟨729,0⟩]]

without_editor_info def starB_22 : Poly := [[⟨252,(-144)⟩,⟨0,0⟩,⟨513,(-270)⟩,⟨(-459),(-432)⟩],[⟨216,648⟩,⟨216,(-216)⟩,⟨648,1296⟩,⟨648,0⟩],[⟨(-1296),0⟩,⟨0,0⟩,⟨(-1944),0⟩,⟨648,1296⟩],[⟨(-864),(-1728)⟩,⟨0,0⟩,⟨(-1944),(-3888)⟩,⟨(-1944),0⟩]]

without_editor_info theorem star_22 (x y : ℤ) :
    (3 : Eisenstein)^3 * rowProduct (neighbors 22) (values x y) (constants 22) - value root_22 x y ^ 3 =
      value F x y * value starA_22 x y + values x y 22 * value starB_22 x y :=
  identity_power (neighbors 22) nodes (constants 22) F starA_22 starB_22 root_22 22 3 3 (by decide +kernel) x y

without_editor_info def root_23 : Poly := [[⟨2,(-2)⟩]]

without_editor_info def starA_23 : Poly := [[⟨108,(-108)⟩]]

without_editor_info def starB_23 : Poly := [[⟨84,108⟩,⟨0,0⟩,⟨216,216⟩],[⟨(-192),(-384)⟩,⟨(-432),0⟩],[⟨(-576),(-864)⟩],[⟨(-288),288⟩]]

without_editor_info theorem star_23 (x y : ℤ) :
    (3 : Eisenstein)^3 * rowProduct (neighbors 23) (values x y) (constants 23) - value root_23 x y ^ 3 =
      value F x y * value starA_23 x y + values x y 23 * value starB_23 x y :=
  identity_power (neighbors 23) nodes (constants 23) F starA_23 starB_23 root_23 23 3 3 (by decide +kernel) x y

without_editor_info def root_24 : Poly := [[⟨0,(-1)⟩,⟨0,0⟩,⟨1,0⟩]]

without_editor_info def starA_24 : Poly := [[⟨(-1),1⟩,⟨1,2⟩,⟨(-2),(-1)⟩,⟨(-1),1⟩]]

without_editor_info def starB_24 : Poly := [[⟨(-1),(-5)⟩,⟨(-7),(-8)⟩,⟨(-8),(-7)⟩,⟨(-9),(-3)⟩,⟨(-6),0⟩,⟨(-2),2⟩],[⟨(-4),(-8)⟩,⟨(-20),(-16)⟩,⟨(-24),(-12)⟩,⟨(-20),(-4)⟩,⟨(-4),4⟩],[⟨(-8),(-8)⟩,⟨(-16),(-8)⟩,⟨(-16),(-8)⟩,⟨(-8),0⟩],[⟨8,(-8)⟩,⟨(-8),(-16)⟩,⟨16,8⟩,⟨8,(-8)⟩]]

without_editor_info theorem star_24 (x y : ℤ) :
    (1 : Eisenstein)^3 * rowProduct (neighbors 24) (values x y) (constants 24) - value root_24 x y ^ 3 =
      value F x y * value starA_24 x y + values x y 24 * value starB_24 x y :=
  identity_power (neighbors 24) nodes (constants 24) F starA_24 starB_24 root_24 24 1 3 (by decide +kernel) x y

without_editor_info def bezA_0 : Poly := [[⟨(-1),0⟩]]

without_editor_info def bezB_0 : Poly := [[⟨(-1),(-1)⟩,⟨(-1),(-1)⟩,⟨(-1),0⟩]]

without_editor_info def bezC_0 : Poly := [[⟨1,0⟩],[⟨0,1⟩],[⟨(-2),(-2)⟩],[⟨4,0⟩]]

without_editor_info theorem bezout_0 (x y : ℤ) :
    value F x y * value bezA_0 x y + values x y 0 * value bezB_0 x y +
      values x y 4 * value bezC_0 x y = (2 : Eisenstein) :=
  bezout F (nodes 0) (nodes 4) bezA_0 bezB_0 bezC_0 2 (by decide +kernel) x y

without_editor_info def bezA_1 : Poly := [[⟨(-2),(-1)⟩]]

without_editor_info def bezB_1 : Poly := [[⟨(-1),(-2)⟩,⟨(-1),(-2)⟩,⟨(-2),(-1)⟩],[⟨1,(-1)⟩],[⟨(-2),(-4)⟩],[⟨(-8),(-4)⟩]]

without_editor_info def bezC_1 : Poly := [[],[⟨(-1),1⟩],[⟨2,4⟩],[⟨8,4⟩]]

without_editor_info theorem bezout_1 (x y : ℤ) :
    value F x y * value bezA_1 x y + values x y 0 * value bezB_1 x y +
      values x y 10 * value bezC_1 x y = (3 : Eisenstein) :=
  bezout F (nodes 0) (nodes 10) bezA_1 bezB_1 bezC_1 3 (by decide +kernel) x y

without_editor_info def bezA_2 : Poly := [[⟨(-2),(-1)⟩]]

without_editor_info def bezB_2 : Poly := [[⟨(-1),(-2)⟩,⟨(-1),(-2)⟩,⟨(-2),(-1)⟩],[⟨1,(-1)⟩],[⟨(-2),2⟩],[⟨4,(-4)⟩]]

without_editor_info def bezC_2 : Poly := [[],[⟨2,1⟩],[⟨(-4),(-2)⟩],[⟨8,4⟩]]

without_editor_info theorem bezout_2 (x y : ℤ) :
    value F x y * value bezA_2 x y + values x y 0 * value bezB_2 x y +
      values x y 11 * value bezC_2 x y = (3 : Eisenstein) :=
  bezout F (nodes 0) (nodes 11) bezA_2 bezB_2 bezC_2 3 (by decide +kernel) x y

without_editor_info def bezA_3 : Poly := [[⟨1,0⟩]]

without_editor_info def bezB_3 : Poly := [[⟨(-1),(-2)⟩,⟨1,1⟩,⟨1,0⟩],[⟨3,0⟩],[⟨2,4⟩],[⟨(-4),0⟩]]

without_editor_info def bezC_3 : Poly := [[⟨(-2),(-3)⟩],[⟨3,0⟩],[⟨2,4⟩],[⟨(-4),0⟩]]

without_editor_info theorem bezout_3 (x y : ℤ) :
    value F x y * value bezA_3 x y + values x y 0 * value bezB_3 x y +
      values x y 15 * value bezC_3 x y = (3 : Eisenstein) :=
  bezout F (nodes 0) (nodes 15) bezA_3 bezB_3 bezC_3 3 (by decide +kernel) x y

without_editor_info def bezA_4 : Poly := [[⟨1,(-1)⟩]]

without_editor_info def bezB_4 : Poly := [[⟨(-2),(-4)⟩,⟨2,1⟩,⟨1,(-1)⟩],[⟨(-3),3⟩],[⟨6,6⟩],[⟨4,(-4)⟩]]

without_editor_info def bezC_4 : Poly := [[⟨4,5⟩],[⟨3,(-3)⟩],[⟨(-6),(-6)⟩],[⟨(-4),4⟩]]

without_editor_info theorem bezout_4 (x y : ℤ) :
    value F x y * value bezA_4 x y + values x y 0 * value bezB_4 x y +
      values x y 16 * value bezC_4 x y = (6 : Eisenstein) :=
  bezout F (nodes 0) (nodes 16) bezA_4 bezB_4 bezC_4 6 (by decide +kernel) x y

without_editor_info def bezA_5 : Poly := [[⟨(-1),0⟩]]

without_editor_info def bezB_5 : Poly := [[⟨0,1⟩,⟨0,(-1)⟩,⟨(-1),0⟩]]

without_editor_info def bezC_5 : Poly := [[⟨1,0⟩],[⟨0,1⟩],[⟨(-2),(-2)⟩],[⟨4,0⟩]]

without_editor_info theorem bezout_5 (x y : ℤ) :
    value F x y * value bezA_5 x y + values x y 1 * value bezB_5 x y +
      values x y 4 * value bezC_5 x y = (1 : Eisenstein) :=
  bezout F (nodes 1) (nodes 4) bezA_5 bezB_5 bezC_5 1 (by decide +kernel) x y

without_editor_info def bezA_6 : Poly := [[⟨(-1),(-1)⟩]]

without_editor_info def bezB_6 : Poly := [[⟨(-1),0⟩,⟨1,0⟩,⟨(-1),(-1)⟩]]

without_editor_info def bezC_6 : Poly := [[],[⟨0,(-1)⟩],[⟨2,0⟩],[⟨4,4⟩]]

without_editor_info theorem bezout_6 (x y : ℤ) :
    value F x y * value bezA_6 x y + values x y 1 * value bezB_6 x y +
      values x y 5 * value bezC_6 x y = (1 : Eisenstein) :=
  bezout F (nodes 1) (nodes 5) bezA_6 bezB_6 bezC_6 1 (by decide +kernel) x y

without_editor_info def bezA_7 : Poly := [[⟨(-1),(-1)⟩]]

without_editor_info def bezB_7 : Poly := [[⟨(-1),0⟩,⟨1,0⟩,⟨(-1),(-1)⟩]]

without_editor_info def bezC_7 : Poly := [[⟨1,1⟩],[⟨0,(-1)⟩],[⟨(-2),0⟩],[⟨4,4⟩]]

without_editor_info theorem bezout_7 (x y : ℤ) :
    value F x y * value bezA_7 x y + values x y 1 * value bezB_7 x y +
      values x y 6 * value bezC_7 x y = (2 : Eisenstein) :=
  bezout F (nodes 1) (nodes 6) bezA_7 bezB_7 bezC_7 2 (by decide +kernel) x y

without_editor_info def bezA_8 : Poly := [[⟨(-2),(-2)⟩]]

without_editor_info def bezB_8 : Poly := [[⟨(-9),(-7)⟩,⟨2,0⟩,⟨(-2),(-2)⟩],[⟨0,(-8)⟩],[⟨8,0⟩],[⟨8,8⟩]]

without_editor_info def bezC_8 : Poly := [[⟨(-7),(-7)⟩],[⟨0,(-8)⟩],[⟨8,0⟩],[⟨8,8⟩]]

without_editor_info theorem bezout_8 (x y : ℤ) :
    value F x y * value bezA_8 x y + values x y 1 * value bezB_8 x y +
      values x y 15 * value bezC_8 x y = (16 : Eisenstein) :=
  bezout F (nodes 1) (nodes 15) bezA_8 bezB_8 bezC_8 16 (by decide +kernel) x y

without_editor_info def bezA_9 : Poly := [[⟨0,(-1)⟩]]

without_editor_info def bezB_9 : Poly := [[⟨(-1),0⟩,⟨1,1⟩,⟨0,(-1)⟩],[⟨0,1⟩],[⟨0,2⟩],[⟨0,4⟩]]

without_editor_info def bezC_9 : Poly := [[⟨0,1⟩],[⟨0,1⟩],[⟨0,2⟩],[⟨0,4⟩]]

without_editor_info theorem bezout_9 (x y : ℤ) :
    value F x y * value bezA_9 x y + values x y 1 * value bezB_9 x y +
      values x y 19 * value bezC_9 x y = (1 : Eisenstein) :=
  bezout F (nodes 1) (nodes 19) bezA_9 bezB_9 bezC_9 1 (by decide +kernel) x y

without_editor_info def bezA_10 : Poly := [[⟨(-1),(-1)⟩]]

without_editor_info def bezB_10 : Poly := [[⟨(-1),0⟩,⟨1,0⟩,⟨(-1),(-1)⟩]]

without_editor_info def bezC_10 : Poly := [[⟨1,1⟩],[],[],[⟨8,8⟩]]

without_editor_info theorem bezout_10 (x y : ℤ) :
    value F x y * value bezA_10 x y + values x y 1 * value bezB_10 x y +
      values x y 24 * value bezC_10 x y = (1 : Eisenstein) :=
  bezout F (nodes 1) (nodes 24) bezA_10 bezB_10 bezC_10 1 (by decide +kernel) x y

without_editor_info def bezA_11 : Poly := [[⟨(-1),0⟩]]

without_editor_info def bezB_11 : Poly := [[⟨0,1⟩,⟨0,1⟩,⟨(-1),0⟩]]

without_editor_info def bezC_11 : Poly := [[⟨1,0⟩],[⟨(-1),(-1)⟩],[⟨0,2⟩],[⟨4,0⟩]]

without_editor_info theorem bezout_11 (x y : ℤ) :
    value F x y * value bezA_11 x y + values x y 2 * value bezB_11 x y +
      values x y 6 * value bezC_11 x y = (2 : Eisenstein) :=
  bezout F (nodes 2) (nodes 6) bezA_11 bezB_11 bezC_11 2 (by decide +kernel) x y

without_editor_info def bezA_12 : Poly := [[⟨(-1),1⟩]]

without_editor_info def bezB_12 : Poly := [[⟨1,2⟩,⟨1,2⟩,⟨(-1),1⟩],[⟨2,1⟩],[⟨2,4⟩],[⟨(-4),4⟩]]

without_editor_info def bezC_12 : Poly := [[],[⟨(-2),(-1)⟩],[⟨(-2),(-4)⟩],[⟨4,(-4)⟩]]

without_editor_info theorem bezout_12 (x y : ℤ) :
    value F x y * value bezA_12 x y + values x y 2 * value bezB_12 x y +
      values x y 10 * value bezC_12 x y = (3 : Eisenstein) :=
  bezout F (nodes 2) (nodes 10) bezA_12 bezB_12 bezC_12 3 (by decide +kernel) x y

without_editor_info def bezA_13 : Poly := [[⟨(-1),1⟩]]

without_editor_info def bezB_13 : Poly := [[⟨1,2⟩,⟨1,2⟩,⟨(-1),1⟩],[⟨2,1⟩],[⟨(-4),(-2)⟩],[⟨8,4⟩]]

without_editor_info def bezC_13 : Poly := [[],[⟨1,(-1)⟩],[⟨(-2),2⟩],[⟨4,(-4)⟩]]

without_editor_info theorem bezout_13 (x y : ℤ) :
    value F x y * value bezA_13 x y + values x y 2 * value bezB_13 x y +
      values x y 12 * value bezC_13 x y = (3 : Eisenstein) :=
  bezout F (nodes 2) (nodes 12) bezA_13 bezB_13 bezC_13 3 (by decide +kernel) x y

without_editor_info def bezA_14 : Poly := [[⟨1,0⟩]]

without_editor_info def bezB_14 : Poly := [[⟨1,2⟩,⟨0,(-1)⟩,⟨1,0⟩],[⟨3,0⟩],[⟨(-2),(-4)⟩],[⟨(-4),0⟩]]

without_editor_info def bezC_14 : Poly := [[⟨1,3⟩],[⟨3,0⟩],[⟨(-2),(-4)⟩],[⟨(-4),0⟩]]

without_editor_info theorem bezout_14 (x y : ℤ) :
    value F x y * value bezA_14 x y + values x y 2 * value bezB_14 x y +
      values x y 19 * value bezC_14 x y = (3 : Eisenstein) :=
  bezout F (nodes 2) (nodes 19) bezA_14 bezB_14 bezC_14 3 (by decide +kernel) x y

without_editor_info def bezA_15 : Poly := [[⟨2,1⟩]]

without_editor_info def bezB_15 : Poly := [[⟨2,4⟩,⟨1,(-1)⟩,⟨2,1⟩],[⟨(-6),(-3)⟩],[⟨0,(-6)⟩],[⟨8,4⟩]]

without_editor_info def bezC_15 : Poly := [[⟨(-1),(-5)⟩],[⟨6,3⟩],[⟨0,6⟩],[⟨(-8),(-4)⟩]]

without_editor_info theorem bezout_15 (x y : ℤ) :
    value F x y * value bezA_15 x y + values x y 2 * value bezB_15 x y +
      values x y 21 * value bezC_15 x y = (6 : Eisenstein) :=
  bezout F (nodes 2) (nodes 21) bezA_15 bezB_15 bezC_15 6 (by decide +kernel) x y

without_editor_info def bezA_16 : Poly := [[⟨2,1⟩]]

without_editor_info def bezB_16 : Poly := [[⟨(-1),(-2)⟩,⟨(-2),(-1)⟩,⟨2,1⟩],[⟨3,(-3)⟩],[⟨6,6⟩],[⟨(-4),4⟩]]

without_editor_info def bezC_16 : Poly := [[⟨(-1),(-5)⟩],[⟨6,3⟩],[⟨0,6⟩],[⟨(-8),(-4)⟩]]

without_editor_info theorem bezout_16 (x y : ℤ) :
    value F x y * value bezA_16 x y + values x y 3 * value bezB_16 x y +
      values x y 13 * value bezC_16 x y = (3 : Eisenstein) :=
  bezout F (nodes 3) (nodes 13) bezA_16 bezB_16 bezC_16 3 (by decide +kernel) x y

without_editor_info def bezA_17 : Poly := [[⟨(-1),1⟩]]

without_editor_info def bezB_17 : Poly := [[⟨(-7),(-2)⟩,⟨1,(-1)⟩,⟨(-1),1⟩],[⟨3,6⟩],[⟨0,(-6)⟩],[⟨(-4),4⟩]]

without_editor_info def bezC_17 : Poly := [[⟨5,4⟩],[⟨(-3),(-6)⟩],[⟨0,6⟩],[⟨4,(-4)⟩]]

without_editor_info theorem bezout_17 (x y : ℤ) :
    value F x y * value bezA_17 x y + values x y 3 * value bezB_17 x y +
      values x y 16 * value bezC_17 x y = (12 : Eisenstein) :=
  bezout F (nodes 3) (nodes 16) bezA_17 bezB_17 bezC_17 12 (by decide +kernel) x y

without_editor_info def bezA_18 : Poly := [[⟨1,(-1)⟩]]

without_editor_info def bezB_18 : Poly := [[⟨1,2⟩,⟨(-1),1⟩,⟨1,(-1)⟩],[⟨6,3⟩],[⟨0,(-6)⟩],[⟨(-8),(-4)⟩]]

without_editor_info def bezC_18 : Poly := [[⟨4,5⟩],[⟨3,(-3)⟩],[⟨(-6),(-6)⟩],[⟨(-4),4⟩]]

without_editor_info theorem bezout_18 (x y : ℤ) :
    value F x y * value bezA_18 x y + values x y 3 * value bezB_18 x y +
      values x y 18 * value bezC_18 x y = (3 : Eisenstein) :=
  bezout F (nodes 3) (nodes 18) bezA_18 bezB_18 bezC_18 3 (by decide +kernel) x y

without_editor_info def bezA_19 : Poly := [[⟨(-2),(-1)⟩]]

without_editor_info def bezB_19 : Poly := [[⟨(-5),2⟩,⟨2,1⟩,⟨(-2),(-1)⟩],[⟨(-3),(-6)⟩],[⟨6,6⟩],[⟨(-8),(-4)⟩]]

without_editor_info def bezC_19 : Poly := [[⟨1,(-4)⟩],[⟨3,6⟩],[⟨(-6),(-6)⟩],[⟨8,4⟩]]

without_editor_info theorem bezout_19 (x y : ℤ) :
    value F x y * value bezA_19 x y + values x y 3 * value bezB_19 x y +
      values x y 21 * value bezC_19 x y = (12 : Eisenstein) :=
  bezout F (nodes 3) (nodes 21) bezA_19 bezB_19 bezC_19 12 (by decide +kernel) x y

without_editor_info def bezA_20 : Poly := [[⟨1,1⟩]]

without_editor_info def bezB_20 : Poly := [[⟨1,1⟩,⟨1,1⟩,⟨1,1⟩],[⟨1,0⟩],[⟨0,2⟩],[⟨(-4),(-4)⟩]]

without_editor_info def bezC_20 : Poly := [[⟨(-2),(-2)⟩,⟨(-1),(-1)⟩,⟨(-1),(-1)⟩]]

without_editor_info theorem bezout_20 (x y : ℤ) :
    value F x y * value bezA_20 x y + values x y 4 * value bezB_20 x y +
      values x y 15 * value bezC_20 x y = (1 : Eisenstein) :=
  bezout F (nodes 4) (nodes 15) bezA_20 bezB_20 bezC_20 1 (by decide +kernel) x y

without_editor_info def bezA_21 : Poly := [[⟨(-1),(-1)⟩]]

without_editor_info def bezB_21 : Poly := [[⟨(-2),(-3)⟩,⟨1,2⟩,⟨0,(-1)⟩],[⟨(-1),0⟩],[⟨0,(-2)⟩],[⟨4,4⟩]]

without_editor_info def bezC_21 : Poly := [[⟨3,4⟩,⟨(-1),(-2)⟩,⟨0,1⟩]]

without_editor_info theorem bezout_21 (x y : ℤ) :
    value F x y * value bezA_21 x y + values x y 4 * value bezB_21 x y +
      values x y 17 * value bezC_21 x y = (6 : Eisenstein) :=
  bezout F (nodes 4) (nodes 17) bezA_21 bezB_21 bezC_21 6 (by decide +kernel) x y

without_editor_info def bezA_22 : Poly := [[⟨(-1),(-2)⟩]]

without_editor_info def bezB_22 : Poly := [[⟨(-4),(-5)⟩,⟨(-3),(-3)⟩,⟨(-2),(-1)⟩],[⟨(-2),(-1)⟩],[⟨2,(-2)⟩],[⟨4,8⟩]]

without_editor_info def bezC_22 : Poly := [[⟨5,7⟩,⟨3,3⟩,⟨2,1⟩]]

without_editor_info theorem bezout_22 (x y : ℤ) :
    value F x y * value bezA_22 x y + values x y 4 * value bezB_22 x y +
      values x y 18 * value bezC_22 x y = (9 : Eisenstein) :=
  bezout F (nodes 4) (nodes 18) bezA_22 bezB_22 bezC_22 9 (by decide +kernel) x y

without_editor_info def bezA_23 : Poly := [[⟨0,1⟩]]

without_editor_info def bezB_23 : Poly := [[⟨0,(-1)⟩],[⟨1,1⟩],[⟨(-2),0⟩],[⟨0,(-4)⟩]]

without_editor_info def bezC_23 : Poly := [[⟨(-1),0⟩,⟨1,0⟩,⟨0,1⟩]]

without_editor_info theorem bezout_23 (x y : ℤ) :
    value F x y * value bezA_23 x y + values x y 4 * value bezB_23 x y +
      values x y 20 * value bezC_23 x y = (2 : Eisenstein) :=
  bezout F (nodes 4) (nodes 20) bezA_23 bezB_23 bezC_23 2 (by decide +kernel) x y

without_editor_info def bezA_24 : Poly := [[⟨(-1),1⟩]]

without_editor_info def bezB_24 : Poly := [[⟨2,(-2)⟩,⟨0,0⟩,⟨1,(-1)⟩],[⟨1,2⟩],[⟨(-4),(-2)⟩],[⟨4,(-4)⟩]]

without_editor_info def bezC_24 : Poly := [[⟨(-1),1⟩,⟨0,0⟩,⟨(-1),1⟩]]

without_editor_info theorem bezout_24 (x y : ℤ) :
    value F x y * value bezA_24 x y + values x y 4 * value bezB_24 x y +
      values x y 21 * value bezC_24 x y = (3 : Eisenstein) :=
  bezout F (nodes 4) (nodes 21) bezA_24 bezB_24 bezC_24 3 (by decide +kernel) x y

without_editor_info def bezA_25 : Poly := [[⟨(-1),0⟩]]

without_editor_info def bezB_25 : Poly := [[⟨(-2),(-2)⟩,⟨1,1⟩,⟨(-1),(-1)⟩],[⟨(-1),(-1)⟩],[⟨0,(-2)⟩],[⟨4,0⟩]]

without_editor_info def bezC_25 : Poly := [[⟨2,2⟩,⟨(-1),(-1)⟩,⟨1,1⟩]]

without_editor_info theorem bezout_25 (x y : ℤ) :
    value F x y * value bezA_25 x y + values x y 5 * value bezB_25 x y +
      values x y 11 * value bezC_25 x y = (3 : Eisenstein) :=
  bezout F (nodes 5) (nodes 11) bezA_25 bezB_25 bezC_25 3 (by decide +kernel) x y

without_editor_info def bezA_26 : Poly := [[⟨(-2),(-1)⟩]]

without_editor_info def bezB_26 : Poly := [[⟨(-2),(-1)⟩,⟨(-2),(-1)⟩,⟨(-1),1⟩],[⟨(-1),(-2)⟩],[⟨2,(-2)⟩],[⟨8,4⟩]]

without_editor_info def bezC_26 : Poly := [[⟨2,1⟩,⟨2,1⟩,⟨1,(-1)⟩]]

without_editor_info theorem bezout_26 (x y : ℤ) :
    value F x y * value bezA_26 x y + values x y 5 * value bezB_26 x y +
      values x y 12 * value bezC_26 x y = (3 : Eisenstein) :=
  bezout F (nodes 5) (nodes 12) bezA_26 bezB_26 bezC_26 3 (by decide +kernel) x y

without_editor_info def bezA_27 : Poly := [[⟨1,0⟩]]

without_editor_info def bezB_27 : Poly := [[⟨(-2),0⟩,⟨(-1),0⟩,⟨(-1),0⟩],[⟨1,1⟩],[⟨0,2⟩],[⟨(-4),0⟩]]

without_editor_info def bezC_27 : Poly := [[⟨2,0⟩,⟨1,0⟩,⟨1,0⟩]]

without_editor_info theorem bezout_27 (x y : ℤ) :
    value F x y * value bezA_27 x y + values x y 5 * value bezB_27 x y +
      values x y 21 * value bezC_27 x y = (1 : Eisenstein) :=
  bezout F (nodes 5) (nodes 21) bezA_27 bezB_27 bezC_27 1 (by decide +kernel) x y

without_editor_info def bezA_28 : Poly := [[⟨(-1),(-1)⟩]]

without_editor_info def bezB_28 : Poly := [[⟨2,1⟩,⟨(-1),0⟩,⟨1,1⟩],[⟨0,(-1)⟩],[⟨(-2),0⟩],[⟨4,4⟩]]

without_editor_info def bezC_28 : Poly := [[⟨(-1),0⟩,⟨1,0⟩,⟨(-1),(-1)⟩]]

without_editor_info theorem bezout_28 (x y : ℤ) :
    value F x y * value bezA_28 x y + values x y 6 * value bezB_28 x y +
      values x y 10 * value bezC_28 x y = (2 : Eisenstein) :=
  bezout F (nodes 6) (nodes 10) bezA_28 bezB_28 bezC_28 2 (by decide +kernel) x y

without_editor_info def bezA_29 : Poly := [[⟨0,(-1)⟩]]

without_editor_info def bezB_29 : Poly := [[⟨2,1⟩,⟨1,0⟩,⟨1,0⟩],[⟨1,0⟩],[⟨(-2),(-2)⟩],[⟨0,4⟩]]

without_editor_info def bezC_29 : Poly := [[⟨(-2),0⟩,⟨(-1),0⟩,⟨(-1),0⟩]]

without_editor_info theorem bezout_29 (x y : ℤ) :
    value F x y * value bezA_29 x y + values x y 6 * value bezB_29 x y +
      values x y 11 * value bezC_29 x y = (1 : Eisenstein) :=
  bezout F (nodes 6) (nodes 11) bezA_29 bezB_29 bezC_29 1 (by decide +kernel) x y

without_editor_info def bezA_30 : Poly := [[⟨1,2⟩]]

without_editor_info def bezB_30 : Poly := [[⟨1,5⟩,⟨0,3⟩,⟨(-1),1⟩],[⟨(-1),1⟩],[⟨4,2⟩],[⟨(-4),(-8)⟩]]

without_editor_info def bezC_30 : Poly := [[⟨(-2),(-7)⟩,⟨0,(-3)⟩,⟨1,(-1)⟩]]

without_editor_info theorem bezout_30 (x y : ℤ) :
    value F x y * value bezA_30 x y + values x y 6 * value bezB_30 x y +
      values x y 13 * value bezC_30 x y = (9 : Eisenstein) :=
  bezout F (nodes 6) (nodes 13) bezA_30 bezB_30 bezC_30 9 (by decide +kernel) x y

without_editor_info def bezA_31 : Poly := [[⟨0,1⟩]]

without_editor_info def bezB_31 : Poly := [[⟨1,3⟩,⟨(-1),(-2)⟩,⟨1,1⟩],[⟨(-1),0⟩],[⟨2,2⟩],[⟨0,(-4)⟩]]

without_editor_info def bezC_31 : Poly := [[⟨(-1),(-4)⟩,⟨1,2⟩,⟨(-1),(-1)⟩]]

without_editor_info theorem bezout_31 (x y : ℤ) :
    value F x y * value bezA_31 x y + values x y 6 * value bezB_31 x y +
      values x y 14 * value bezC_31 x y = (6 : Eisenstein) :=
  bezout F (nodes 6) (nodes 14) bezA_31 bezB_31 bezC_31 6 (by decide +kernel) x y

without_editor_info def bezA_32 : Poly := [[⟨(-2),(-1)⟩]]

without_editor_info def bezB_32 : Poly := [[⟨4,2⟩,⟨0,0⟩,⟨2,1⟩],[⟨(-1),(-2)⟩],[⟨(-2),2⟩],[⟨8,4⟩]]

without_editor_info def bezC_32 : Poly := [[⟨(-2),(-1)⟩,⟨0,0⟩,⟨(-2),(-1)⟩]]

without_editor_info theorem bezout_32 (x y : ℤ) :
    value F x y * value bezA_32 x y + values x y 6 * value bezB_32 x y +
      values x y 16 * value bezC_32 x y = (3 : Eisenstein) :=
  bezout F (nodes 6) (nodes 16) bezA_32 bezB_32 bezC_32 3 (by decide +kernel) x y

without_editor_info def bezA_33 : Poly := [[⟨0,(-1)⟩]]

without_editor_info def bezB_33 : Poly := [[⟨0,(-1)⟩,⟨0,(-1)⟩,⟨0,(-1)⟩],[⟨1,0⟩],[⟨(-2),(-2)⟩],[⟨0,4⟩]]

without_editor_info def bezC_33 : Poly := [[⟨0,2⟩,⟨0,1⟩,⟨0,1⟩]]

without_editor_info theorem bezout_33 (x y : ℤ) :
    value F x y * value bezA_33 x y + values x y 6 * value bezB_33 x y +
      values x y 19 * value bezC_33 x y = (1 : Eisenstein) :=
  bezout F (nodes 6) (nodes 19) bezA_33 bezB_33 bezC_33 1 (by decide +kernel) x y

without_editor_info def bezA_34 : Poly := [[⟨(-1),0⟩]]

without_editor_info def bezB_34 : Poly := [[⟨1,0⟩],[⟨(-1),(-1)⟩],[⟨0,2⟩],[⟨4,0⟩]]

without_editor_info def bezC_34 : Poly := [[⟨(-1),(-1)⟩,⟨1,1⟩,⟨(-1),0⟩]]

without_editor_info theorem bezout_34 (x y : ℤ) :
    value F x y * value bezA_34 x y + values x y 6 * value bezB_34 x y +
      values x y 20 * value bezC_34 x y = (1 : Eisenstein) :=
  bezout F (nodes 6) (nodes 20) bezA_34 bezB_34 bezC_34 1 (by decide +kernel) x y

without_editor_info def bezA_35 : Poly := [[⟨(-1),1⟩]]

without_editor_info def bezB_35 : Poly := [[⟨(-1),1⟩,⟨(-1),1⟩,⟨(-2),(-1)⟩],[⟨1,2⟩],[⟨4,2⟩],[⟨4,(-4)⟩]]

without_editor_info def bezC_35 : Poly := [[⟨1,(-1)⟩,⟨1,(-1)⟩,⟨2,1⟩]]

without_editor_info theorem bezout_35 (x y : ℤ) :
    value F x y * value bezA_35 x y + values x y 7 * value bezB_35 x y +
      values x y 11 * value bezC_35 x y = (3 : Eisenstein) :=
  bezout F (nodes 7) (nodes 11) bezA_35 bezB_35 bezC_35 3 (by decide +kernel) x y

without_editor_info def bezA_36 : Poly := [[⟨(-1),0⟩]]

without_editor_info def bezB_36 : Poly := [[⟨0,2⟩,⟨0,(-1)⟩,⟨0,1⟩],[⟨0,1⟩],[⟨2,2⟩],[⟨4,0⟩]]

without_editor_info def bezC_36 : Poly := [[⟨0,(-2)⟩,⟨0,1⟩,⟨0,(-1)⟩]]

without_editor_info theorem bezout_36 (x y : ℤ) :
    value F x y * value bezA_36 x y + values x y 7 * value bezB_36 x y +
      values x y 12 * value bezC_36 x y = (3 : Eisenstein) :=
  bezout F (nodes 7) (nodes 12) bezA_36 bezB_36 bezC_36 3 (by decide +kernel) x y

without_editor_info def bezA_37 : Poly := [[⟨1,0⟩]]

without_editor_info def bezB_37 : Poly := [[⟨(-2),0⟩,⟨(-1),0⟩,⟨(-1),0⟩],[⟨0,(-1)⟩],[⟨(-2),(-2)⟩],[⟨(-4),0⟩]]

without_editor_info def bezC_37 : Poly := [[⟨2,0⟩,⟨1,0⟩,⟨1,0⟩]]

without_editor_info theorem bezout_37 (x y : ℤ) :
    value F x y * value bezA_37 x y + values x y 7 * value bezB_37 x y +
      values x y 16 * value bezC_37 x y = (1 : Eisenstein) :=
  bezout F (nodes 7) (nodes 16) bezA_37 bezB_37 bezC_37 1 (by decide +kernel) x y

without_editor_info def bezA_38 : Poly := [[⟨0,1⟩]]

without_editor_info def bezB_38 : Poly := [[],[⟨1,1⟩],[⟨2,0⟩],[⟨0,(-4)⟩]]

without_editor_info def bezC_38 : Poly := [[⟨(-1),0⟩,⟨1,0⟩,⟨0,1⟩]]

without_editor_info theorem bezout_38 (x y : ℤ) :
    value F x y * value bezA_38 x y + values x y 7 * value bezB_38 x y +
      values x y 20 * value bezC_38 x y = (1 : Eisenstein) :=
  bezout F (nodes 7) (nodes 20) bezA_38 bezB_38 bezC_38 1 (by decide +kernel) x y

without_editor_info def bezA_39 : Poly := [[⟨(-1),0⟩]]

without_editor_info def bezB_39 : Poly := [[⟨1,(-1)⟩,⟨1,(-1)⟩,⟨(-1),(-1)⟩],[⟨3,3⟩],[⟨(-4),(-2)⟩],[⟨4,0⟩]]

without_editor_info def bezC_39 : Poly := [[⟨(-2),(-2)⟩,⟨(-1),1⟩,⟨1,1⟩]]

without_editor_info theorem bezout_39 (x y : ℤ) :
    value F x y * value bezA_39 x y + values x y 8 * value bezB_39 x y +
      values x y 11 * value bezC_39 x y = (4 : Eisenstein) :=
  bezout F (nodes 8) (nodes 11) bezA_39 bezB_39 bezC_39 4 (by decide +kernel) x y

without_editor_info def bezA_40 : Poly := [[⟨(-2),(-1)⟩]]

without_editor_info def bezB_40 : Poly := [[⟨2,(-2)⟩,⟨1,2⟩,⟨(-1),1⟩],[⟨3,6⟩],[⟨(-6),(-6)⟩],[⟨8,4⟩]]

without_editor_info def bezC_40 : Poly := [[⟨(-1),(-2)⟩,⟨(-1),(-2)⟩,⟨1,(-1)⟩]]

without_editor_info theorem bezout_40 (x y : ℤ) :
    value F x y * value bezA_40 x y + values x y 8 * value bezB_40 x y +
      values x y 14 * value bezC_40 x y = (9 : Eisenstein) :=
  bezout F (nodes 8) (nodes 14) bezA_40 bezB_40 bezC_40 9 (by decide +kernel) x y

without_editor_info def bezA_41 : Poly := [[⟨0,(-1)⟩]]

without_editor_info def bezB_41 : Poly := [[⟨0,(-2)⟩,⟨0,2⟩,⟨1,0⟩],[⟨(-3),0⟩],[⟨2,(-2)⟩],[⟨0,4⟩]]

without_editor_info def bezC_41 : Poly := [[⟨3,4⟩,⟨0,(-2)⟩,⟨(-1),0⟩]]

without_editor_info theorem bezout_41 (x y : ℤ) :
    value F x y * value bezA_41 x y + values x y 8 * value bezB_41 x y +
      values x y 17 * value bezC_41 x y = (6 : Eisenstein) :=
  bezout F (nodes 8) (nodes 17) bezA_41 bezB_41 bezC_41 6 (by decide +kernel) x y

without_editor_info def bezA_42 : Poly := [[⟨(-1),(-1)⟩]]

without_editor_info def bezB_42 : Poly := [[⟨4,(-7)⟩,⟨(-1),(-3)⟩,⟨(-1),(-1)⟩],[⟨0,3⟩],[⟨(-2),(-4)⟩],[⟨4,4⟩]]

without_editor_info def bezC_42 : Poly := [[⟨(-2),6⟩,⟨1,3⟩,⟨1,1⟩]]

without_editor_info theorem bezout_42 (x y : ℤ) :
    value F x y * value bezA_42 x y + values x y 8 * value bezB_42 x y +
      values x y 19 * value bezC_42 x y = (24 : Eisenstein) :=
  bezout F (nodes 8) (nodes 19) bezA_42 bezB_42 bezC_42 24 (by decide +kernel) x y

without_editor_info def bezA_43 : Poly := [[⟨(-1),0⟩]]

without_editor_info def bezB_43 : Poly := [[⟨2,1⟩,⟨2,1⟩,⟨0,1⟩],[⟨0,(-3)⟩],[⟨(-2),2⟩],[⟨4,0⟩]]

without_editor_info def bezC_43 : Poly := [[⟨0,2⟩,⟨(-2),(-1)⟩,⟨0,(-1)⟩]]

without_editor_info theorem bezout_43 (x y : ℤ) :
    value F x y * value bezA_43 x y + values x y 9 * value bezB_43 x y +
      values x y 12 * value bezC_43 x y = (4 : Eisenstein) :=
  bezout F (nodes 9) (nodes 12) bezA_43 bezB_43 bezC_43 4 (by decide +kernel) x y

without_editor_info def bezA_44 : Poly := [[⟨1,1⟩]]

without_editor_info def bezB_44 : Poly := [[⟨2,2⟩,⟨(-2),(-2)⟩,⟨1,0⟩],[⟨(-3),0⟩],[⟨4,2⟩],[⟨(-4),(-4)⟩]]

without_editor_info def bezC_44 : Poly := [[⟨(-1),(-4)⟩,⟨2,2⟩,⟨(-1),0⟩]]

without_editor_info theorem bezout_44 (x y : ℤ) :
    value F x y * value bezA_44 x y + values x y 9 * value bezB_44 x y +
      values x y 14 * value bezC_44 x y = (6 : Eisenstein) :=
  bezout F (nodes 9) (nodes 14) bezA_44 bezB_44 bezC_44 6 (by decide +kernel) x y

without_editor_info def bezA_45 : Poly := [[⟨0,1⟩]]

without_editor_info def bezB_45 : Poly := [[⟨11,7⟩,⟨2,3⟩,⟨0,1⟩],[⟨(-3),(-3)⟩],[⟨2,4⟩],[⟨0,(-4)⟩]]

without_editor_info def bezC_45 : Poly := [[⟨(-8),(-6)⟩,⟨(-2),(-3)⟩,⟨0,(-1)⟩]]

without_editor_info theorem bezout_45 (x y : ℤ) :
    value F x y * value bezA_45 x y + values x y 9 * value bezB_45 x y +
      values x y 15 * value bezC_45 x y = (24 : Eisenstein) :=
  bezout F (nodes 9) (nodes 15) bezA_45 bezB_45 bezC_45 24 (by decide +kernel) x y

without_editor_info def bezA_46 : Poly := [[⟨(-1),1⟩]]

without_editor_info def bezB_46 : Poly := [[⟨4,2⟩,⟨(-1),(-2)⟩,⟨(-2),(-1)⟩],[⟨(-3),(-6)⟩],[⟨0,6⟩],[⟨4,(-4)⟩]]

without_editor_info def bezC_46 : Poly := [[⟨1,2⟩,⟨1,2⟩,⟨2,1⟩]]

without_editor_info theorem bezout_46 (x y : ℤ) :
    value F x y * value bezA_46 x y + values x y 9 * value bezB_46 x y +
      values x y 17 * value bezC_46 x y = (9 : Eisenstein) :=
  bezout F (nodes 9) (nodes 17) bezA_46 bezB_46 bezC_46 9 (by decide +kernel) x y

without_editor_info def bezA_47 : Poly := [[⟨0,2⟩]]

without_editor_info def bezB_47 : Poly := [[⟨0,(-1)⟩,⟨0,0⟩,⟨0,0⟩,⟨0,(-1)⟩],[⟨0,0⟩,⟨0,0⟩,⟨0,(-2)⟩],[⟨0,0⟩,⟨0,(-4)⟩],[⟨0,(-8)⟩]]

without_editor_info def bezC_47 : Poly := [[⟨(-2),2⟩,⟨1,(-1)⟩,⟨1,2⟩,⟨0,1⟩]]

without_editor_info theorem bezout_47 (x y : ℤ) :
    value F x y * value bezA_47 x y + values x y 10 * value bezB_47 x y +
      values x y 20 * value bezC_47 x y = (4 : Eisenstein) :=
  bezout F (nodes 10) (nodes 20) bezA_47 bezB_47 bezC_47 4 (by decide +kernel) x y

without_editor_info def bezA_48 : Poly := [[⟨0,27⟩]]

without_editor_info def bezB_48 : Poly := [[⟨(-24),(-21)⟩,⟨36,0⟩,⟨18,36⟩],[⟨0,0⟩,⟨0,0⟩,⟨0,(-27)⟩],[⟨0,0⟩,⟨0,(-54)⟩],[⟨0,(-108)⟩]]

without_editor_info def bezC_48 : Poly := [[⟨16,5⟩,⟨(-24),0⟩,⟨(-12),(-24)⟩,⟨0,(-9)⟩]]

without_editor_info theorem bezout_48 (x y : ℤ) :
    value F x y * value bezA_48 x y + values x y 10 * value bezB_48 x y +
      values x y 22 * value bezC_48 x y = (6 : Eisenstein) :=
  bezout F (nodes 10) (nodes 22) bezA_48 bezB_48 bezC_48 6 (by decide +kernel) x y

without_editor_info def bezA_49 : Poly := [[⟨(-27),(-27)⟩]]

without_editor_info def bezB_49 : Poly := [[⟨(-3),21⟩,⟨36,0⟩,⟨(-18),(-36)⟩],[⟨0,0⟩,⟨0,0⟩,⟨27,27⟩],[⟨0,0⟩,⟨54,54⟩],[⟨108,108⟩]]

without_editor_info def bezC_49 : Poly := [[⟨11,(-5)⟩,⟨(-24),0⟩,⟨12,24⟩,⟨9,9⟩]]

without_editor_info theorem bezout_49 (x y : ℤ) :
    value F x y * value bezA_49 x y + values x y 10 * value bezB_49 x y +
      values x y 23 * value bezC_49 x y = (6 : Eisenstein) :=
  bezout F (nodes 10) (nodes 23) bezA_49 bezB_49 bezC_49 6 (by decide +kernel) x y

without_editor_info def bezA_50 : Poly := [[⟨(-6),0⟩]]

without_editor_info def bezB_50 : Poly := [[⟨3,3⟩,⟨0,0⟩,⟨2,4⟩,⟨1,(-1)⟩],[⟨0,0⟩,⟨0,0⟩,⟨(-6),(-6)⟩],[⟨0,0⟩,⟨0,12⟩],[⟨24,0⟩]]

without_editor_info def bezC_50 : Poly := [[⟨0,(-3)⟩,⟨0,0⟩,⟨(-2),(-4)⟩,⟨2,1⟩]]

without_editor_info theorem bezout_50 (x y : ℤ) :
    value F x y * value bezA_50 x y + values x y 11 * value bezB_50 x y +
      values x y 12 * value bezC_50 x y = (6 : Eisenstein) :=
  bezout F (nodes 11) (nodes 12) bezA_50 bezB_50 bezC_50 6 (by decide +kernel) x y

without_editor_info def bezA_51 : Poly := [[⟨2,2⟩]]

without_editor_info def bezB_51 : Poly := [[⟨1,3⟩,⟨1,2⟩,⟨1,2⟩,⟨0,(-1)⟩],[⟨0,0⟩,⟨0,0⟩,⟨2,0⟩],[⟨0,0⟩,⟨0,4⟩],[⟨(-8),(-8)⟩]]

without_editor_info def bezC_51 : Poly := [[⟨(-2),(-4)⟩,⟨(-1),(-2)⟩,⟨(-1),(-2)⟩,⟨(-1),0⟩]]

without_editor_info theorem bezout_51 (x y : ℤ) :
    value F x y * value bezA_51 x y + values x y 12 * value bezB_51 x y +
      values x y 15 * value bezC_51 x y = (2 : Eisenstein) :=
  bezout F (nodes 12) (nodes 15) bezA_51 bezB_51 bezC_51 2 (by decide +kernel) x y

without_editor_info def bezA_52 : Poly := [[⟨(-2),2⟩]]

without_editor_info def bezB_52 : Poly := [[⟨(-1),0⟩,⟨0,3⟩,⟨5,4⟩,⟨0,(-1)⟩],[⟨2,4⟩,⟨4,(-4)⟩,⟨(-4),(-2)⟩],[⟨(-8),(-4)⟩,⟨4,8⟩],[⟨8,(-8)⟩]]

without_editor_info def bezC_52 : Poly := [[⟨3,(-2)⟩,⟨(-6),(-6)⟩,⟨(-2),2⟩,⟨1,0⟩]]

without_editor_info theorem bezout_52 (x y : ℤ) :
    value F x y * value bezA_52 x y + values x y 13 * value bezB_52 x y +
      values x y 14 * value bezC_52 x y = (6 : Eisenstein) :=
  bezout F (nodes 13) (nodes 14) bezA_52 bezB_52 bezC_52 6 (by decide +kernel) x y

without_editor_info def bezA_53 : Poly := [[⟨4,2⟩]]

without_editor_info def bezB_53 : Poly := [[⟨(-1),(-14)⟩,⟨1,(-4)⟩,⟨(-1),(-5)⟩,⟨(-1),1⟩],[⟨2,(-2)⟩,⟨(-8),(-4)⟩,⟨2,4⟩],[⟨4,8⟩,⟨4,(-4)⟩],[⟨(-16),(-8)⟩]]

without_editor_info def bezC_53 : Poly := [[⟨(-3),12⟩,⟨2,10⟩,⟨4,2⟩,⟨(-1),(-2)⟩]]

without_editor_info theorem bezout_53 (x y : ℤ) :
    value F x y * value bezA_53 x y + values x y 13 * value bezB_53 x y +
      values x y 19 * value bezC_53 x y = (24 : Eisenstein) :=
  bezout F (nodes 13) (nodes 19) bezA_53 bezB_53 bezC_53 24 (by decide +kernel) x y

without_editor_info def bezA_54 : Poly := [[⟨(-1),1⟩]]

without_editor_info def bezB_54 : Poly := [[⟨1,(-1)⟩,⟨1,(-1)⟩,⟨2,1⟩],[⟨1,2⟩,⟨2,(-2)⟩,⟨(-2),(-1)⟩],[⟨(-4),(-2)⟩,⟨2,4⟩],[⟨4,(-4)⟩]]

without_editor_info def bezC_54 : Poly := [[⟨0,0⟩,⟨(-8),(-1)⟩,⟨(-1),4⟩,⟨1,(-1)⟩]]

without_editor_info theorem bezout_54 (x y : ℤ) :
    value F x y * value bezA_54 x y + values x y 13 * value bezB_54 x y +
      values x y 24 * value bezC_54 x y = (3 : Eisenstein) :=
  bezout F (nodes 13) (nodes 24) bezA_54 bezB_54 bezC_54 3 (by decide +kernel) x y

without_editor_info def bezA_55 : Poly := [[⟨0,6⟩]]

without_editor_info def bezB_55 : Poly := [[⟨4,(-4)⟩,⟨(-1),1⟩,⟨(-4),(-8)⟩,⟨(-1),(-2)⟩],[⟨6,6⟩,⟨12,12⟩,⟨6,6⟩],[⟨(-12),0⟩,⟨(-12),0⟩],[⟨0,(-24)⟩]]

without_editor_info def bezC_55 : Poly := [[⟨(-4),(-2)⟩,⟨1,(-10)⟩,⟨4,(-1)⟩,⟨1,(-1)⟩]]

without_editor_info theorem bezout_55 (x y : ℤ) :
    value F x y * value bezA_55 x y + values x y 14 * value bezB_55 x y +
      values x y 16 * value bezC_55 x y = (6 : Eisenstein) :=
  bezout F (nodes 14) (nodes 16) bezA_55 bezB_55 bezC_55 6 (by decide +kernel) x y

without_editor_info def bezA_56 : Poly := [[⟨(-6),0⟩]]

without_editor_info def bezB_56 : Poly := [[⟨0,(-6)⟩,⟨8,7⟩,⟨4,(-1)⟩,⟨2,1⟩],[⟨0,6⟩,⟨0,12⟩,⟨0,6⟩],[⟨(-12),(-12)⟩,⟨(-12),(-12)⟩],[⟨24,0⟩]]

without_editor_info def bezC_56 : Poly := [[⟨6,6⟩,⟨1,(-7)⟩,⟨5,1⟩,⟨1,(-1)⟩]]

without_editor_info theorem bezout_56 (x y : ℤ) :
    value F x y * value bezA_56 x y + values x y 14 * value bezB_56 x y +
      values x y 17 * value bezC_56 x y = (18 : Eisenstein) :=
  bezout F (nodes 14) (nodes 17) bezA_56 bezB_56 bezC_56 18 (by decide +kernel) x y

without_editor_info def bezA_57 : Poly := [[⟨4,2⟩]]

without_editor_info def bezB_57 : Poly := [[⟨(-1),(-11)⟩,⟨(-8),(-1)⟩,⟨2,1⟩,⟨(-1),(-2)⟩],[⟨2,(-2)⟩,⟨4,(-4)⟩,⟨2,(-2)⟩],[⟨4,8⟩,⟨4,8⟩],[⟨(-16),(-8)⟩]]

without_editor_info def bezC_57 : Poly := [[⟨(-3),9⟩,⟨2,(-2)⟩,⟨(-8),(-4)⟩,⟨(-1),1⟩]]

without_editor_info theorem bezout_57 (x y : ℤ) :
    value F x y * value bezA_57 x y + values x y 14 * value bezB_57 x y +
      values x y 19 * value bezC_57 x y = (18 : Eisenstein) :=
  bezout F (nodes 14) (nodes 19) bezA_57 bezB_57 bezC_57 18 (by decide +kernel) x y

without_editor_info def bezA_58 : Poly := [[⟨0,27⟩]]

without_editor_info def bezB_58 : Poly := [[⟨(-69),(-21)⟩,⟨(-27),9⟩,⟨(-36),(-18)⟩],[⟨27,27⟩,⟨54,54⟩,⟨27,27⟩],[⟨(-54),0⟩,⟨(-54),0⟩],[⟨0,(-108)⟩]]

without_editor_info def bezC_58 : Poly := [[⟨46,(-4)⟩,⟨18,(-33)⟩,⟨24,(-15)⟩,⟨0,(-9)⟩]]

without_editor_info theorem bezout_58 (x y : ℤ) :
    value F x y * value bezA_58 x y + values x y 14 * value bezB_58 x y +
      values x y 22 * value bezC_58 x y = (6 : Eisenstein) :=
  bezout F (nodes 14) (nodes 22) bezA_58 bezB_58 bezC_58 6 (by decide +kernel) x y

without_editor_info def bezA_59 : Poly := [[⟨(-4),4⟩]]

without_editor_info def bezB_59 : Poly := [[⟨(-2),(-4)⟩,⟨4,(-1)⟩,⟨(-1),(-8)⟩,⟨(-1),1⟩],[⟨(-8),(-4)⟩,⟨8,16⟩,⟨4,(-4)⟩],[⟨(-8),(-16)⟩,⟨(-8),8⟩],[⟨16,(-16)⟩]]

without_editor_info def bezC_59 : Poly := [[⟨2,4⟩,⟨8,7⟩,⟨(-5),(-4)⟩,⟨(-1),1⟩]]

without_editor_info theorem bezout_59 (x y : ℤ) :
    value F x y * value bezA_59 x y + values x y 15 * value bezB_59 x y +
      values x y 16 * value bezC_59 x y = (12 : Eisenstein) :=
  bezout F (nodes 15) (nodes 16) bezA_59 bezB_59 bezC_59 12 (by decide +kernel) x y

without_editor_info def bezA_60 : Poly := [[⟨2,(-2)⟩]]

without_editor_info def bezB_60 : Poly := [[⟨(-11),(-10)⟩,⟨4,(-1)⟩,⟨(-1),4⟩,⟨2,1⟩],[⟨4,2⟩,⟨(-4),(-8)⟩,⟨(-2),2⟩],[⟨4,8⟩,⟨4,(-4)⟩],[⟨(-8),8⟩]]

without_editor_info def bezC_60 : Poly := [[⟨11,10⟩,⟨(-10),(-2)⟩,⟨4,2⟩,⟨(-1),(-2)⟩]]

without_editor_info theorem bezout_60 (x y : ℤ) :
    value F x y * value bezA_60 x y + values x y 15 * value bezB_60 x y +
      values x y 17 * value bezC_60 x y = (18 : Eisenstein) :=
  bezout F (nodes 15) (nodes 17) bezA_60 bezB_60 bezC_60 18 (by decide +kernel) x y

without_editor_info def bezA_61 : Poly := [[⟨2,(-2)⟩]]

without_editor_info def bezB_61 : Poly := [[⟨(-14),(-13)⟩,⟨(-8),(-7)⟩,⟨(-1),(-2)⟩,⟨(-1),(-2)⟩],[⟨4,2⟩,⟨(-4),(-8)⟩,⟨(-2),2⟩],[⟨4,8⟩,⟨4,(-4)⟩],[⟨(-8),8⟩]]

without_editor_info def bezC_61 : Poly := [[⟨14,13⟩,⟨2,4⟩,⟨4,8⟩,⟨2,1⟩]]

without_editor_info theorem bezout_61 (x y : ℤ) :
    value F x y * value bezA_61 x y + values x y 15 * value bezB_61 x y +
      values x y 18 * value bezC_61 x y = (24 : Eisenstein) :=
  bezout F (nodes 15) (nodes 18) bezA_61 bezB_61 bezC_61 24 (by decide +kernel) x y

without_editor_info def bezA_62 : Poly := [[⟨2,2⟩]]

without_editor_info def bezB_62 : Poly := [[⟨0,0⟩,⟨0,(-3)⟩,⟨(-3),0⟩,⟨1,1⟩],[⟨0,2⟩,⟨4,0⟩,⟨(-2),(-2)⟩],[⟨(-4),0⟩,⟨4,4⟩],[⟨(-8),(-8)⟩]]

without_editor_info def bezC_62 : Poly := [[⟨(-2),2⟩,⟨3,(-4)⟩,⟨(-2),1⟩,⟨1,1⟩]]

without_editor_info theorem bezout_62 (x y : ℤ) :
    value F x y * value bezA_62 x y + values x y 15 * value bezB_62 x y +
      values x y 20 * value bezC_62 x y = (2 : Eisenstein) :=
  bezout F (nodes 15) (nodes 20) bezA_62 bezB_62 bezC_62 2 (by decide +kernel) x y

without_editor_info def bezA_63 : Poly := [[⟨(-4),(-2)⟩]]

without_editor_info def bezB_63 : Poly := [[⟨(-1),(-1)⟩,⟨0,(-3)⟩,⟨2,1⟩,⟨1,0⟩],[⟨(-2),(-4)⟩,⟨(-4),(-8)⟩,⟨(-2),(-4)⟩],[⟨(-4),4⟩,⟨(-4),4⟩],[⟨16,8⟩]]

without_editor_info def bezC_63 : Poly := [[⟨5,3⟩,⟨6,6⟩,⟨4,2⟩,⟨1,1⟩]]

without_editor_info theorem bezout_63 (x y : ℤ) :
    value F x y * value bezA_63 x y + values x y 17 * value bezB_63 x y +
      values x y 18 * value bezC_63 x y = (6 : Eisenstein) :=
  bezout F (nodes 17) (nodes 18) bezA_63 bezB_63 bezC_63 6 (by decide +kernel) x y

without_editor_info def bezA_64 : Poly := [[⟨(-6),(-6)⟩]]

without_editor_info def bezB_64 : Poly := [[⟨8,4⟩,⟨(-2),(-1)⟩,⟨4,8⟩,⟨1,2⟩],[⟨0,(-6)⟩,⟨0,(-12)⟩,⟨0,(-6)⟩],[⟨(-12),0⟩,⟨(-12),0⟩],[⟨24,24⟩]]

without_editor_info def bezC_64 : Poly := [[⟨(-2),2⟩,⟨11,10⟩,⟨5,1⟩,⟨2,1⟩]]

without_editor_info theorem bezout_64 (x y : ℤ) :
    value F x y * value bezA_64 x y + values x y 17 * value bezB_64 x y +
      values x y 21 * value bezC_64 x y = (6 : Eisenstein) :=
  bezout F (nodes 17) (nodes 21) bezA_64 bezB_64 bezC_64 6 (by decide +kernel) x y

without_editor_info def bezA_65 : Poly := [[⟨(-27),(-27)⟩]]

without_editor_info def bezB_65 : Poly := [[⟨(-48),21⟩,⟨(-36),(-9)⟩,⟨(-18),18⟩],[⟨0,(-27)⟩,⟨0,(-54)⟩,⟨0,(-27)⟩],[⟨(-54),0⟩,⟨(-54),0⟩],[⟨108,108⟩]]

without_editor_info def bezC_65 : Poly := [[⟨50,4⟩,⟨51,33⟩,⟨39,15⟩,⟨9,9⟩]]

without_editor_info theorem bezout_65 (x y : ℤ) :
    value F x y * value bezA_65 x y + values x y 17 * value bezB_65 x y +
      values x y 23 * value bezC_65 x y = (6 : Eisenstein) :=
  bezout F (nodes 17) (nodes 23) bezA_65 bezB_65 bezC_65 6 (by decide +kernel) x y

without_editor_info def bezA_66 : Poly := [[⟨(-2),(-1)⟩]]

without_editor_info def bezB_66 : Poly := [[⟨2,1⟩,⟨2,1⟩,⟨1,(-1)⟩],[⟨(-1),(-2)⟩,⟨4,2⟩,⟨(-1),1⟩],[⟨(-2),2⟩,⟨(-2),(-4)⟩],[⟨8,4⟩]]

without_editor_info def bezC_66 : Poly := [[⟨0,0⟩,⟨(-7),1⟩,⟨(-5),(-4)⟩,⟨2,1⟩]]

without_editor_info theorem bezout_66 (x y : ℤ) :
    value F x y * value bezA_66 x y + values x y 18 * value bezB_66 x y +
      values x y 24 * value bezC_66 x y = (3 : Eisenstein) :=
  bezout F (nodes 18) (nodes 24) bezA_66 bezB_66 bezC_66 3 (by decide +kernel) x y

without_editor_info def bezA_67 : Poly := [[⟨0,2⟩]]

without_editor_info def bezB_67 : Poly := [[⟨0,0⟩,⟨(-3),(-3)⟩,⟨3,0⟩,⟨0,1⟩],[⟨2,2⟩,⟨(-4),0⟩,⟨0,(-2)⟩],[⟨4,0⟩,⟨0,4⟩],[⟨0,(-8)⟩]]

without_editor_info def bezC_67 : Poly := [[⟨(-2),14⟩,⟨(-9),(-11)⟩,⟨5,2⟩,⟨0,1⟩]]

without_editor_info theorem bezout_67 (x y : ℤ) :
    value F x y * value bezA_67 x y + values x y 19 * value bezB_67 x y +
      values x y 20 * value bezC_67 x y = (16 : Eisenstein) :=
  bezout F (nodes 19) (nodes 20) bezA_67 bezB_67 bezC_67 16 (by decide +kernel) x y

without_editor_info def bezA_68 : Poly := [[⟨(-8),(-4)⟩]]

without_editor_info def bezB_68 : Poly := [[⟨2,4⟩,⟨5,1⟩,⟨7,8⟩,⟨(-2),(-1)⟩],[⟨(-4),4⟩,⟨(-8),(-16)⟩,⟨8,4⟩],[⟨8,16⟩,⟨(-16),(-8)⟩],[⟨32,16⟩]]

without_editor_info def bezC_68 : Poly := [[⟨(-2),(-4)⟩,⟨1,(-7)⟩,⟨(-1),4⟩,⟨(-2),(-1)⟩]]

without_editor_info theorem bezout_68 (x y : ℤ) :
    value F x y * value bezA_68 x y + values x y 19 * value bezB_68 x y +
      values x y 21 * value bezC_68 x y = (12 : Eisenstein) :=
  bezout F (nodes 19) (nodes 21) bezA_68 bezB_68 bezC_68 12 (by decide +kernel) x y

without_editor_info def bezA_69 : Poly := [[⟨0,1⟩]]

without_editor_info def bezB_69 : Poly := [[⟨(-1),0⟩,⟨1,0⟩,⟨0,1⟩]]

without_editor_info def bezC_69 : Poly := [[⟨0,(-1)⟩],[],[],[⟨0,(-8)⟩]]

without_editor_info theorem bezout_69 (x y : ℤ) :
    value F x y * value bezA_69 x y + values x y 20 * value bezB_69 x y +
      values x y 24 * value bezC_69 x y = (1 : Eisenstein) :=
  bezout F (nodes 20) (nodes 24) bezA_69 bezB_69 bezC_69 1 (by decide +kernel) x y

without_editor_info def supportNumber : Eisenstein := 6

without_editor_info theorem constant_support : ∀ i : Fin 25, constants i * (![⟨864,432⟩,⟨648,0⟩,⟨0,432⟩,⟨0,1296⟩,⟨1296,0⟩,⟨0,1296⟩,⟨0,1296⟩,⟨0,1296⟩,⟨648,648⟩,⟨324,324⟩,⟨1296,1296⟩,⟨108,108⟩,⟨432,216⟩,⟨(-432),432⟩,⟨(-432),0⟩,⟨0,1296⟩,⟨0,324⟩,⟨432,864⟩,⟨432,432⟩,⟨1296,1296⟩,⟨324,0⟩,⟨0,648⟩,⟨(-216),0⟩,⟨108,216⟩,⟨1296,0⟩]) i = supportNumber^4 := by decide +kernel

without_editor_info def starDen : Fin 25 → Eisenstein := ![1,1,1,3,1,1,1,1,1,1,2,1,1,1,2,1,1,1,2,1,1,1,3,3,1]

without_editor_info def bezDen : Fin 70 → Eisenstein := ![2,3,3,3,6,1,1,2,16,1,1,2,3,3,3,6,3,12,3,12,1,6,9,2,3,3,3,1,2,1,9,6,3,1,1,3,3,1,1,4,9,6,24,4,6,24,9,4,6,6,6,2,6,24,3,6,18,18,6,12,18,24,2,6,6,6,3,16,12,1]

without_editor_info theorem star_support : ∀ i : Fin 25, starDen i * (![1296,1296,1296,432,1296,1296,1296,1296,1296,1296,648,1296,1296,1296,648,1296,1296,1296,648,1296,1296,1296,432,432,1296]) i = supportNumber^4 := by decide +kernel

without_editor_info theorem bez_support : ∀ e : Fin 70, bezDen e * (![648,432,432,432,216,1296,1296,648,81,1296,1296,648,432,432,432,216,432,108,432,108,1296,216,144,648,432,432,432,1296,648,1296,144,216,432,1296,1296,432,432,1296,1296,324,144,216,54,324,216,54,144,324,216,216,216,648,216,54,432,216,72,72,216,108,72,54,648,216,216,216,432,81,108,1296]) e = supportNumber^4 := by decide +kernel

without_editor_info theorem outside {x y : ℤ} (hf : equation x y = 0) (π : Eisenstein) [Fact (Prime π)]
    (h3 : ¬ π ∣ 3) (hN : ¬ π ∣ supportNumber) : graphSum edges (values x y) constants (tame π h3) = 0 := by
  have hc : ∀ i, ¬ π ∣ constants i := fun i => not_dvd_of_support π supportNumber _ _ 4 hN (constant_support i)
  have hs : ∀ i, ¬ π ∣ starDen i := fun i => not_dvd_of_support π supportNumber _ _ 4 hN (star_support i)
  have hb : ∀ e, ¬ π ∣ bezDen e := fun e => not_dvd_of_support π supportNumber _ _ 4 hN (bez_support e)
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
    · exact separate_of_identity π (curve_zero hf) (hb 58) (bezout_58 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 59) (bezout_59 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 60) (bezout_60 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 61) (bezout_61 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 62) (bezout_62 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 63) (bezout_63 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 64) (bezout_64 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 65) (bezout_65 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 66) (bezout_66 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 67) (bezout_67 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 68) (bezout_68 x y)
    · exact separate_of_identity π (curve_zero hf) (hb 69) (bezout_69 x y)
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
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 20) (star_20 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 21) (star_21 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 22) (star_22 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 23) (star_23 x y)
    · exact residue_cube_of_identity π (curve_zero hf) hi (hs 24) (star_24 x y)

end GraphCert.Generated.g6681fe82262d85cf066bd0fe.Proof



set_option Elab.async false

open CubicSpecial

open GraphCert.Cubic

namespace GraphCert.Generated.g6681fe82262d85cf066bd0fe.Proof.At2

without_editor_info instance : Fact (Nat.Prime 2) := ⟨by decide⟩

without_editor_info instance : Fact (Prime (2 : Eisenstein)) := ⟨prime_integer_of_mod_three (by decide) (by decide)⟩

without_editor_info instance : Fact (Prime ((2 : ℕ) : Eisenstein)) := ⟨by simpa only [Nat.cast_ofNat] using (inferInstance : Fact (Prime (2 : Eisenstein))).out⟩

without_editor_info theorem away_three : ¬ (2 : Eisenstein) ∣ 3 := primary_prime_away_three (inferInstance : Fact (Prime (2 : Eisenstein))).out ⟨1, by decide⟩

without_editor_info def constantCertificates : Fin 25 → TameCertificate := (fun i => (#[⟨0,⟨1,(-1)⟩,⟨0,1⟩,⟨0,(-1)⟩,2,⟨1,2⟩⟩,⟨1,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨(-3),(-3)⟩,⟨0,1⟩,⟨(-1),0⟩,2,⟨1,1⟩⟩,⟨0,⟨(-1),(-1)⟩,⟨0,1⟩,⟨0,0⟩,2,⟨2,2⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨(-1),(-1)⟩,⟨0,1⟩,⟨0,0⟩,2,⟨2,2⟩⟩,⟨0,⟨(-1),(-1)⟩,⟨0,1⟩,⟨0,0⟩,2,⟨2,2⟩⟩,⟨0,⟨(-1),(-1)⟩,⟨0,1⟩,⟨0,0⟩,2,⟨2,2⟩⟩,⟨1,⟨0,(-1)⟩,⟨1,1⟩,⟨0,0⟩,1,⟨0,1⟩⟩,⟨2,⟨0,(-1)⟩,⟨1,1⟩,⟨0,0⟩,1,⟨0,1⟩⟩,⟨0,⟨0,(-1)⟩,⟨1,1⟩,⟨0,0⟩,1,⟨0,1⟩⟩,⟨2,⟨0,(-3)⟩,⟨1,1⟩,⟨(-1),0⟩,1,⟨0,0⟩⟩,⟨1,⟨1,(-1)⟩,⟨0,1⟩,⟨0,(-1)⟩,2,⟨1,2⟩⟩,⟨0,⟨(-2),(-1)⟩,⟨1,1⟩,⟨1,1⟩,1,⟨1,1⟩⟩,⟨0,⟨(-3),0⟩,⟨1,0⟩,⟨2,0⟩,0,⟨0,0⟩⟩,⟨0,⟨(-1),(-1)⟩,⟨0,1⟩,⟨0,0⟩,2,⟨2,2⟩⟩,⟨2,⟨(-1),(-1)⟩,⟨0,1⟩,⟨0,0⟩,2,⟨2,2⟩⟩,⟨0,⟨(-1),(-2)⟩,⟨1,0⟩,⟨1,1⟩,0,⟨1,1⟩⟩,⟨0,⟨0,(-3)⟩,⟨1,1⟩,⟨(-1),0⟩,1,⟨0,0⟩⟩,⟨0,⟨0,(-1)⟩,⟨1,1⟩,⟨0,0⟩,1,⟨0,1⟩⟩,⟨2,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨1,⟨(-1),(-1)⟩,⟨0,1⟩,⟨0,0⟩,2,⟨2,2⟩⟩,⟨1,⟨(-3),0⟩,⟨1,0⟩,⟨2,0⟩,0,⟨0,0⟩⟩,⟨2,⟨(-1),(-2)⟩,⟨1,0⟩,⟨1,1⟩,0,⟨1,1⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩] : Array (TameCertificate))[i.val]'(by simpa using i.isLt))

without_editor_info theorem constants_checked : ∀ i : Fin 25, (constantCertificates i).check 2 (constants i) := by decide +kernel

without_editor_info def envelopes0 : Fin 25 → WildEnvelope := (fun i => (#[⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![1,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info def certificates0 : Fin 25 → TameCertificate := (fun i => (#[⟨0,⟨2,1⟩,⟨1,1⟩,⟨0,(-1)⟩,1,⟨1,0⟩⟩,⟨0,⟨1,1⟩,⟨0,1⟩,⟨1,0⟩,2,⟨1,1⟩⟩,⟨0,⟨1,3⟩,⟨0,1⟩,⟨2,1⟩,2,⟨1,2⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨3,1⟩,⟨0,1⟩,⟨1,(-1)⟩,2,⟨2,1⟩⟩,⟨0,⟨2,1⟩,⟨1,1⟩,⟨0,(-1)⟩,1,⟨1,0⟩⟩,⟨0,⟨2,3⟩,⟨1,1⟩,⟨1,(-1)⟩,1,⟨1,1⟩⟩,⟨0,⟨1,3⟩,⟨0,1⟩,⟨2,1⟩,2,⟨1,2⟩⟩,⟨0,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨0,⟨3,3⟩,⟨0,1⟩,⟨2,0⟩,2,⟨2,2⟩⟩,⟨0,⟨3,0⟩,⟨1,0⟩,⟨(-1),0⟩,0,⟨1,0⟩⟩,⟨0,⟨2,1⟩,⟨1,1⟩,⟨0,(-1)⟩,1,⟨1,0⟩⟩,⟨0,⟨1,3⟩,⟨0,1⟩,⟨2,1⟩,2,⟨1,2⟩⟩,⟨0,⟨3,2⟩,⟨1,0⟩,⟨(-1),(-1)⟩,0,⟨1,1⟩⟩,⟨1,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨1,1⟩,⟨0,1⟩,⟨1,0⟩,2,⟨1,1⟩⟩,⟨0,⟨3,3⟩,⟨0,1⟩,⟨2,0⟩,2,⟨2,2⟩⟩,⟨1,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨1,2⟩,⟨1,0⟩,⟨0,(-1)⟩,0,⟨0,1⟩⟩,⟨0,⟨0,3⟩,⟨1,1⟩,⟨2,0⟩,1,⟨0,1⟩⟩,⟨0,⟨0,3⟩,⟨1,1⟩,⟨2,0⟩,1,⟨0,1⟩⟩,⟨0,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨1,⟨1,1⟩,⟨0,1⟩,⟨1,0⟩,2,⟨1,1⟩⟩,⟨1,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨0,⟨3,0⟩,⟨1,0⟩,⟨(-1),0⟩,0,⟨1,0⟩⟩] : Array (TameCertificate))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks0 : ∀ i : Fin 25, inertEnvelopeCheck (envelopes0 i) 2 (residueE (2^2) (values 3 3 i)) 2 (real i) (certificates0 i) := by decide +kernel

without_editor_info theorem noLoops : ∀ e : Fin 70, (edges e).src ≠ (edges e).dst := by
  exact listEdges_all (m := 70) edgeList (by decide)
    (fun e => e.src ≠ e.dst) (by decide +kernel)

without_editor_info theorem fixedDirections0 : ∀ i : Fin 25,
    i=3 ∨ (envelopes0 i).directions=0 := by decide +kernel

without_editor_info theorem linear0 : ∀ i : Fin 25, ∀ j : Fin 4,
    tameForm ((envelopes0 i).directions j)
      (graphStar edges (fun i => (envelopes0 i).base) (fun i => (constantCertificates i).vector) i) = 0 := by
  have h : ∀ k : Fin 4, tameForm ((envelopes0 3).directions k)
      (graphStar edges (fun i => (envelopes0 i).base) (fun i => (constantCertificates i).vector) 3)=0 := by
    simp only [graphStar_neighbors edges neighbors adjacency_checked]
    decide +kernel
  intro i k
  rcases fixedDirections0 i with rfl | hz
  · exact h k
  · rw [hz]; simp [tameForm]

without_editor_info theorem cross0 : ∀ e : Fin 70, ∀ j k : Fin 4,
    tameForm ((envelopes0 (edges e).src).directions j) ((envelopes0 (edges e).dst).directions k) = 0 := by
  intro e i k
  rcases fixedDirections0 (edges e).src with hs | hz
  · rcases fixedDirections0 (edges e).dst with ht | hz
    · exact False.elim (noLoops e (hs.trans ht.symm))
    · rw [hz]; simp [tameForm]
  · rw [hz]; simp [tameForm]

without_editor_info theorem value0 : vectorGraph edges (fun i => (envelopes0 i).base) (fun i => (constantCertificates i).vector) tameBilinear = 0 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell0 {x y : ℤ} (hf : equation x y = 0)
    (hx : (2 : ℤ)^2 ∣ x-3) (hy : (2 : ℤ)^2 ∣ y-3) : graphSum edges (values x y) constants (tame (2 : Eisenstein) away_three) = 0 :=
  inert_cell edges values constants real values_congr values_real 2 away_three (by decide) 3 3 2 envelopes0 constantCertificates certificates0 0 constants_checked checks0 linear0 cross0 value0 (all_nonzero hf) hx hy

without_editor_info def envelopes1 : Fin 25 → WildEnvelope := (fun i => (#[⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info def certificates1 : Fin 25 → TameCertificate := (fun i => (#[⟨0,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨0,⟨3,1⟩,⟨0,1⟩,⟨1,(-1)⟩,2,⟨2,1⟩⟩,⟨0,⟨3,3⟩,⟨0,1⟩,⟨2,0⟩,2,⟨2,2⟩⟩,⟨1,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨3,1⟩,⟨0,1⟩,⟨1,(-1)⟩,2,⟨2,1⟩⟩,⟨0,⟨2,1⟩,⟨1,1⟩,⟨0,(-1)⟩,1,⟨1,0⟩⟩,⟨0,⟨2,3⟩,⟨1,1⟩,⟨1,(-1)⟩,1,⟨1,1⟩⟩,⟨0,⟨1,3⟩,⟨0,1⟩,⟨2,1⟩,2,⟨1,2⟩⟩,⟨0,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨0,⟨3,3⟩,⟨0,1⟩,⟨2,0⟩,2,⟨2,2⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨2,3⟩,⟨1,1⟩,⟨1,(-1)⟩,1,⟨1,1⟩⟩,⟨0,⟨3,1⟩,⟨0,1⟩,⟨1,(-1)⟩,2,⟨2,1⟩⟩,⟨0,⟨3,0⟩,⟨1,0⟩,⟨(-1),0⟩,0,⟨1,0⟩⟩,⟨1,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨0,⟨3,1⟩,⟨0,1⟩,⟨1,(-1)⟩,2,⟨2,1⟩⟩,⟨0,⟨1,3⟩,⟨0,1⟩,⟨2,1⟩,2,⟨1,2⟩⟩,⟨1,⟨1,1⟩,⟨0,1⟩,⟨1,0⟩,2,⟨1,1⟩⟩,⟨0,⟨3,0⟩,⟨1,0⟩,⟨(-1),0⟩,0,⟨1,0⟩⟩,⟨0,⟨2,3⟩,⟨1,1⟩,⟨1,(-1)⟩,1,⟨1,1⟩⟩,⟨0,⟨2,3⟩,⟨1,1⟩,⟨1,(-1)⟩,1,⟨1,1⟩⟩,⟨0,⟨2,1⟩,⟨1,1⟩,⟨0,(-1)⟩,1,⟨1,0⟩⟩,⟨1,⟨1,1⟩,⟨0,1⟩,⟨1,0⟩,2,⟨1,1⟩⟩,⟨1,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨0,⟨3,0⟩,⟨1,0⟩,⟨(-1),0⟩,0,⟨1,0⟩⟩] : Array (TameCertificate))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks1 : ∀ i : Fin 25, inertEnvelopeCheck (envelopes1 i) 2 (residueE (2^2) (values 3 1 i)) 2 (real i) (certificates1 i) := by decide +kernel

without_editor_info theorem zeroDirections1 : ∀ i : Fin 25, ∀ j : Fin 4,
    (envelopes1 i).directions j=0 := by decide +kernel

without_editor_info theorem linear1 : ∀ i : Fin 25, ∀ j : Fin 4,
    tameForm ((envelopes1 i).directions j)
      (graphStar edges (fun i => (envelopes1 i).base) (fun i => (constantCertificates i).vector) i) = 0 := by
  intro i k
  rw [zeroDirections1 i k]
  simp [tameForm]

without_editor_info theorem cross1 : ∀ e : Fin 70, ∀ j k : Fin 4,
    tameForm ((envelopes1 (edges e).src).directions j) ((envelopes1 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections1 ((edges e).src) i]
  simp [tameForm]

without_editor_info theorem value1 : vectorGraph edges (fun i => (envelopes1 i).base) (fun i => (constantCertificates i).vector) tameBilinear = 0 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell1 {x y : ℤ} (hf : equation x y = 0)
    (hx : (2 : ℤ)^2 ∣ x-3) (hy : (2 : ℤ)^2 ∣ y-1) : graphSum edges (values x y) constants (tame (2 : Eisenstein) away_three) = 0 :=
  inert_cell edges values constants real values_congr values_real 2 away_three (by decide) 3 1 2 envelopes1 constantCertificates certificates1 0 constants_checked checks1 linear1 cross1 value1 (all_nonzero hf) hx hy

without_editor_info def envelopes2 : Fin 25 → WildEnvelope := (fun i => (#[⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![1,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info def certificates2 : Fin 25 → TameCertificate := (fun i => (#[⟨0,⟨3,1⟩,⟨0,1⟩,⟨1,(-1)⟩,2,⟨2,1⟩⟩,⟨0,⟨2,1⟩,⟨1,1⟩,⟨0,(-1)⟩,1,⟨1,0⟩⟩,⟨0,⟨2,3⟩,⟨1,1⟩,⟨1,(-1)⟩,1,⟨1,1⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨3,1⟩,⟨0,1⟩,⟨1,(-1)⟩,2,⟨2,1⟩⟩,⟨0,⟨2,1⟩,⟨1,1⟩,⟨0,(-1)⟩,1,⟨1,0⟩⟩,⟨0,⟨2,3⟩,⟨1,1⟩,⟨1,(-1)⟩,1,⟨1,1⟩⟩,⟨0,⟨1,3⟩,⟨0,1⟩,⟨2,1⟩,2,⟨1,2⟩⟩,⟨0,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨0,⟨3,3⟩,⟨0,1⟩,⟨2,0⟩,2,⟨2,2⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨1,⟨1,1⟩,⟨0,1⟩,⟨1,0⟩,2,⟨1,1⟩⟩,⟨1,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨0,⟨3,3⟩,⟨0,1⟩,⟨2,0⟩,2,⟨2,2⟩⟩,⟨0,⟨1,3⟩,⟨0,1⟩,⟨2,1⟩,2,⟨1,2⟩⟩,⟨0,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨0,⟨0,3⟩,⟨1,1⟩,⟨2,0⟩,1,⟨0,1⟩⟩,⟨0,⟨2,1⟩,⟨1,1⟩,⟨0,(-1)⟩,1,⟨1,0⟩⟩,⟨0,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨0,⟨3,3⟩,⟨0,1⟩,⟨2,0⟩,2,⟨2,2⟩⟩,⟨0,⟨1,3⟩,⟨0,1⟩,⟨2,1⟩,2,⟨1,2⟩⟩,⟨0,⟨1,1⟩,⟨0,1⟩,⟨1,0⟩,2,⟨1,1⟩⟩,⟨1,⟨1,1⟩,⟨0,1⟩,⟨1,0⟩,2,⟨1,1⟩⟩,⟨1,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨0,⟨3,0⟩,⟨1,0⟩,⟨(-1),0⟩,0,⟨1,0⟩⟩] : Array (TameCertificate))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks2 : ∀ i : Fin 25, inertEnvelopeCheck (envelopes2 i) 2 (residueE (2^2) (values 3 2 i)) 2 (real i) (certificates2 i) := by decide +kernel

without_editor_info theorem fixedDirections2 : ∀ i : Fin 25,
    i=10 ∨ (envelopes2 i).directions=0 := by decide +kernel

without_editor_info theorem linear2 : ∀ i : Fin 25, ∀ j : Fin 4,
    tameForm ((envelopes2 i).directions j)
      (graphStar edges (fun i => (envelopes2 i).base) (fun i => (constantCertificates i).vector) i) = 0 := by
  have h : ∀ k : Fin 4, tameForm ((envelopes2 10).directions k)
      (graphStar edges (fun i => (envelopes2 i).base) (fun i => (constantCertificates i).vector) 10)=0 := by
    simp only [graphStar_neighbors edges neighbors adjacency_checked]
    decide +kernel
  intro i k
  rcases fixedDirections2 i with rfl | hz
  · exact h k
  · rw [hz]; simp [tameForm]

without_editor_info theorem cross2 : ∀ e : Fin 70, ∀ j k : Fin 4,
    tameForm ((envelopes2 (edges e).src).directions j) ((envelopes2 (edges e).dst).directions k) = 0 := by
  intro e i k
  rcases fixedDirections2 (edges e).src with hs | hz
  · rcases fixedDirections2 (edges e).dst with ht | hz
    · exact False.elim (noLoops e (hs.trans ht.symm))
    · rw [hz]; simp [tameForm]
  · rw [hz]; simp [tameForm]

without_editor_info theorem value2 : vectorGraph edges (fun i => (envelopes2 i).base) (fun i => (constantCertificates i).vector) tameBilinear = 0 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell2 {x y : ℤ} (hf : equation x y = 0)
    (hx : (2 : ℤ)^2 ∣ x-3) (hy : (2 : ℤ)^2 ∣ y-2) : graphSum edges (values x y) constants (tame (2 : Eisenstein) away_three) = 0 :=
  inert_cell edges values constants real values_congr values_real 2 away_three (by decide) 3 2 2 envelopes2 constantCertificates certificates2 0 constants_checked checks2 linear2 cross2 value2 (all_nonzero hf) hx hy

without_editor_info def envelopes3 : Fin 25 → WildEnvelope := (fun i => (#[⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info def certificates3 : Fin 25 → TameCertificate := (fun i => (#[⟨0,⟨1,1⟩,⟨0,1⟩,⟨1,0⟩,2,⟨1,1⟩⟩,⟨0,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨0,⟨0,3⟩,⟨1,1⟩,⟨2,0⟩,1,⟨0,1⟩⟩,⟨0,⟨3,0⟩,⟨1,0⟩,⟨(-1),0⟩,0,⟨1,0⟩⟩,⟨0,⟨3,1⟩,⟨0,1⟩,⟨1,(-1)⟩,2,⟨2,1⟩⟩,⟨0,⟨2,1⟩,⟨1,1⟩,⟨0,(-1)⟩,1,⟨1,0⟩⟩,⟨0,⟨2,3⟩,⟨1,1⟩,⟨1,(-1)⟩,1,⟨1,1⟩⟩,⟨0,⟨1,3⟩,⟨0,1⟩,⟨2,1⟩,2,⟨1,2⟩⟩,⟨0,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨0,⟨3,3⟩,⟨0,1⟩,⟨2,0⟩,2,⟨2,2⟩⟩,⟨1,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨1,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨1,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩,⟨0,⟨3,1⟩,⟨0,1⟩,⟨1,(-1)⟩,2,⟨2,1⟩⟩,⟨0,⟨3,1⟩,⟨0,1⟩,⟨1,(-1)⟩,2,⟨2,1⟩⟩,⟨0,⟨2,1⟩,⟨1,1⟩,⟨0,(-1)⟩,1,⟨1,0⟩⟩,⟨0,⟨2,3⟩,⟨1,1⟩,⟨1,(-1)⟩,1,⟨1,1⟩⟩,⟨0,⟨2,3⟩,⟨1,1⟩,⟨1,(-1)⟩,1,⟨1,1⟩⟩,⟨0,⟨2,3⟩,⟨1,1⟩,⟨1,(-1)⟩,1,⟨1,1⟩⟩,⟨0,⟨1,3⟩,⟨0,1⟩,⟨2,1⟩,2,⟨1,2⟩⟩,⟨0,⟨3,3⟩,⟨0,1⟩,⟨2,0⟩,2,⟨2,2⟩⟩,⟨0,⟨3,1⟩,⟨0,1⟩,⟨1,(-1)⟩,2,⟨2,1⟩⟩,⟨1,⟨0,1⟩,⟨1,1⟩,⟨1,0⟩,1,⟨0,0⟩⟩,⟨1,⟨1,1⟩,⟨0,1⟩,⟨1,0⟩,2,⟨1,1⟩⟩,⟨0,⟨1,0⟩,⟨1,0⟩,⟨0,0⟩,0,⟨0,0⟩⟩] : Array (TameCertificate))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks3 : ∀ i : Fin 25, inertEnvelopeCheck (envelopes3 i) 2 (residueE (2^2) (values 1 0 i)) 2 (real i) (certificates3 i) := by decide +kernel

without_editor_info theorem zeroDirections3 : ∀ i : Fin 25, ∀ j : Fin 4,
    (envelopes3 i).directions j=0 := by decide +kernel

without_editor_info theorem linear3 : ∀ i : Fin 25, ∀ j : Fin 4,
    tameForm ((envelopes3 i).directions j)
      (graphStar edges (fun i => (envelopes3 i).base) (fun i => (constantCertificates i).vector) i) = 0 := by
  intro i k
  rw [zeroDirections3 i k]
  simp [tameForm]

without_editor_info theorem cross3 : ∀ e : Fin 70, ∀ j k : Fin 4,
    tameForm ((envelopes3 (edges e).src).directions j) ((envelopes3 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections3 ((edges e).src) i]
  simp [tameForm]

without_editor_info theorem value3 : vectorGraph edges (fun i => (envelopes3 i).base) (fun i => (constantCertificates i).vector) tameBilinear = 0 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell3 {x y : ℤ} (hf : equation x y = 0)
    (hx : (2 : ℤ)^2 ∣ x-1) (hy : (2 : ℤ)^2 ∣ y-0) : graphSum edges (values x y) constants (tame (2 : Eisenstein) away_three) = 0 :=
  inert_cell edges values constants real values_congr values_real 2 away_three (by decide) 1 0 2 envelopes3 constantCertificates certificates3 0 constants_checked checks3 linear3 cross3 value3 (all_nonzero hf) hx hy

without_editor_info noncomputable def localSum (x y : ℤ) : ZMod 3 := graphSum edges (values x y) constants (tame (2 : Eisenstein) away_three)

without_editor_info def residues : Fin 4 → ℤ × ℤ × ℕ := (fun i => (#[(3,3,2),(3,1,2),(3,2,2),(1,0,2)] : Array (ℤ × ℤ × ℕ))[i.val]'(by simpa using i.isLt))

without_editor_info def targets : Fin 4 → ZMod 3 := (fun i => (#[0,0,0,0] : Array (ZMod 3))[i.val]'(by simpa using i.isLt))

without_editor_info theorem cell_value (i : Fin 4) {x y : ℤ} (hf : equation x y = 0)
    (hx : (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1)
    (hy : (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1) : localSum x y = targets i := by
  fin_cases i
  · exact cell0 hf hx hy
  · exact cell1 hf hx hy
  · exact cell2 hf hx hy
  · exact cell3 hf hx hy

without_editor_info theorem covered0 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (2 : ℤ)^2 ∣ x-3) (hy : (2 : ℤ)^2 ∣ y-3) : ∃ i : Fin 4, (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨0,hx,hy⟩

without_editor_info theorem covered1 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (2 : ℤ)^2 ∣ x-3) (hy : (2 : ℤ)^2 ∣ y-1) : ∃ i : Fin 4, (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨1,hx,hy⟩

without_editor_info theorem covered2 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (2 : ℤ)^2 ∣ x-3) (hy : (2 : ℤ)^2 ∣ y-2) : ∃ i : Fin 4, (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨2,hx,hy⟩

without_editor_info theorem covered3 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (2 : ℤ)^2 ∣ x-1) (hy : (2 : ℤ)^2 ∣ y-0) : ∃ i : Fin 4, (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨3,hx,hy⟩

without_editor_info theorem branch0 {x y : ℤ} (hf : equation x y = 0)
    (hx : (2 : ℤ)^1 ∣ x-1) (hy : (2 : ℤ)^1 ∣ y-0) : ∃ i : Fin 4, (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 4, (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    2 (by decide) 2 1 0 [(1,0),(3,2)] (by decide +kernel) ?_ hf hx hy
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
    (hx : (2 : ℤ)^1 ∣ x-1) (hy : (2 : ℤ)^1 ∣ y-1) : ∃ i : Fin 4, (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 4, (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    2 (by decide) 2 1 1 [(3,1),(3,3)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · intro X Y hF hX hY
    apply covered1 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered0 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch2 {x y : ℤ} (hf : equation x y = 0)
    (hx : (2 : ℤ)^0 ∣ x-0) (hy : (2 : ℤ)^0 ∣ y-0) : ∃ i : Fin 4, (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 4, (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    2 (by decide) 1 0 0 [(1,0),(1,1)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · intro X Y hF hX hY
    apply branch0 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply branch1 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem local_cover {x y : ℤ} (hf : equation x y = 0) : ∃ i : Fin 4, (2 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (2 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := branch2 hf (by simp) (by simp)

end GraphCert.Generated.g6681fe82262d85cf066bd0fe.Proof.At2



set_option Elab.async false

open CubicSpecial

open GraphCert.Cubic

namespace GraphCert.Generated.g6681fe82262d85cf066bd0fe.Proof.At3

without_editor_info def constantsClass : Fin 25 → WildVector := (fun i => (#[![1,0,0,0],![0,0,1,0],![2,1,0,0],![0,2,0,0],![0,0,0,0],![0,2,0,0],![0,2,0,0],![0,2,0,0],![0,1,1,0],![0,1,2,0],![0,1,0,0],![2,0,2,0],![1,0,1,0],![1,2,0,0],![2,2,0,0],![0,2,0,0],![0,2,2,0],![1,1,0,0],![2,0,0,0],![0,1,0,0],![0,0,2,0],![0,2,1,0],![2,2,1,0],![1,1,2,0],![0,0,0,0]] : Array (WildVector))[i.val]'(by simpa using i.isLt))

without_editor_info theorem constants_checked : ∀ i : Fin 25, computeWildClass 32 (constants i) = some (constantsClass i) := by decide +kernel

without_editor_info def envelopes0 : Fin 25 → WildEnvelope := (fun i => (#[⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks0 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes0 i) (residueE (3^3) (values 26 21 i)) 3 (real i) := by decide +kernel

without_editor_info theorem zeroDirections0 : ∀ i : Fin 25, ∀ j : Fin 4,
    (envelopes0 i).directions j=0 := by decide +kernel

without_editor_info theorem linear0 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes0 i).directions j)
      (graphStar edges (fun i => (envelopes0 i).base) constantsClass i) = 0 := by
  intro i k
  rw [zeroDirections0 i k]
  simp [wildForm]

without_editor_info theorem cross0 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes0 (edges e).src).directions j) ((envelopes0 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections0 ((edges e).src) i]
  simp [wildForm]

without_editor_info theorem value0 : vectorGraph edges (fun i => (envelopes0 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell0 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-26) (hy : (3 : ℤ)^3 ∣ y-21) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 26 21 3 envelopes0 constantsClass 1 constants_checked checks0 linear0 cross0 value0 (all_nonzero hf) hx hy

without_editor_info def envelopes1 : Fin 25 → WildEnvelope := (fun i => (#[⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks1 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes1 i) (residueE (3^3) (values 17 12 i)) 3 (real i) := by decide +kernel

without_editor_info theorem zeroDirections1 : ∀ i : Fin 25, ∀ j : Fin 4,
    (envelopes1 i).directions j=0 := by decide +kernel

without_editor_info theorem linear1 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes1 i).directions j)
      (graphStar edges (fun i => (envelopes1 i).base) constantsClass i) = 0 := by
  intro i k
  rw [zeroDirections1 i k]
  simp [wildForm]

without_editor_info theorem cross1 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes1 (edges e).src).directions j) ((envelopes1 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections1 ((edges e).src) i]
  simp [wildForm]

without_editor_info theorem value1 : vectorGraph edges (fun i => (envelopes1 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell1 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-17) (hy : (3 : ℤ)^3 ∣ y-12) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 17 12 3 envelopes1 constantsClass 1 constants_checked checks1 linear1 cross1 value1 (all_nonzero hf) hx hy

without_editor_info def envelopes2 : Fin 25 → WildEnvelope := (fun i => (#[⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks2 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes2 i) (residueE (3^3) (values 8 3 i)) 3 (real i) := by decide +kernel

without_editor_info theorem zeroDirections2 : ∀ i : Fin 25, ∀ j : Fin 4,
    (envelopes2 i).directions j=0 := by decide +kernel

without_editor_info theorem linear2 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes2 i).directions j)
      (graphStar edges (fun i => (envelopes2 i).base) constantsClass i) = 0 := by
  intro i k
  rw [zeroDirections2 i k]
  simp [wildForm]

without_editor_info theorem cross2 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes2 (edges e).src).directions j) ((envelopes2 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections2 ((edges e).src) i]
  simp [wildForm]

without_editor_info theorem value2 : vectorGraph edges (fun i => (envelopes2 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell2 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-8) (hy : (3 : ℤ)^3 ∣ y-3) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 8 3 3 envelopes2 constantsClass 1 constants_checked checks2 linear2 cross2 value2 (all_nonzero hf) hx hy

without_editor_info def envelopes3 : Fin 25 → WildEnvelope := (fun i => (#[⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks3 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes3 i) (residueE (3^3) (values 23 9 i)) 3 (real i) := by decide +kernel

without_editor_info theorem zeroDirections3 : ∀ i : Fin 25, ∀ j : Fin 4,
    (envelopes3 i).directions j=0 := by decide +kernel

without_editor_info theorem linear3 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes3 i).directions j)
      (graphStar edges (fun i => (envelopes3 i).base) constantsClass i) = 0 := by
  intro i k
  rw [zeroDirections3 i k]
  simp [wildForm]

without_editor_info theorem cross3 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes3 (edges e).src).directions j) ((envelopes3 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections3 ((edges e).src) i]
  simp [wildForm]

without_editor_info theorem value3 : vectorGraph edges (fun i => (envelopes3 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell3 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-23) (hy : (3 : ℤ)^3 ∣ y-9) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 23 9 3 envelopes3 constantsClass 1 constants_checked checks3 linear3 cross3 value3 (all_nonzero hf) hx hy

without_editor_info def envelopes4 : Fin 25 → WildEnvelope := (fun i => (#[⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks4 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes4 i) (residueE (3^3) (values 14 0 i)) 3 (real i) := by decide +kernel

without_editor_info theorem zeroDirections4 : ∀ i : Fin 25, ∀ j : Fin 4,
    (envelopes4 i).directions j=0 := by decide +kernel

without_editor_info theorem linear4 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes4 i).directions j)
      (graphStar edges (fun i => (envelopes4 i).base) constantsClass i) = 0 := by
  intro i k
  rw [zeroDirections4 i k]
  simp [wildForm]

without_editor_info theorem cross4 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes4 (edges e).src).directions j) ((envelopes4 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections4 ((edges e).src) i]
  simp [wildForm]

without_editor_info theorem value4 : vectorGraph edges (fun i => (envelopes4 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell4 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-14) (hy : (3 : ℤ)^3 ∣ y-0) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 14 0 3 envelopes4 constantsClass 1 constants_checked checks4 linear4 cross4 value4 (all_nonzero hf) hx hy

without_editor_info def envelopes5 : Fin 25 → WildEnvelope := (fun i => (#[⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks5 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes5 i) (residueE (3^3) (values 5 18 i)) 3 (real i) := by decide +kernel

without_editor_info theorem zeroDirections5 : ∀ i : Fin 25, ∀ j : Fin 4,
    (envelopes5 i).directions j=0 := by decide +kernel

without_editor_info theorem linear5 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes5 i).directions j)
      (graphStar edges (fun i => (envelopes5 i).base) constantsClass i) = 0 := by
  intro i k
  rw [zeroDirections5 i k]
  simp [wildForm]

without_editor_info theorem cross5 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes5 (edges e).src).directions j) ((envelopes5 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections5 ((edges e).src) i]
  simp [wildForm]

without_editor_info theorem value5 : vectorGraph edges (fun i => (envelopes5 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell5 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-5) (hy : (3 : ℤ)^3 ∣ y-18) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 5 18 3 envelopes5 constantsClass 1 constants_checked checks5 linear5 cross5 value5 (all_nonzero hf) hx hy

without_editor_info def envelopes6 : Fin 25 → WildEnvelope := (fun i => (#[⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks6 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes6 i) (residueE (3^3) (values 20 24 i)) 3 (real i) := by decide +kernel

without_editor_info theorem zeroDirections6 : ∀ i : Fin 25, ∀ j : Fin 4,
    (envelopes6 i).directions j=0 := by decide +kernel

without_editor_info theorem linear6 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes6 i).directions j)
      (graphStar edges (fun i => (envelopes6 i).base) constantsClass i) = 0 := by
  intro i k
  rw [zeroDirections6 i k]
  simp [wildForm]

without_editor_info theorem cross6 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes6 (edges e).src).directions j) ((envelopes6 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections6 ((edges e).src) i]
  simp [wildForm]

without_editor_info theorem value6 : vectorGraph edges (fun i => (envelopes6 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell6 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-20) (hy : (3 : ℤ)^3 ∣ y-24) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 20 24 3 envelopes6 constantsClass 1 constants_checked checks6 linear6 cross6 value6 (all_nonzero hf) hx hy

without_editor_info def envelopes7 : Fin 25 → WildEnvelope := (fun i => (#[⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks7 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes7 i) (residueE (3^3) (values 11 15 i)) 3 (real i) := by decide +kernel

without_editor_info theorem zeroDirections7 : ∀ i : Fin 25, ∀ j : Fin 4,
    (envelopes7 i).directions j=0 := by decide +kernel

without_editor_info theorem linear7 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes7 i).directions j)
      (graphStar edges (fun i => (envelopes7 i).base) constantsClass i) = 0 := by
  intro i k
  rw [zeroDirections7 i k]
  simp [wildForm]

without_editor_info theorem cross7 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes7 (edges e).src).directions j) ((envelopes7 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections7 ((edges e).src) i]
  simp [wildForm]

without_editor_info theorem value7 : vectorGraph edges (fun i => (envelopes7 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell7 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-11) (hy : (3 : ℤ)^3 ∣ y-15) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 11 15 3 envelopes7 constantsClass 1 constants_checked checks7 linear7 cross7 value7 (all_nonzero hf) hx hy

without_editor_info def envelopes8 : Fin 25 → WildEnvelope := (fun i => (#[⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks8 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes8 i) (residueE (3^3) (values 2 6 i)) 3 (real i) := by decide +kernel

without_editor_info theorem zeroDirections8 : ∀ i : Fin 25, ∀ j : Fin 4,
    (envelopes8 i).directions j=0 := by decide +kernel

without_editor_info theorem linear8 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes8 i).directions j)
      (graphStar edges (fun i => (envelopes8 i).base) constantsClass i) = 0 := by
  intro i k
  rw [zeroDirections8 i k]
  simp [wildForm]

without_editor_info theorem cross8 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes8 (edges e).src).directions j) ((envelopes8 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections8 ((edges e).src) i]
  simp [wildForm]

without_editor_info theorem value8 : vectorGraph edges (fun i => (envelopes8 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell8 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-2) (hy : (3 : ℤ)^3 ∣ y-6) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 2 6 3 envelopes8 constantsClass 1 constants_checked checks8 linear8 cross8 value8 (all_nonzero hf) hx hy

without_editor_info def envelopes9 : Fin 25 → WildEnvelope := (fun i => (#[⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks9 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes9 i) (residueE (3^3) (values 25 2 i)) 3 (real i) := by decide +kernel

without_editor_info theorem zeroDirections9 : ∀ i : Fin 25, ∀ j : Fin 4,
    (envelopes9 i).directions j=0 := by decide +kernel

without_editor_info theorem linear9 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes9 i).directions j)
      (graphStar edges (fun i => (envelopes9 i).base) constantsClass i) = 0 := by
  intro i k
  rw [zeroDirections9 i k]
  simp [wildForm]

without_editor_info theorem cross9 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes9 (edges e).src).directions j) ((envelopes9 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections9 ((edges e).src) i]
  simp [wildForm]

without_editor_info theorem value9 : vectorGraph edges (fun i => (envelopes9 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell9 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-25) (hy : (3 : ℤ)^3 ∣ y-2) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 25 2 3 envelopes9 constantsClass 1 constants_checked checks9 linear9 cross9 value9 (all_nonzero hf) hx hy

without_editor_info def envelopes10 : Fin 25 → WildEnvelope := (fun i => (#[⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks10 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes10 i) (residueE (3^3) (values 16 2 i)) 3 (real i) := by decide +kernel

without_editor_info theorem zeroDirections10 : ∀ i : Fin 25, ∀ j : Fin 4,
    (envelopes10 i).directions j=0 := by decide +kernel

without_editor_info theorem linear10 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes10 i).directions j)
      (graphStar edges (fun i => (envelopes10 i).base) constantsClass i) = 0 := by
  intro i k
  rw [zeroDirections10 i k]
  simp [wildForm]

without_editor_info theorem cross10 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes10 (edges e).src).directions j) ((envelopes10 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections10 ((edges e).src) i]
  simp [wildForm]

without_editor_info theorem value10 : vectorGraph edges (fun i => (envelopes10 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell10 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-16) (hy : (3 : ℤ)^3 ∣ y-2) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 16 2 3 envelopes10 constantsClass 1 constants_checked checks10 linear10 cross10 value10 (all_nonzero hf) hx hy

without_editor_info def envelopes11 : Fin 25 → WildEnvelope := (fun i => (#[⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks11 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes11 i) (residueE (3^3) (values 7 2 i)) 3 (real i) := by decide +kernel

without_editor_info theorem zeroDirections11 : ∀ i : Fin 25, ∀ j : Fin 4,
    (envelopes11 i).directions j=0 := by decide +kernel

without_editor_info theorem linear11 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes11 i).directions j)
      (graphStar edges (fun i => (envelopes11 i).base) constantsClass i) = 0 := by
  intro i k
  rw [zeroDirections11 i k]
  simp [wildForm]

without_editor_info theorem cross11 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes11 (edges e).src).directions j) ((envelopes11 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections11 ((edges e).src) i]
  simp [wildForm]

without_editor_info theorem value11 : vectorGraph edges (fun i => (envelopes11 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell11 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-7) (hy : (3 : ℤ)^3 ∣ y-2) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 7 2 3 envelopes11 constantsClass 1 constants_checked checks11 linear11 cross11 value11 (all_nonzero hf) hx hy

without_editor_info def envelopes12 : Fin 25 → WildEnvelope := (fun i => (#[⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks12 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes12 i) (residueE (3^3) (values 22 20 i)) 3 (real i) := by decide +kernel

without_editor_info theorem zeroDirections12 : ∀ i : Fin 25, ∀ j : Fin 4,
    (envelopes12 i).directions j=0 := by decide +kernel

without_editor_info theorem linear12 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes12 i).directions j)
      (graphStar edges (fun i => (envelopes12 i).base) constantsClass i) = 0 := by
  intro i k
  rw [zeroDirections12 i k]
  simp [wildForm]

without_editor_info theorem cross12 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes12 (edges e).src).directions j) ((envelopes12 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections12 ((edges e).src) i]
  simp [wildForm]

without_editor_info theorem value12 : vectorGraph edges (fun i => (envelopes12 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell12 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-22) (hy : (3 : ℤ)^3 ∣ y-20) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 22 20 3 envelopes12 constantsClass 1 constants_checked checks12 linear12 cross12 value12 (all_nonzero hf) hx hy

without_editor_info def envelopes13 : Fin 25 → WildEnvelope := (fun i => (#[⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks13 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes13 i) (residueE (3^3) (values 13 20 i)) 3 (real i) := by decide +kernel

without_editor_info theorem zeroDirections13 : ∀ i : Fin 25, ∀ j : Fin 4,
    (envelopes13 i).directions j=0 := by decide +kernel

without_editor_info theorem linear13 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes13 i).directions j)
      (graphStar edges (fun i => (envelopes13 i).base) constantsClass i) = 0 := by
  intro i k
  rw [zeroDirections13 i k]
  simp [wildForm]

without_editor_info theorem cross13 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes13 (edges e).src).directions j) ((envelopes13 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections13 ((edges e).src) i]
  simp [wildForm]

without_editor_info theorem value13 : vectorGraph edges (fun i => (envelopes13 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell13 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-13) (hy : (3 : ℤ)^3 ∣ y-20) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 13 20 3 envelopes13 constantsClass 1 constants_checked checks13 linear13 cross13 value13 (all_nonzero hf) hx hy

without_editor_info def envelopes14 : Fin 25 → WildEnvelope := (fun i => (#[⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks14 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes14 i) (residueE (3^3) (values 4 20 i)) 3 (real i) := by decide +kernel

without_editor_info theorem zeroDirections14 : ∀ i : Fin 25, ∀ j : Fin 4,
    (envelopes14 i).directions j=0 := by decide +kernel

without_editor_info theorem linear14 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes14 i).directions j)
      (graphStar edges (fun i => (envelopes14 i).base) constantsClass i) = 0 := by
  intro i k
  rw [zeroDirections14 i k]
  simp [wildForm]

without_editor_info theorem cross14 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes14 (edges e).src).directions j) ((envelopes14 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections14 ((edges e).src) i]
  simp [wildForm]

without_editor_info theorem value14 : vectorGraph edges (fun i => (envelopes14 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell14 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-4) (hy : (3 : ℤ)^3 ∣ y-20) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 4 20 3 envelopes14 constantsClass 1 constants_checked checks14 linear14 cross14 value14 (all_nonzero hf) hx hy

without_editor_info def envelopes15 : Fin 25 → WildEnvelope := (fun i => (#[⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,1,0],![1,1,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks15 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes15 i) (residueE (3^3) (values 19 11 i)) 3 (real i) := by decide +kernel

without_editor_info theorem noLoops : ∀ e : Fin 70, (edges e).src ≠ (edges e).dst := by
  exact listEdges_all (m := 70) edgeList (by decide)
    (fun e => e.src ≠ e.dst) (by decide +kernel)

without_editor_info theorem fixedDirections15 : ∀ i : Fin 25,
    i=10 ∨ (envelopes15 i).directions=0 := by decide +kernel

without_editor_info theorem linear15 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes15 i).directions j)
      (graphStar edges (fun i => (envelopes15 i).base) constantsClass i) = 0 := by
  have h : ∀ k : Fin 4, wildForm ((envelopes15 10).directions k)
      (graphStar edges (fun i => (envelopes15 i).base) constantsClass 10)=0 := by
    simp only [graphStar_neighbors edges neighbors adjacency_checked]
    decide +kernel
  intro i k
  rcases fixedDirections15 i with rfl | hz
  · exact h k
  · rw [hz]; simp [wildForm]

without_editor_info theorem cross15 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes15 (edges e).src).directions j) ((envelopes15 (edges e).dst).directions k) = 0 := by
  intro e i k
  rcases fixedDirections15 (edges e).src with hs | hz
  · rcases fixedDirections15 (edges e).dst with ht | hz
    · exact False.elim (noLoops e (hs.trans ht.symm))
    · rw [hz]; simp [wildForm]
  · rw [hz]; simp [wildForm]

without_editor_info theorem value15 : vectorGraph edges (fun i => (envelopes15 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell15 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-19) (hy : (3 : ℤ)^3 ∣ y-11) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 19 11 3 envelopes15 constantsClass 1 constants_checked checks15 linear15 cross15 value15 (all_nonzero hf) hx hy

without_editor_info def envelopes16 : Fin 25 → WildEnvelope := (fun i => (#[⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,1,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks16 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes16 i) (residueE (3^3) (values 10 11 i)) 3 (real i) := by decide +kernel

without_editor_info theorem fixedDirections16 : ∀ i : Fin 25,
    i=10 ∨ (envelopes16 i).directions=0 := by decide +kernel

without_editor_info theorem linear16 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes16 i).directions j)
      (graphStar edges (fun i => (envelopes16 i).base) constantsClass i) = 0 := by
  have h : ∀ k : Fin 4, wildForm ((envelopes16 10).directions k)
      (graphStar edges (fun i => (envelopes16 i).base) constantsClass 10)=0 := by
    simp only [graphStar_neighbors edges neighbors adjacency_checked]
    decide +kernel
  intro i k
  rcases fixedDirections16 i with rfl | hz
  · exact h k
  · rw [hz]; simp [wildForm]

without_editor_info theorem cross16 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes16 (edges e).src).directions j) ((envelopes16 (edges e).dst).directions k) = 0 := by
  intro e i k
  rcases fixedDirections16 (edges e).src with hs | hz
  · rcases fixedDirections16 (edges e).dst with ht | hz
    · exact False.elim (noLoops e (hs.trans ht.symm))
    · rw [hz]; simp [wildForm]
  · rw [hz]; simp [wildForm]

without_editor_info theorem value16 : vectorGraph edges (fun i => (envelopes16 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell16 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-10) (hy : (3 : ℤ)^3 ∣ y-11) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 10 11 3 envelopes16 constantsClass 1 constants_checked checks16 linear16 cross16 value16 (all_nonzero hf) hx hy

without_editor_info def envelopes17 : Fin 25 → WildEnvelope := (fun i => (#[⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,1,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks17 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes17 i) (residueE (3^3) (values 1 11 i)) 3 (real i) := by decide +kernel

without_editor_info theorem fixedDirections17 : ∀ i : Fin 25,
    i=10 ∨ (envelopes17 i).directions=0 := by decide +kernel

without_editor_info theorem linear17 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes17 i).directions j)
      (graphStar edges (fun i => (envelopes17 i).base) constantsClass i) = 0 := by
  have h : ∀ k : Fin 4, wildForm ((envelopes17 10).directions k)
      (graphStar edges (fun i => (envelopes17 i).base) constantsClass 10)=0 := by
    simp only [graphStar_neighbors edges neighbors adjacency_checked]
    decide +kernel
  intro i k
  rcases fixedDirections17 i with rfl | hz
  · exact h k
  · rw [hz]; simp [wildForm]

without_editor_info theorem cross17 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes17 (edges e).src).directions j) ((envelopes17 (edges e).dst).directions k) = 0 := by
  intro e i k
  rcases fixedDirections17 (edges e).src with hs | hz
  · rcases fixedDirections17 (edges e).dst with ht | hz
    · exact False.elim (noLoops e (hs.trans ht.symm))
    · rw [hz]; simp [wildForm]
  · rw [hz]; simp [wildForm]

without_editor_info theorem value17 : vectorGraph edges (fun i => (envelopes17 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell17 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-1) (hy : (3 : ℤ)^3 ∣ y-11) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 1 11 3 envelopes17 constantsClass 1 constants_checked checks17 linear17 cross17 value17 (all_nonzero hf) hx hy

without_editor_info def envelopes18 : Fin 25 → WildEnvelope := (fun i => (#[⟨![1,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,1,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks18 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes18 i) (residueE (3^3) (values 24 14 i)) 3 (real i) := by decide +kernel

without_editor_info theorem zeroDirections18 : ∀ i : Fin 25, ∀ j : Fin 4,
    (envelopes18 i).directions j=0 := by decide +kernel

without_editor_info theorem linear18 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes18 i).directions j)
      (graphStar edges (fun i => (envelopes18 i).base) constantsClass i) = 0 := by
  intro i k
  rw [zeroDirections18 i k]
  simp [wildForm]

without_editor_info theorem cross18 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes18 (edges e).src).directions j) ((envelopes18 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections18 ((edges e).src) i]
  simp [wildForm]

without_editor_info theorem value18 : vectorGraph edges (fun i => (envelopes18 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell18 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-24) (hy : (3 : ℤ)^3 ∣ y-14) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 24 14 3 envelopes18 constantsClass 1 constants_checked checks18 linear18 cross18 value18 (all_nonzero hf) hx hy

without_editor_info def envelopes19 : Fin 25 → WildEnvelope := (fun i => (#[⟨![1,1,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks19 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes19 i) (residueE (3^3) (values 15 23 i)) 3 (real i) := by decide +kernel

without_editor_info theorem zeroDirections19 : ∀ i : Fin 25, ∀ j : Fin 4,
    (envelopes19 i).directions j=0 := by decide +kernel

without_editor_info theorem linear19 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes19 i).directions j)
      (graphStar edges (fun i => (envelopes19 i).base) constantsClass i) = 0 := by
  intro i k
  rw [zeroDirections19 i k]
  simp [wildForm]

without_editor_info theorem cross19 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes19 (edges e).src).directions j) ((envelopes19 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections19 ((edges e).src) i]
  simp [wildForm]

without_editor_info theorem value19 : vectorGraph edges (fun i => (envelopes19 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell19 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-15) (hy : (3 : ℤ)^3 ∣ y-23) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 15 23 3 envelopes19 constantsClass 1 constants_checked checks19 linear19 cross19 value19 (all_nonzero hf) hx hy

without_editor_info def envelopes20 : Fin 25 → WildEnvelope := (fun i => (#[⟨![1,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,1,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks20 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes20 i) (residueE (3^3) (values 6 5 i)) 3 (real i) := by decide +kernel

without_editor_info theorem zeroDirections20 : ∀ i : Fin 25, ∀ j : Fin 4,
    (envelopes20 i).directions j=0 := by decide +kernel

without_editor_info theorem linear20 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes20 i).directions j)
      (graphStar edges (fun i => (envelopes20 i).base) constantsClass i) = 0 := by
  intro i k
  rw [zeroDirections20 i k]
  simp [wildForm]

without_editor_info theorem cross20 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes20 (edges e).src).directions j) ((envelopes20 (edges e).dst).directions k) = 0 := by
  intro e i k
  rw [zeroDirections20 ((edges e).src) i]
  simp [wildForm]

without_editor_info theorem value20 : vectorGraph edges (fun i => (envelopes20 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell20 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-6) (hy : (3 : ℤ)^3 ∣ y-5) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 6 5 3 envelopes20 constantsClass 1 constants_checked checks20 linear20 cross20 value20 (all_nonzero hf) hx hy

without_editor_info def envelopes21 : Fin 25 → WildEnvelope := (fun i => (#[⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,1,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks21 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes21 i) (residueE (3^3) (values 21 8 i)) 3 (real i) := by decide +kernel

without_editor_info theorem fixedDirections21 : ∀ i : Fin 25,
    i=3 ∨ (envelopes21 i).directions=0 := by decide +kernel

without_editor_info theorem linear21 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes21 i).directions j)
      (graphStar edges (fun i => (envelopes21 i).base) constantsClass i) = 0 := by
  have h : ∀ k : Fin 4, wildForm ((envelopes21 3).directions k)
      (graphStar edges (fun i => (envelopes21 i).base) constantsClass 3)=0 := by
    simp only [graphStar_neighbors edges neighbors adjacency_checked]
    decide +kernel
  intro i k
  rcases fixedDirections21 i with rfl | hz
  · exact h k
  · rw [hz]; simp [wildForm]

without_editor_info theorem cross21 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes21 (edges e).src).directions j) ((envelopes21 (edges e).dst).directions k) = 0 := by
  intro e i k
  rcases fixedDirections21 (edges e).src with hs | hz
  · rcases fixedDirections21 (edges e).dst with ht | hz
    · exact False.elim (noLoops e (hs.trans ht.symm))
    · rw [hz]; simp [wildForm]
  · rw [hz]; simp [wildForm]

without_editor_info theorem value21 : vectorGraph edges (fun i => (envelopes21 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell21 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-21) (hy : (3 : ℤ)^3 ∣ y-8) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 21 8 3 envelopes21 constantsClass 1 constants_checked checks21 linear21 cross21 value21 (all_nonzero hf) hx hy

without_editor_info def envelopes22 : Fin 25 → WildEnvelope := (fun i => (#[⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,1,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks22 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes22 i) (residueE (3^3) (values 12 17 i)) 3 (real i) := by decide +kernel

without_editor_info theorem fixedDirections22 : ∀ i : Fin 25,
    i=3 ∨ (envelopes22 i).directions=0 := by decide +kernel

without_editor_info theorem linear22 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes22 i).directions j)
      (graphStar edges (fun i => (envelopes22 i).base) constantsClass i) = 0 := by
  have h : ∀ k : Fin 4, wildForm ((envelopes22 3).directions k)
      (graphStar edges (fun i => (envelopes22 i).base) constantsClass 3)=0 := by
    simp only [graphStar_neighbors edges neighbors adjacency_checked]
    decide +kernel
  intro i k
  rcases fixedDirections22 i with rfl | hz
  · exact h k
  · rw [hz]; simp [wildForm]

without_editor_info theorem cross22 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes22 (edges e).src).directions j) ((envelopes22 (edges e).dst).directions k) = 0 := by
  intro e i k
  rcases fixedDirections22 (edges e).src with hs | hz
  · rcases fixedDirections22 (edges e).dst with ht | hz
    · exact False.elim (noLoops e (hs.trans ht.symm))
    · rw [hz]; simp [wildForm]
  · rw [hz]; simp [wildForm]

without_editor_info theorem value22 : vectorGraph edges (fun i => (envelopes22 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell22 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-12) (hy : (3 : ℤ)^3 ∣ y-17) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 12 17 3 envelopes22 constantsClass 1 constants_checked checks22 linear22 cross22 value22 (all_nonzero hf) hx hy

without_editor_info def envelopes23 : Fin 25 → WildEnvelope := (fun i => (#[⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,1,0],![1,1,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks23 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes23 i) (residueE (3^3) (values 3 26 i)) 3 (real i) := by decide +kernel

without_editor_info theorem fixedDirections23 : ∀ i : Fin 25,
    i=3 ∨ (envelopes23 i).directions=0 := by decide +kernel

without_editor_info theorem linear23 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes23 i).directions j)
      (graphStar edges (fun i => (envelopes23 i).base) constantsClass i) = 0 := by
  have h : ∀ k : Fin 4, wildForm ((envelopes23 3).directions k)
      (graphStar edges (fun i => (envelopes23 i).base) constantsClass 3)=0 := by
    simp only [graphStar_neighbors edges neighbors adjacency_checked]
    decide +kernel
  intro i k
  rcases fixedDirections23 i with rfl | hz
  · exact h k
  · rw [hz]; simp [wildForm]

without_editor_info theorem cross23 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes23 (edges e).src).directions j) ((envelopes23 (edges e).dst).directions k) = 0 := by
  intro e i k
  rcases fixedDirections23 (edges e).src with hs | hz
  · rcases fixedDirections23 (edges e).dst with ht | hz
    · exact False.elim (noLoops e (hs.trans ht.symm))
    · rw [hz]; simp [wildForm]
  · rw [hz]; simp [wildForm]

without_editor_info theorem value23 : vectorGraph edges (fun i => (envelopes23 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell23 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-3) (hy : (3 : ℤ)^3 ∣ y-26) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 3 26 3 envelopes23 constantsClass 1 constants_checked checks23 linear23 cross23 value23 (all_nonzero hf) hx hy

without_editor_info def envelopes24 : Fin 25 → WildEnvelope := (fun i => (#[⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,1,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,0,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,1,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks24 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes24 i) (residueE (3^3) (values 18 2 i)) 3 (real i) := by decide +kernel

without_editor_info theorem fixedDirections24 : ∀ i : Fin 25,
    i=24 ∨ (envelopes24 i).directions=0 := by decide +kernel

without_editor_info theorem linear24 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes24 i).directions j)
      (graphStar edges (fun i => (envelopes24 i).base) constantsClass i) = 0 := by
  have h : ∀ k : Fin 4, wildForm ((envelopes24 24).directions k)
      (graphStar edges (fun i => (envelopes24 i).base) constantsClass 24)=0 := by
    simp only [graphStar_neighbors edges neighbors adjacency_checked]
    decide +kernel
  intro i k
  rcases fixedDirections24 i with rfl | hz
  · exact h k
  · rw [hz]; simp [wildForm]

without_editor_info theorem cross24 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes24 (edges e).src).directions j) ((envelopes24 (edges e).dst).directions k) = 0 := by
  intro e i k
  rcases fixedDirections24 (edges e).src with hs | hz
  · rcases fixedDirections24 (edges e).dst with ht | hz
    · exact False.elim (noLoops e (hs.trans ht.symm))
    · rw [hz]; simp [wildForm]
  · rw [hz]; simp [wildForm]

without_editor_info theorem value24 : vectorGraph edges (fun i => (envelopes24 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell24 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-18) (hy : (3 : ℤ)^3 ∣ y-2) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 18 2 3 envelopes24 constantsClass 1 constants_checked checks24 linear24 cross24 value24 (all_nonzero hf) hx hy

without_editor_info def envelopes25 : Fin 25 → WildEnvelope := (fun i => (#[⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,2,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,1,2,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,0,0,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,1,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks25 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes25 i) (residueE (3^3) (values 9 11 i)) 3 (real i) := by decide +kernel

without_editor_info theorem fixedDirections25 : ∀ i : Fin 25,
    i=24 ∨ (envelopes25 i).directions=0 := by decide +kernel

without_editor_info theorem linear25 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes25 i).directions j)
      (graphStar edges (fun i => (envelopes25 i).base) constantsClass i) = 0 := by
  have h : ∀ k : Fin 4, wildForm ((envelopes25 24).directions k)
      (graphStar edges (fun i => (envelopes25 i).base) constantsClass 24)=0 := by
    simp only [graphStar_neighbors edges neighbors adjacency_checked]
    decide +kernel
  intro i k
  rcases fixedDirections25 i with rfl | hz
  · exact h k
  · rw [hz]; simp [wildForm]

without_editor_info theorem cross25 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes25 (edges e).src).directions j) ((envelopes25 (edges e).dst).directions k) = 0 := by
  intro e i k
  rcases fixedDirections25 (edges e).src with hs | hz
  · rcases fixedDirections25 (edges e).dst with ht | hz
    · exact False.elim (noLoops e (hs.trans ht.symm))
    · rw [hz]; simp [wildForm]
  · rw [hz]; simp [wildForm]

without_editor_info theorem value25 : vectorGraph edges (fun i => (envelopes25 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell25 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-9) (hy : (3 : ℤ)^3 ∣ y-11) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 9 11 3 envelopes25 constantsClass 1 constants_checked checks25 linear25 cross25 value25 (all_nonzero hf) hx hy

without_editor_info def envelopes26 : Fin 25 → WildEnvelope := (fun i => (#[⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,2,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,1,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,1,1],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![2,0,1,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,2,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,1,1,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,0,2,2],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![1,1,0,0],![![0,0,0,0],![0,0,0,0],![0,0,0,0],![0,0,0,0]]⟩,⟨![0,0,0,0],![![0,0,1,0],![1,1,0,0],![0,0,0,0],![0,0,0,0]]⟩] : Array (WildEnvelope))[i.val]'(by simpa using i.isLt))

without_editor_info theorem checks26 : ∀ i : Fin 25, wildEnvelopeCheck (envelopes26 i) (residueE (3^3) (values 0 20 i)) 3 (real i) := by decide +kernel

without_editor_info theorem fixedDirections26 : ∀ i : Fin 25,
    i=24 ∨ (envelopes26 i).directions=0 := by decide +kernel

without_editor_info theorem linear26 : ∀ i : Fin 25, ∀ j : Fin 4,
    wildForm ((envelopes26 i).directions j)
      (graphStar edges (fun i => (envelopes26 i).base) constantsClass i) = 0 := by
  have h : ∀ k : Fin 4, wildForm ((envelopes26 24).directions k)
      (graphStar edges (fun i => (envelopes26 i).base) constantsClass 24)=0 := by
    simp only [graphStar_neighbors edges neighbors adjacency_checked]
    decide +kernel
  intro i k
  rcases fixedDirections26 i with rfl | hz
  · exact h k
  · rw [hz]; simp [wildForm]

without_editor_info theorem cross26 : ∀ e : Fin 70, ∀ j k : Fin 4,
    wildForm ((envelopes26 (edges e).src).directions j) ((envelopes26 (edges e).dst).directions k) = 0 := by
  intro e i k
  rcases fixedDirections26 (edges e).src with hs | hz
  · rcases fixedDirections26 (edges e).dst with ht | hz
    · exact False.elim (noLoops e (hs.trans ht.symm))
    · rw [hz]; simp [wildForm]
  · rw [hz]; simp [wildForm]

without_editor_info theorem value26 : vectorGraph edges (fun i => (envelopes26 i).base) constantsClass wildBilinear = 1 := by
  simp only [edges, vectorGraph_listEdges]
  decide +kernel

without_editor_info theorem cell26 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-0) (hy : (3 : ℤ)^3 ∣ y-20) : graphSum edges (values x y) constants wild = 1 :=
  wild_cell edges values constants real values_congr values_real 0 20 3 envelopes26 constantsClass 1 constants_checked checks26 linear26 cross26 value26 (all_nonzero hf) hx hy

without_editor_info noncomputable def localSum (x y : ℤ) : ZMod 3 := graphSum edges (values x y) constants wild

without_editor_info def residues : Fin 27 → ℤ × ℤ × ℕ := (fun i => (#[(26,21,3),(17,12,3),(8,3,3),(23,9,3),(14,0,3),(5,18,3),(20,24,3),(11,15,3),(2,6,3),(25,2,3),(16,2,3),(7,2,3),(22,20,3),(13,20,3),(4,20,3),(19,11,3),(10,11,3),(1,11,3),(24,14,3),(15,23,3),(6,5,3),(21,8,3),(12,17,3),(3,26,3),(18,2,3),(9,11,3),(0,20,3)] : Array (ℤ × ℤ × ℕ))[i.val]'(by simpa using i.isLt))

without_editor_info def targets : Fin 27 → ZMod 3 := (fun i => (#[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] : Array (ZMod 3))[i.val]'(by simpa using i.isLt))

without_editor_info theorem cell_value (i : Fin 27) {x y : ℤ} (hf : equation x y = 0)
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
  · exact cell9 hf hx hy
  · exact cell10 hf hx hy
  · exact cell11 hf hx hy
  · exact cell12 hf hx hy
  · exact cell13 hf hx hy
  · exact cell14 hf hx hy
  · exact cell15 hf hx hy
  · exact cell16 hf hx hy
  · exact cell17 hf hx hy
  · exact cell18 hf hx hy
  · exact cell19 hf hx hy
  · exact cell20 hf hx hy
  · exact cell21 hf hx hy
  · exact cell22 hf hx hy
  · exact cell23 hf hx hy
  · exact cell24 hf hx hy
  · exact cell25 hf hx hy
  · exact cell26 hf hx hy

without_editor_info theorem covered0 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-26) (hy : (3 : ℤ)^3 ∣ y-21) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨0,hx,hy⟩

without_editor_info theorem covered1 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-17) (hy : (3 : ℤ)^3 ∣ y-12) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨1,hx,hy⟩

without_editor_info theorem covered2 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-8) (hy : (3 : ℤ)^3 ∣ y-3) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨2,hx,hy⟩

without_editor_info theorem covered3 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-23) (hy : (3 : ℤ)^3 ∣ y-9) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨3,hx,hy⟩

without_editor_info theorem covered4 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-14) (hy : (3 : ℤ)^3 ∣ y-0) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨4,hx,hy⟩

without_editor_info theorem covered5 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-5) (hy : (3 : ℤ)^3 ∣ y-18) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨5,hx,hy⟩

without_editor_info theorem covered6 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-20) (hy : (3 : ℤ)^3 ∣ y-24) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨6,hx,hy⟩

without_editor_info theorem covered7 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-11) (hy : (3 : ℤ)^3 ∣ y-15) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨7,hx,hy⟩

without_editor_info theorem covered8 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-2) (hy : (3 : ℤ)^3 ∣ y-6) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨8,hx,hy⟩

without_editor_info theorem covered9 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-25) (hy : (3 : ℤ)^3 ∣ y-2) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨9,hx,hy⟩

without_editor_info theorem covered10 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-16) (hy : (3 : ℤ)^3 ∣ y-2) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨10,hx,hy⟩

without_editor_info theorem covered11 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-7) (hy : (3 : ℤ)^3 ∣ y-2) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨11,hx,hy⟩

without_editor_info theorem covered12 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-22) (hy : (3 : ℤ)^3 ∣ y-20) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨12,hx,hy⟩

without_editor_info theorem covered13 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-13) (hy : (3 : ℤ)^3 ∣ y-20) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨13,hx,hy⟩

without_editor_info theorem covered14 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-4) (hy : (3 : ℤ)^3 ∣ y-20) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨14,hx,hy⟩

without_editor_info theorem covered15 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-19) (hy : (3 : ℤ)^3 ∣ y-11) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨15,hx,hy⟩

without_editor_info theorem covered16 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-10) (hy : (3 : ℤ)^3 ∣ y-11) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨16,hx,hy⟩

without_editor_info theorem covered17 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-1) (hy : (3 : ℤ)^3 ∣ y-11) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨17,hx,hy⟩

without_editor_info theorem covered18 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-24) (hy : (3 : ℤ)^3 ∣ y-14) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨18,hx,hy⟩

without_editor_info theorem covered19 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-15) (hy : (3 : ℤ)^3 ∣ y-23) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨19,hx,hy⟩

without_editor_info theorem covered20 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-6) (hy : (3 : ℤ)^3 ∣ y-5) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨20,hx,hy⟩

without_editor_info theorem covered21 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-21) (hy : (3 : ℤ)^3 ∣ y-8) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨21,hx,hy⟩

without_editor_info theorem covered22 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-12) (hy : (3 : ℤ)^3 ∣ y-17) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨22,hx,hy⟩

without_editor_info theorem covered23 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-3) (hy : (3 : ℤ)^3 ∣ y-26) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨23,hx,hy⟩

without_editor_info theorem covered24 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-18) (hy : (3 : ℤ)^3 ∣ y-2) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨24,hx,hy⟩

without_editor_info theorem covered25 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-9) (hy : (3 : ℤ)^3 ∣ y-11) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨25,hx,hy⟩

without_editor_info theorem covered26 {x y : ℤ} (_hf : equation x y = 0)
    (hx : (3 : ℤ)^3 ∣ x-0) (hy : (3 : ℤ)^3 ∣ y-20) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := ⟨26,hx,hy⟩

without_editor_info theorem branch0 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^2 ∣ x-0) (hy : (3 : ℤ)^2 ∣ y-2) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    3 (by decide) 9 0 2 [(0,20),(9,11),(18,2)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · intro X Y hF hX hY
    apply covered26 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered25 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered24 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch1 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^2 ∣ x-3) (hy : (3 : ℤ)^2 ∣ y-8) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    3 (by decide) 9 3 8 [(3,26),(12,17),(21,8)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · intro X Y hF hX hY
    apply covered23 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered22 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered21 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch2 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^2 ∣ x-6) (hy : (3 : ℤ)^2 ∣ y-5) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    3 (by decide) 9 6 5 [(6,5),(15,23),(24,14)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · intro X Y hF hX hY
    apply covered20 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered19 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered18 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch3 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^1 ∣ x-0) (hy : (3 : ℤ)^1 ∣ y-2) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    3 (by decide) 3 0 2 [(0,2),(3,8),(6,5)] (by decide +kernel) ?_ hf hx hy
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
    (hx : (3 : ℤ)^2 ∣ x-1) (hy : (3 : ℤ)^2 ∣ y-2) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    3 (by decide) 9 1 2 [(1,11),(10,11),(19,11)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · intro X Y hF hX hY
    apply covered17 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered16 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered15 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch5 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^2 ∣ x-4) (hy : (3 : ℤ)^2 ∣ y-2) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    3 (by decide) 9 4 2 [(4,20),(13,20),(22,20)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · intro X Y hF hX hY
    apply covered14 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered13 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered12 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch6 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^2 ∣ x-7) (hy : (3 : ℤ)^2 ∣ y-2) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    3 (by decide) 9 7 2 [(7,2),(16,2),(25,2)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · intro X Y hF hX hY
    apply covered11 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered10 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered9 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch7 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^1 ∣ x-1) (hy : (3 : ℤ)^1 ∣ y-2) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    3 (by decide) 3 1 2 [(1,2),(4,2),(7,2)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · intro X Y hF hX hY
    apply branch4 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply branch5 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply branch6 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch8 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^2 ∣ x-2) (hy : (3 : ℤ)^2 ∣ y-6) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    3 (by decide) 9 2 6 [(2,6),(11,15),(20,24)] (by decide +kernel) ?_ hf hx hy
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

without_editor_info theorem branch9 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^2 ∣ x-5) (hy : (3 : ℤ)^2 ∣ y-0) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    3 (by decide) 9 5 0 [(5,18),(14,0),(23,9)] (by decide +kernel) ?_ hf hx hy
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

without_editor_info theorem branch10 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^2 ∣ x-8) (hy : (3 : ℤ)^2 ∣ y-3) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    3 (by decide) 9 8 3 [(8,3),(17,12),(26,21)] (by decide +kernel) ?_ hf hx hy
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

without_editor_info theorem branch11 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^1 ∣ x-2) (hy : (3 : ℤ)^1 ∣ y-0) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    3 (by decide) 3 2 0 [(2,6),(5,0),(8,3)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · intro X Y hF hX hY
    apply branch8 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply branch9 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply branch10 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch12 {x y : ℤ} (hf : equation x y = 0)
    (hx : (3 : ℤ)^0 ∣ x-0) (hy : (3 : ℤ)^0 ∣ y-0) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1)
    3 (by decide) 1 0 0 [(0,2),(1,2),(2,0)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · intro X Y hF hX hY
    apply branch3 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply branch7 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply branch11 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem local_cover {x y : ℤ} (hf : equation x y = 0) : ∃ i : Fin 27, (3 : ℤ)^(residues i).2.2 ∣ x-(residues i).1 ∧ (3 : ℤ)^(residues i).2.2 ∣ y-(residues i).2.1 := branch12 hf (by simp) (by simp)

end GraphCert.Generated.g6681fe82262d85cf066bd0fe.Proof.At3

open CubicSpecial GraphCert.Cubic

namespace GraphCert.Generated.g6681fe82262d85cf066bd0fe.Proof



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

end GraphCert.Generated.g6681fe82262d85cf066bd0fe.Proof

namespace GraphCert.Generated.g6681fe82262d85cf066bd0fe.Proof

without_editor_info theorem no_solution {x y : ℤ} (hf : equation x y = 0) : False := by
  have h := cubic_reciprocity hf
  have h2 : At2.localSum x y = 0 := by
    obtain ⟨i, hx, hy⟩ := At2.local_cover hf
    have hv := At2.cell_value i hf hx hy
    have ht : ∀ i, At2.targets i = 0 := by decide +kernel
    simpa only [hv] using ht i
  have h3 : At3.localSum x y = 1 := by
    obtain ⟨i, hx, hy⟩ := At3.local_cover hf
    have hv := At3.cell_value i hf hx hy
    have ht : ∀ i, At3.targets i = 1 := by decide +kernel
    simpa only [hv] using ht i
  all_goals
    rw [h2, h3] at h
    exact absurd h (by decide +kernel)

end GraphCert.Generated.g6681fe82262d85cf066bd0fe.Proof

namespace OriginalEquation
def f (x y : ℤ) : ℤ := 8*x^4 + x + y^3 + y - 1
theorem no_integer_solutions : ¬ ∃ x y : ℤ, f x y = 0 := by
  rintro ⟨x, y, hf⟩
  apply GraphCert.Generated.g6681fe82262d85cf066bd0fe.Proof.no_solution (x := x) (y := y)
  change GraphCert.Generated.g6681fe82262d85cf066bd0fe.Proof.equation x y = 0
  convert hf using 1 <;>
    simp [f, GraphCert.Generated.g6681fe82262d85cf066bd0fe.Proof.equation, GraphCert.Generated.g6681fe82262d85cf066bd0fe.Proof.F,
      GraphCert.Cubic.Polynomial.value, GraphCert.Cubic.Polynomial.eval, CubicSpecial.Dense.eval] <;> ring
end OriginalEquation


                                               
theorem E96191221685552745_2 : ¬ ∃ x y : ℤ, 8*x^4 + x + y^3 + y - 1 = 0 := by
  rintro ⟨x, y, h⟩
  apply OriginalEquation.no_integer_solutions
  refine ⟨x, y, ?_⟩
  dsimp [OriginalEquation.f]
  linear_combination h

#print axioms E96191221685552745_2
