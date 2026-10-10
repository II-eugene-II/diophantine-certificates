import Mathlib.Tactic.FinCases
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Data.Nat.Factorization.Induction

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

                                     
                                                                      
                                                                       
set_option Elab.async false
set_option linter.all false




   
                                                                             
                                                                                   
  
namespace QuadraticNorm

/-- Normalize constants and univariate functions when certificate rows have different types. -/
class ToBivariate (α : Type) where
  apply : α → ℤ → ℤ → ℤ

instance : ToBivariate ℤ := ⟨fun c _ _ => c⟩
instance : ToBivariate (ℤ → ℤ) := ⟨fun f x _ => f x⟩
instance : ToBivariate (ℤ → ℤ → ℤ) := ⟨id⟩

abbrev Certificate :=
  (ℤ → ℤ → ℤ) × ℤ × (ℤ → ℤ → ℤ) × (ℤ → ℤ → ℤ) × (ℤ → ℤ → ℤ)

/-- Build a uniform row for a list mixing constant and function inputs. -/
def cert {D H U V : Type} [ToBivariate D] [ToBivariate H] [ToBivariate U] [ToBivariate V]
    (d : D) (kappa : ℤ) (h : H) (u : U) (v : V) : Certificate :=
  (ToBivariate.apply d, kappa, ToBivariate.apply h, ToBivariate.apply u, ToBivariate.apply v)

abbrev Coeffs := List (ℕ × ℕ × ℤ)

def eval {R : Type*} [Ring R] (f : Coeffs) (x y : R) : R :=
  (f.map fun (i, j, c) => (c : R) * x ^ i * y ^ j).sum

theorem cast_eval (f : Coeffs) (x y : ℤ) (m : ℕ) :
    ((eval f x y : ℤ) : ZMod m) = eval f (x : ZMod m) (y : ZMod m) := by
  simp [eval, List.map_map, Function.comp_def]

theorem eval_residue_natAbs (f : Coeffs) (x y : ℤ) (m : ℕ) [NeZero m]
    (h : 0 ≤ eval f x y) :
    (eval f (x : ZMod m) (y : ZMod m)).val = (eval f x y).natAbs % m := by
  have he := congrArg (fun z : ℤ => (z : ZMod m).val) (Int.ofNat_natAbs_of_nonneg h)
  simpa only [Int.cast_natCast, ZMod.val_natCast, cast_eval] using he.symm

def NoIntZero (f : Coeffs) : Prop := ∀ x y : ℤ, eval f x y ≠ 0

/-- An inert prime dividing a quadratic norm divides both coordinates. -/
theorem inert_divides {p : ℕ} (hp : p.Prime) {d u v : ℤ}
    (hj : jacobiSym (-d) p = -1) (hn : (p : ℤ) ∣ u ^ 2 + d * v ^ 2) :
    (p : ℤ) ∣ u ∧ (p : ℤ) ∣ v := by
  letI : Fact p.Prime := ⟨hp⟩
  exact jacobiSym.prime_dvd_of_eq_neg_one hj (by simpa using hn)

/-- Inert-prime valuations of a nonzero norm are even, with no valuation bound. -/
theorem norm_even {p : ℕ} (hp : p.Prime) {d : ℤ}
    (hj : jacobiSym (-d) p = -1) (u v : ℤ)
    (hn : u ^ 2 + d * v ^ 2 ≠ 0) :
    Even (padicValInt p (u ^ 2 + d * v ^ 2)) := by
  letI : Fact p.Prime := ⟨hp⟩
  generalize hk : padicValInt p (u ^ 2 + d * v ^ 2) = k
  induction k using Nat.strong_induction_on generalizing u v with
  | h k ih =>
    by_cases hd : (p : ℤ) ∣ u ^ 2 + d * v ^ 2
    · obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := inert_divides hp hj hd
      have hid : u ^ 2 + d * v ^ 2 =
          (p : ℤ) * ((p : ℤ) * (a ^ 2 + d * b ^ 2)) := by rw [ha, hb]; ring
      have hab : a ^ 2 + d * b ^ 2 ≠ 0 := by
        intro he
        exact hn (by rw [hid, he]; ring)
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have he : k = 2 + padicValInt p (a ^ 2 + d * b ^ 2) := by
        rw [← hk, hid, padicValInt.mul hp0 (mul_ne_zero hp0 hab),
          padicValInt.mul hp0 hab, padicValInt_self]
        omega
      rw [he]
      exact Even.add (by decide) (ih _ (by omega) a b hab rfl)
    · rw [padicValInt.eq_zero_of_not_dvd hd] at hk
      subst k
      exact ⟨0, rfl⟩

private theorem jacobi_prod (a : ℤ) (s : Finset ℕ) (g : ℕ → ℕ)
    (h : ∀ i ∈ s, g i ≠ 0) :
    jacobiSym a (∏ i ∈ s, g i) = ∏ i ∈ s, jacobiSym a (g i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, g j ≠ 0 := fun j hj => h j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      jacobiSym.mul_right' a (h i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr hs), ih hs]

/-- A prime with negative symbol and odd valuation must divide the cofactor.
This is the reusable, unbounded arithmetic step in the norm method. -/
theorem norm_factor_contradiction (d h t u v : ℤ)
    (hh : h ≠ 0) (hid : h * t = u ^ 2 + d * v ^ 2)
    (hj : jacobiSym (-d) h.natAbs = -1)
    (ht : ∀ p : ℕ, p.Prime → jacobiSym (-d) p = -1 →
      (p : ℤ) ∣ h → ¬ (p : ℤ) ∣ t ∨ Even (padicValInt p h)) : False := by
  have hn : h.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hh
  have hfactor := Nat.prod_primeFactors_pow_factorization hn
  have hvalue : jacobiSym (-d) h.natAbs = 1 := by
    rw [hfactor, jacobi_prod]
    · apply Finset.prod_eq_one
      intro p hp
      obtain ⟨hpp, hpn, _⟩ := Nat.mem_primeFactors.mp hp
      letI : Fact p.Prime := ⟨hpp⟩
      have hph : (p : ℤ) ∣ h := Int.natCast_dvd.mpr hpn
      have hjnz : jacobiSym (-d) p ≠ 0 := by
        intro hz
        obtain ⟨m, hm⟩ := hpn
        have hm0 : m ≠ 0 := by intro he; simp [he] at hm; exact hh hm
        rw [hm, jacobiSym.mul_right' (-d) hpp.ne_zero hm0, hz, zero_mul] at hj
        omega
      rw [jacobiSym.pow_right]
      rcases jacobiSym.trichotomy (-d) p with hz | he | he
      · exact (hjnz hz).elim
      · rw [he, one_pow]
      · have hev : Even (padicValInt p h) := by
          rcases ht p hpp he hph with hpt | hev
          · have ht0 : t ≠ 0 := by intro he; exact hpt (he ▸ dvd_zero _)
            have hev := norm_even hpp he u v (hid ▸ mul_ne_zero hh ht0)
            rwa [← hid, padicValInt.mul hh ht0,
              padicValInt.eq_zero_of_not_dvd hpt, add_zero] at hev
          · exact hev
        have hev' : Even (h.natAbs.factorization p) := by
          simpa only [Nat.factorization_def _ hpp, padicValInt] using hev
        rw [he]
        exact hev'.neg_one_pow
    · intro p hp
      exact pow_ne_zero _ (Nat.mem_primeFactors.mp hp).1.ne_zero
  omega

/-- Clearing a known nonzero factor allows ramified factors to be removed. -/
theorem scaled_norm_factor_contradiction (d h t u v s : ℤ)
    (hdiv : s ∣ h) (hh : h ≠ 0)
    (hid : h * t = u ^ 2 + d * v ^ 2)
    (hj : jacobiSym (-d) (h / s).natAbs = -1)
    (ht : ∀ p : ℕ, p.Prime → jacobiSym (-d) p = -1 →
      (p : ℤ) ∣ h → ¬ (p : ℤ) ∣ t ∨ Even (padicValInt p h))
    (hs : ∀ p : ℕ, p.Prime → jacobiSym (-d) p = -1 → ¬ (p : ℤ) ∣ s) : False := by
  have he : h / s * s = h := Int.ediv_mul_cancel hdiv
  have hq : h / s ≠ 0 := by intro hz; exact hh (by rw [hz, zero_mul] at he; exact he.symm)
  apply norm_factor_contradiction d (h / s) (s * t) u v
  · exact hq
  · rw [← mul_assoc, he, hid]
  · exact hj
  · intro p hp hsym hd
    letI : Fact p.Prime := ⟨hp⟩
    have hph : (p : ℤ) ∣ h := he ▸ dvd_mul_of_dvd_left hd s
    rcases ht p hp hsym hph with hpt | hev
    · left
      exact fun hd => ((Int.prime_iff_natAbs_prime.mpr (by simpa using hp)).dvd_mul.mp hd).elim
        (hs p hp hsym) hpt
    · right
      have hs0 : s ≠ 0 := by intro hz; exact hs p hp hsym (hz ▸ dvd_zero _)
      rwa [← he, padicValInt.mul hq hs0, padicValInt.eq_zero_of_not_dvd (hs p hp hsym), add_zero] at hev

/-- A finite factorization certificate bounds the exceptional primes. -/
theorem prime_mem_factors {p : ℕ} (hp : p.Prime) (ps : List ℕ)
    (hps : ∀ q ∈ ps, q.Prime) (hd : p ∣ ps.prod) : p ∈ ps := by
  induction ps with
  | nil => exact (hp.not_dvd_one hd).elim
  | cons q qs ih =>
    rcases hp.dvd_mul.mp hd with hq | hqs
    · exact List.mem_cons.mpr (Or.inl ((Nat.dvd_prime (hps q (by simp))).mp hq
        |>.resolve_left hp.ne_one))
    · exact List.mem_cons.mpr (Or.inr (ih (by aesop) hqs))

theorem quotient_mod (n m s k : ℕ) (h : s * k ∣ m) :
    (n / s) % k = (n % m / s) % k := by
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mod_of_dvd n h,
    Nat.mod_mul_right_div_self]

/-- Reciprocity turns an unbounded Jacobi-symbol assertion into residue data. -/
theorem jacobi_from_residue (a : ℤ) (n m s : ℕ)
    (h2 : s * 2 ∣ m) (h4 : s * (4 * a.natAbs) ∣ m)
    (ho : (n % m / s) % 2 = 1)
    (hj : jacobiSym a ((n % m / s) % (4 * a.natAbs)) = -1) :
    jacobiSym a (n / s) = -1 := by
  have hodd : Odd (n / s) := Nat.odd_iff.mpr ((quotient_mod n m s 2 h2).trans ho)
  rw [jacobiSym.mod_right a hodd, quotient_mod n m s (4 * a.natAbs) h4, hj]

/-- The character of Q(sqrt(-7)) is periodic even on even positive inputs. -/
theorem jacobi_neg_seven (n : ℕ) (hn : n ≠ 0) :
    jacobiSym (-7) n = jacobiSym (n : ℤ) 7 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases ho : Odd n
    · have hr := jacobiSym.quadratic_reciprocity' (by decide : Odd 7) ho
      rw [qrSign.symm ho (by decide)] at hr
      have hq : qrSign 7 n = jacobiSym (-1) n := by norm_num [qrSign]
      rw [hq] at hr
      have hs : jacobiSym (-1) n ^ 2 = 1 := jacobiSym.sq_one (by simp)
      norm_num only [Nat.cast_ofNat] at hr
      rw [show (-7 : ℤ) = (-1) * 7 by norm_num, jacobiSym.mul_left, hr,
        ← mul_assoc, ← pow_two, hs, one_mul]
    · have he : n % 2 = 0 := by have := Nat.odd_iff.not.mp ho; omega
      have hhalf : n / 2 ≠ 0 := by omega
      have hsplit : n = 2 * (n / 2) := by omega
      have hj2 : jacobiSym (-7) 2 = 1 := by norm_num
      conv_lhs => rw [hsplit, jacobiSym.mul_right' (-7) (by decide) hhalf, hj2, one_mul]
      rw [ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)) hhalf]
      conv_rhs => rw [hsplit, Nat.cast_mul, jacobiSym.mul_left]; norm_num only [Nat.cast_ofNat]; rw [one_mul]

theorem integer_square_bound (z : ℤ) (k : ℕ) (h : z^2 < ((k:ℤ)+1)^2) :
    -(k:ℤ) ≤ z ∧ z ≤ k := by
  constructor
  · by_contra hn
    have hz : z ≤ -(k:ℤ)-1 := by omega
    nlinarith [mul_nonneg (show 0 ≤ -z-(k:ℤ)-1 by omega)
      (show 0 ≤ -z+(k:ℤ)+1 by omega)]
  · by_contra hn
    have hz : (k:ℤ)+1 ≤ z := by omega
    nlinarith [mul_nonneg (show 0 ≤ z-(k:ℤ)-1 by omega)
      (show 0 ≤ z+(k:ℤ)+1 by omega)]

theorem prime_dvd_pow_sub (p : ℕ) (hp : p.Prime) (z : ℤ) : (p:ℤ) ∣ z^p-z := by
  letI : Fact p.Prime := ⟨hp⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  push_cast
  rw [ZMod.pow_card, sub_self]

end QuadraticNorm

                                                        
                                                                       

namespace RatHilbert

/-- The signed unit after removing all powers of p. -/
def unitPart (p : ℕ) (a : ℤ) : ℤ := a / (p : ℤ) ^ padicValInt p a

def oddParts (p e f : ℕ) (a b : ℤ) : ℤ :=
  jacobiSym (-1) p ^ (e*f) * jacobiSym a p ^ f * jacobiSym b p ^ e

def oddH (p : ℕ) (a b : ℤ) : ℤ :=
  oddParts p (padicValInt p a) (padicValInt p b) (unitPart p a) (unitPart p b)

def qr (a b : ℤ) : ℤ := if a % 4 = 3 ∧ b % 4 = 3 then -1 else 1

def twoChar (a : ℤ) : ℤ := if a % 8 = 1 ∨ a % 8 = 7 then 1 else -1

def twoParts (e f : ℕ) (a b : ℤ) : ℤ := qr a b * twoChar a ^ f * twoChar b ^ e

def twoH (a b : ℤ) : ℤ :=
  twoParts (padicValInt 2 a) (padicValInt 2 b) (unitPart 2 a) (unitPart 2 b)

def infinity (a b : ℤ) : ℤ := if a < 0 ∧ b < 0 then -1 else 1

lemma unitPart_spec (p : ℕ) (a : ℤ) : (p : ℤ)^padicValInt p a * unitPart p a = a := by
  exact Int.mul_ediv_cancel' (padicValInt_dvd a)

lemma unitPart_not_dvd {p : ℕ} [Fact p.Prime] {a : ℤ} (ha : a ≠ 0) :
    ¬ (p : ℤ) ∣ unitPart p a := by
  intro he
  have hd : (p : ℤ)^(padicValInt p a + 1) ∣ a := by
    calc
      _ = (p : ℤ)^padicValInt p a * p := by rw [pow_succ]
      _ ∣ (p : ℤ)^padicValInt p a * unitPart p a := mul_dvd_mul_left _ he
      _ = a := unitPart_spec p a
  have ht := (padicValInt_dvd_iff (padicValInt p a + 1) a).mp hd
  rcases ht with ht | ht
  · exact ha ht
  · omega

lemma val_of_parts {p : ℕ} [Fact p.Prime] {a r : ℤ} {e : ℕ}
    (hr : ¬ (p : ℤ) ∣ r) (he : a = (p : ℤ)^e*r) : padicValInt p a = e := by
  have hp : p.Prime := Fact.out
  have hr0 : r ≠ 0 := by rintro rfl; exact hr (dvd_zero _)
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hv : padicValInt p ((p : ℤ)^e) = e := by
    simp only [padicValInt, Int.natAbs_pow, Int.natAbs_natCast]
    exact padicValNat.prime_pow e
  rw [he, padicValInt.mul (pow_ne_zero _ hp0) hr0, hv,
      padicValInt.eq_zero_of_not_dvd hr, add_zero]

lemma unitPart_of_parts {p : ℕ} [Fact p.Prime] {a r : ℤ} {e : ℕ}
    (hr : ¬ (p : ℤ) ∣ r) (he : a = (p : ℤ)^e*r) : unitPart p a = r := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold unitPart
  rw [val_of_parts hr he, he, Int.mul_ediv_cancel_left _ (pow_ne_zero _ hp0)]

lemma oddH_of_parts {p : ℕ} [Fact p.Prime] {a b r s : ℤ} {e f : ℕ}
    (hr : ¬ (p : ℤ) ∣ r) (hs : ¬ (p : ℤ) ∣ s)
    (ha : a = (p : ℤ)^e*r) (hb : b = (p : ℤ)^f*s) :
    oddH p a b = oddParts p e f r s := by
  simp only [oddH, val_of_parts hr ha, val_of_parts hs hb,
    unitPart_of_parts hr ha, unitPart_of_parts hs hb]

lemma unitPart_mul {p : ℕ} [Fact p.Prime] {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    unitPart p (a*b) = unitPart p a * unitPart p b := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  apply mul_left_cancel₀ (pow_ne_zero (padicValInt p a + padicValInt p b) hp0)
  calc
    _ = (p : ℤ)^padicValInt p (a*b) * unitPart p (a*b) := by rw [padicValInt.mul ha hb]
    _ = a*b := unitPart_spec p (a*b)
    _ = ((p : ℤ)^padicValInt p a * unitPart p a) *
        ((p : ℤ)^padicValInt p b * unitPart p b) := by rw [unitPart_spec,unitPart_spec]
    _ = _ := by rw [pow_add];ring

lemma oddParts_mul_left (p e g f : ℕ) (a c b : ℤ) :
    oddParts p (e+g) f (a*c) b = oddParts p e f a b * oddParts p g f c b := by
  simp only [oddParts,add_mul,pow_add,jacobiSym.mul_left,mul_pow]
  ring

lemma oddH_mul_left {p : ℕ} [Fact p.Prime] {a c b : ℤ} (ha : a ≠ 0) (hc : c ≠ 0) :
    oddH p (a*c) b = oddH p a b * oddH p c b := by
  simp only [oddH,padicValInt.mul ha hc,unitPart_mul ha hc,oddParts_mul_left]

lemma oddH_comm (p : ℕ) (a b : ℤ) : oddH p a b = oddH p b a := by
  unfold oddH oddParts
  rw [Nat.mul_comm]
  ring

lemma odd_mod_four {a : ℤ} (ha : Odd a) : a%4=1 ∨ a%4=3 := by
  have h := Int.odd_iff.mp ha
  omega

lemma twoChar_eq_chi (a : ℤ) (ha : Odd a) : twoChar a = ZMod.χ₈ a := by
  rw [ZMod.χ₈_int_eq_if_mod_eight]
  simp [twoChar,Int.odd_iff.mp ha]

lemma twoChar_mul {a b : ℤ} (ha : Odd a) (hb : Odd b) :
    twoChar (a*b) = twoChar a * twoChar b := by
  rw [twoChar_eq_chi _ (ha.mul hb),twoChar_eq_chi _ ha,twoChar_eq_chi _ hb]
  simp only [Int.cast_mul,map_mul]

lemma qr_eq_chi {a b : ℤ} (ha : Odd a) :
    qr a b = if b%4=3 then ZMod.χ₄ a else 1 := by
  rw [ZMod.χ₄_int_eq_if_mod_four]
  rcases odd_mod_four ha with h | h <;>
    by_cases hb : b%4=3 <;> simp [qr,h,hb,Int.odd_iff.mp ha]

lemma qr_mul_left {a b c : ℤ} (ha : Odd a) (hb : Odd b) :
    qr (a*b) c = qr a c * qr b c := by
  rw [qr_eq_chi (ha.mul hb),qr_eq_chi ha,qr_eq_chi hb]
  split_ifs <;> simp only [Int.cast_mul,map_mul,one_mul]

lemma twoParts_mul_left {a c b : ℤ} (ha : Odd a) (hc : Odd c) (e g f : ℕ) :
    twoParts (e+g) f (a*c) b = twoParts e f a b * twoParts g f c b := by
  simp only [twoParts,qr_mul_left ha hc,twoChar_mul ha hc,pow_add,mul_pow]
  ring

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

lemma odd_not_two_dvd {a : ℤ} (ha : Odd a) : ¬(2:ℤ)∣a := by
  simpa only [← even_iff_two_dvd] using Int.not_even_iff_odd.mpr ha

lemma not_two_dvd_odd {a : ℤ} (ha : ¬(2:ℤ)∣a) : Odd a := by
  simpa only [← even_iff_two_dvd, Int.not_even_iff_odd] using ha

lemma unitPart_two_odd {a : ℤ} (ha : a ≠ 0) : Odd (unitPart 2 a) := by
  exact not_two_dvd_odd (unitPart_not_dvd (p:=2) ha)

lemma twoH_mul_left {a c b : ℤ} (ha : a ≠ 0) (hc : c ≠ 0) :
    twoH (a*c) b = twoH a b * twoH c b := by
  simp only [twoH,padicValInt.mul ha hc,unitPart_mul ha hc,
    twoParts_mul_left (unitPart_two_odd ha) (unitPart_two_odd hc)]

lemma twoH_comm (a b : ℤ) : twoH a b = twoH b a := by
  unfold twoH twoParts qr
  simp only [and_comm]
  ring

lemma twoH_of_parts {a b r s : ℤ} {e f : ℕ} (hr : Odd r) (hs : Odd s)
    (ha : a = (2:ℤ)^e*r) (hb : b = (2:ℤ)^f*s) :
    twoH a b = twoParts e f r s := by
  have hr' : ¬(2:ℤ)∣r := odd_not_two_dvd hr
  have hs' : ¬(2:ℤ)∣s := odd_not_two_dvd hs
  simp only [twoH,val_of_parts hr' ha,val_of_parts hs' hb,
    unitPart_of_parts hr' ha,unitPart_of_parts hs' hb]

lemma jacobi_prime_sq {p : ℕ} [Fact p.Prime] {a : ℤ} (ha : ¬(p:ℤ)∣a) :
    jacobiSym a p ^ 2 = 1 := by
  rw [←jacobiSym.legendreSym.to_jacobiSym]
  apply legendreSym.sq_one p
  intro h
  exact ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)

lemma power_sq (z : ℤ) (n : ℕ) : (z^n)^2=(z^2)^n := by
  rw [←pow_mul,Nat.mul_comm n 2,pow_mul]

lemma prime_not_dvd_one (p : ℕ) (hp : p.Prime) : ¬(p:ℤ)∣(1:ℤ) := by
  intro h
  have hn : p∣1 := by exact_mod_cast h
  exact hp.ne_one (Nat.dvd_one.mp hn)

lemma prime_not_dvd_neg_one (p : ℕ) (hp : p.Prime) : ¬(p:ℤ)∣(-1:ℤ) := by
  simpa using prime_not_dvd_one p hp

lemma oddH_sq {p : ℕ} [Fact p.Prime] (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    oddH p a b ^ 2 = 1 := by
  have hn := prime_not_dvd_neg_one p (Fact.out : p.Prime)
  unfold oddH oddParts
  simp only [mul_pow,power_sq]
  rw [jacobi_prime_sq hn,jacobi_prime_sq (unitPart_not_dvd ha),
      jacobi_prime_sq (unitPart_not_dvd hb)]
  simp

lemma twoH_sq (a b : ℤ) : twoH a b ^ 2 = 1 := by
  have hq (x y : ℤ) : qr x y ^ 2 = 1 := by simp [qr]
  have hc (x : ℤ) : twoChar x ^ 2 = 1 := by simp [twoChar]
  simp only [twoH,twoParts,mul_pow,power_sq,hq,hc,one_pow,mul_one]

lemma infinity_sq (a b : ℤ) : infinity a b ^ 2 = 1 := by simp [infinity]

lemma infinity_comm (a b : ℤ) : infinity a b = infinity b a := by simp [infinity,and_comm]

lemma infinity_mul_left {a c b : ℤ} (ha : a ≠ 0) (hc : c ≠ 0) :
    infinity (a*c) b = infinity a b * infinity c b := by
  rcases lt_or_gt_of_ne ha with ha | ha <;> rcases lt_or_gt_of_ne hc with hc | hc
  · have h := mul_pos_of_neg_of_neg ha hc
    by_cases hb : b<0 <;> simp [infinity,ha,hc,not_lt_of_gt h,hb]
  · have h := mul_neg_of_neg_of_pos ha hc
    simp [infinity,ha,not_lt_of_gt hc,h]
  · have h := mul_neg_of_pos_of_neg ha hc
    simp [infinity,not_lt_of_gt ha,hc,h]
  · have h := mul_pos ha hc
    simp [infinity,not_lt_of_gt ha,not_lt_of_gt hc,not_lt_of_gt h]

def total (S : Finset ℕ) (a b : ℤ) : ℤ :=
  infinity a b * twoH a b * ∏ p ∈ S, oddH p a b

lemma total_comm (S : Finset ℕ) (a b : ℤ) : total S a b = total S b a := by
  simp only [total,infinity_comm a b,twoH_comm a b,oddH_comm _ a b]

lemma total_mul_left {S : Finset ℕ} (hS : ∀p∈S,p.Prime) {a c b : ℤ}
    (ha : a ≠ 0) (hc : c ≠ 0) : total S (a*c) b = total S a b * total S c b := by
  have hh : (∏p∈S,oddH p (a*c) b) = (∏p∈S,oddH p a b * oddH p c b) := by
    apply Finset.prod_congr rfl
    intro p hp
    exact @oddH_mul_left p ⟨hS p hp⟩ a c b ha hc
  simp only [total,infinity_mul_left ha hc,twoH_mul_left ha hc,hh,Finset.prod_mul_distrib]
  ring

lemma total_mul_right {S : Finset ℕ} (hS : ∀p∈S,p.Prime) {a b c : ℤ}
    (hb : b ≠ 0) (hc : c ≠ 0) : total S a (b*c) = total S a b * total S a c := by
  rw [total_comm,total_mul_left hS hb hc,total_comm S b,total_comm S c]

@[simp] lemma oddH_one (p : ℕ) (a : ℤ) : oddH p 1 a = 1 := by
  simp [oddH,oddParts,unitPart]

@[simp] lemma twoH_one (a : ℤ) : twoH 1 a = 1 := by
  simp [twoH,twoParts,qr,twoChar,unitPart]

@[simp] lemma total_one (S : Finset ℕ) (a : ℤ) : total S 1 a = 1 := by
  simp [total,infinity]

lemma prime_not_dvd_prime {p q : ℕ} (hp:p.Prime) (hq:q.Prime) (hne:p≠q) :
    ¬(p:ℤ)∣(q:ℤ) := by
  intro h
  have hn : p∣q := by exact_mod_cast h
  rcases (Nat.dvd_prime hq).mp hn with h | h
  · exact hp.ne_one h
  · exact hne h

lemma oddH_units {p : ℕ} {a b : ℤ} (ha:¬(p:ℤ)∣a) (hb:¬(p:ℤ)∣b) :
    oddH p a b=1 := by
  simp [oddH,oddParts,padicValInt.eq_zero_of_not_dvd ha,padicValInt.eq_zero_of_not_dvd hb]

lemma oddH_prime_unit {p : ℕ} [Fact p.Prime] {b:ℤ} (hb:¬(p:ℤ)∣b) :
    oddH p p b=jacobiSym b p := by
  simp [oddH,oddParts,padicValInt.eq_zero_of_not_dvd hb,unitPart]

lemma oddH_prime_self {p:ℕ} [Fact p.Prime] : oddH p p p=jacobiSym (-1) p := by
  have hp0 : (p:ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  simp [oddH,oddParts,unitPart,Int.ediv_self hp0]

lemma twoH_odd {a b:ℤ} (ha:Odd a) (hb:Odd b) : twoH a b=qr a b := by
  rw [twoH_of_parts ha hb (e:=0) (f:=0) (by simp) (by simp)]
  simp [twoParts]

lemma twoH_two_odd {b:ℤ} (hb:Odd b) : twoH 2 b=twoChar b := by
  rw [twoH_of_parts (by decide : Odd (1:ℤ)) hb (e:=1) (f:=0) (by norm_num) (by simp)]
  simp [twoParts,qr,twoChar]

lemma cast_prime_odd {p:ℕ} (hp:p.Prime) (hp2:p≠2) : Odd (p:ℤ) := by
  exact_mod_cast hp.odd_of_ne_two hp2

lemma jacobi_neg_one_qr {p:ℕ} (hp:p.Prime) (hp2:p≠2) :
    jacobiSym (-1) p=qr (-1) p := by
  rw [jacobiSym.at_neg_one (hp.odd_of_ne_two hp2),ZMod.χ₄_nat_eq_if_mod_four]
  have ho := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have h4 := Nat.odd_mod_four_iff.mp ho
  have hc : (p:ℤ)%4 = (p%4:ℕ) := by omega
  rcases h4 with h4 | h4 <;> simp [qr,h4,ho,hc]

lemma jacobi_two_char {p:ℕ} (hp:p.Prime) (hp2:p≠2) :
    jacobiSym 2 p=twoChar p := by
  rw [twoChar_eq_chi _ (cast_prime_odd hp hp2),jacobiSym.at_two (hp.odd_of_ne_two hp2)]
  norm_cast

lemma qr_self_eq_neg_one (p:ℕ) : qr (p:ℤ) p=qr (-1) p := by
  simp [qr]

lemma jacobi_reciprocity_product {p q:ℕ} [Fact p.Prime] (hp2:p≠2)
    (hq:q.Prime) (hq2:q≠2) (hne:p≠q) :
    jacobiSym (q:ℤ) p * jacobiSym (p:ℤ) q=qr (p:ℤ) q := by
  have hp : p.Prime := Fact.out
  have h := jacobiSym.quadratic_reciprocity_if
    (Nat.odd_iff.mp (hp.odd_of_ne_two hp2)) (Nat.odd_iff.mp (hq.odd_of_ne_two hq2))
  have hs := jacobi_prime_sq (prime_not_dvd_prime hp hq hne)
  have hc : ((p:ℤ)%4=3 ∧ (q:ℤ)%4=3) ↔ (p%4=3 ∧ q%4=3) := by
    norm_cast
  unfold qr
  simp only [hc]
  split_ifs with hh
  · simp only [if_pos hh] at h
    rw [←h]
    nlinarith
  · simp only [if_neg hh] at h
    rw [←h]
    nlinarith

lemma total_neg_neg (S:Finset ℕ) (hS:∀p∈S,p.Prime) : total S (-1) (-1)=1 := by
  have hh : (∏p∈S,oddH p (-1) (-1))=1 := by
    apply Finset.prod_eq_one
    intro p hp
    exact oddH_units (prime_not_dvd_neg_one p (hS p hp)) (prime_not_dvd_neg_one p (hS p hp))
  simp only [total,hh]
  rw [twoH_odd (by decide) (by decide)]
  norm_num [infinity,qr]

lemma total_neg_two (S:Finset ℕ) (hS:∀p∈S,p.Prime ∧ p≠2) : total S (-1) 2=1 := by
  have hh : (∏p∈S,oddH p (-1) 2)=1 := by
    apply Finset.prod_eq_one
    intro p hp
    exact oddH_units (prime_not_dvd_neg_one p (hS p hp).1)
      (prime_not_dvd_prime (hS p hp).1 (by decide) (hS p hp).2)
  simp only [total,hh]
  rw [twoH_comm,twoH_two_odd (by decide)]
  norm_num [infinity,twoChar]

lemma total_two_two (S:Finset ℕ) (hS:∀p∈S,p.Prime ∧ p≠2) : total S 2 2=1 := by
  have hh : (∏p∈S,oddH p 2 2)=1 := by
    apply Finset.prod_eq_one
    intro p hp
    exact oddH_units (prime_not_dvd_prime (hS p hp).1 (by decide) (hS p hp).2)
      (prime_not_dvd_prime (hS p hp).1 (by decide) (hS p hp).2)
  simp only [total,hh]
  rw [twoH_of_parts (by decide : Odd (1:ℤ)) (by decide : Odd (1:ℤ))
    (e:=1) (f:=1) (by norm_num) (by norm_num)]
  norm_num [infinity,twoParts,qr,twoChar]

lemma odd_product_single {S:Finset ℕ} {r:ℕ} (hr:r∈S) (a b:ℤ)
    (h:∀p∈S,p≠r → oddH p a b=1) :
    (∏p∈S,oddH p a b)=oddH r a b := by
  exact Finset.prod_eq_single r h (by simp [hr])

lemma odd_product_double {S:Finset ℕ} {r s:ℕ} (hr:r∈S) (hs:s∈S) (hne:r≠s) (a b:ℤ)
    (h:∀p∈S,p≠r → p≠s → oddH p a b=1) :
    (∏p∈S,oddH p a b)=oddH r a b*oddH s a b := by
  rw [←Finset.mul_prod_erase S _ hr]
  congr 1
  apply odd_product_single (Finset.mem_erase.mpr ⟨Ne.symm hne,hs⟩)
  intro p hp hpne
  exact h p (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp) hpne

lemma total_neg_prime {S:Finset ℕ} (hS:∀p∈S,p.Prime ∧ p≠2)
    {q:ℕ} (hq:q∈S) : total S (-1) q=1 := by
  have hqp := (hS q hq).1
  have hq2 := (hS q hq).2
  have hh : (∏p∈S,oddH p (-1) q)=oddH q (-1) q := by
    apply odd_product_single hq
    intro p hp hpq
    exact oddH_units (prime_not_dvd_neg_one p (hS p hp).1)
      (prime_not_dvd_prime (hS p hp).1 hqp hpq)
  rw [total,hh,twoH_odd (by decide) (cast_prime_odd hqp hq2),oddH_comm]
  rw [@oddH_prime_unit q ⟨hqp⟩ (-1) (prime_not_dvd_neg_one q hqp)]
  rw [←jacobi_neg_one_qr hqp hq2]
  have hs := @jacobi_prime_sq q ⟨hqp⟩ (-1) (prime_not_dvd_neg_one q hqp)
  have hq0 : (0:ℤ) ≤ q := by positivity
  simp only [infinity,not_lt_of_ge hq0,and_false,if_false,one_mul]
  nlinarith

lemma total_two_prime {S:Finset ℕ} (hS:∀p∈S,p.Prime ∧ p≠2)
    {q:ℕ} (hq:q∈S) : total S 2 q=1 := by
  have hqp := (hS q hq).1
  have hq2 := (hS q hq).2
  have hh : (∏p∈S,oddH p 2 q)=oddH q 2 q := by
    apply odd_product_single hq
    intro p hp hpq
    exact oddH_units (prime_not_dvd_prime (hS p hp).1 (by decide) (hS p hp).2)
      (prime_not_dvd_prime (hS p hp).1 hqp hpq)
  rw [total,hh,twoH_two_odd (cast_prime_odd hqp hq2),oddH_comm]
  rw [@oddH_prime_unit q ⟨hqp⟩ 2 (prime_not_dvd_prime hqp (by decide) hq2)]
  rw [←jacobi_two_char hqp hq2]
  have hs := @jacobi_prime_sq q ⟨hqp⟩ 2 (prime_not_dvd_prime hqp (by decide) hq2)
  norm_num [infinity]
  nlinarith

lemma total_prime_self {S:Finset ℕ} (hS:∀p∈S,p.Prime ∧ p≠2)
    {q:ℕ} (hq:q∈S) : total S q q=1 := by
  have hqp := (hS q hq).1
  have hq2 := (hS q hq).2
  have hh : (∏p∈S,oddH p q q)=oddH q q q := by
    apply odd_product_single hq
    intro p hp hpq
    exact oddH_units (prime_not_dvd_prime (hS p hp).1 hqp hpq)
      (prime_not_dvd_prime (hS p hp).1 hqp hpq)
  rw [total,hh,twoH_odd (cast_prime_odd hqp hq2) (cast_prime_odd hqp hq2),qr_self_eq_neg_one]
  rw [@oddH_prime_self q ⟨hqp⟩,←jacobi_neg_one_qr hqp hq2]
  have hs := @jacobi_prime_sq q ⟨hqp⟩ (-1) (prime_not_dvd_neg_one q hqp)
  have hq0 : (0:ℤ) ≤ q := by positivity
  simp only [infinity,not_lt_of_ge hq0,false_and,if_false,one_mul]
  nlinarith

lemma total_prime_prime {S:Finset ℕ} (hS:∀p∈S,p.Prime ∧ p≠2)
    {p q:ℕ} (hp:p∈S) (hq:q∈S) : total S p q=1 := by
  by_cases he:p=q
  · subst q
    exact total_prime_self hS hp
  have hpp := (hS p hp).1
  have hp2 := (hS p hp).2
  have hqp := (hS q hq).1
  have hq2 := (hS q hq).2
  have hh : (∏r∈S,oddH r p q)=oddH p p q*oddH q p q := by
    apply odd_product_double hp hq he
    intro r hr hrp hrq
    exact oddH_units (prime_not_dvd_prime (hS r hr).1 hpp hrp)
      (prime_not_dvd_prime (hS r hr).1 hqp hrq)
  rw [total,hh,twoH_odd (cast_prime_odd hpp hp2) (cast_prime_odd hqp hq2)]
  rw [@oddH_prime_unit p ⟨hpp⟩ q (prime_not_dvd_prime hpp hqp he),oddH_comm q]
  rw [@oddH_prime_unit q ⟨hqp⟩ p (prime_not_dvd_prime hqp hpp (Ne.symm he))]
  rw [@jacobi_reciprocity_product p q ⟨hpp⟩ hp2 hqp hq2 he]
  have hp0 : (0:ℤ) ≤ p := by positivity
  simp only [infinity,not_lt_of_ge hp0,false_and,if_false,one_mul]
  unfold qr
  split_ifs <;> norm_num

/-- Integers whose prime support outside 2 lies in S. -/
def Supported (S : Finset ℕ) (a : ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ a.natAbs → p = 2 ∨ p ∈ S

lemma int_prime_induction {S : Finset ℕ} (P : ℤ → Prop)
    (h1 : P 1) (hn : P (-1))
    (hp : ∀ p : ℕ, p.Prime → (p = 2 ∨ p ∈ S) → P p)
    (hm : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → P a → P b → P (a*b))
    {a : ℤ} (ha : a ≠ 0) (hs : Supported S a) : P a := by
  have hall : ∀ n : ℕ, n ≠ 0 → (∀p:ℕ,p.Prime → p∣n → p=2 ∨ p∈S) → P (n:ℤ) := by
    refine induction_on_primes ?_ ?_ ?_
    · intro h0
      exact False.elim (h0 rfl)
    · intro _ _
      exact h1
    · intro p n hprime ih hpn hsupp
      have hn0 := right_ne_zero_of_mul hpn
      have hpp := hp p hprime (hsupp p hprime (dvd_mul_right p n))
      have hnn := ih hn0 (fun q hq hd => hsupp q hq (dvd_mul_of_dvd_right hd p))
      simpa only [Nat.cast_mul] using hm (p:ℤ) (n:ℤ)
        (by exact_mod_cast hprime.ne_zero) (by exact_mod_cast hn0) hpp hnn
  have hna : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha
  have habs : P (a.natAbs:ℤ) := hall a.natAbs hna hs
  rcases le_total 0 a with ha0 | ha0
  · simpa only [Int.natAbs_of_nonneg ha0] using habs
  · have he : a=(-1)*(a.natAbs:ℤ) := by
      calc a = -(a.natAbs:ℤ) := Int.eq_neg_natAbs_of_nonpos ha0
           _ = (-1)*(a.natAbs:ℤ) := by ring
    rw [he]
    exact hm (-1) (a.natAbs:ℤ) (by norm_num) (by exact_mod_cast hna) hn habs

/-- A generator is -1, 2, or one of the odd primes in S. -/
def Generator (S : Finset ℕ) (a : ℤ) : Prop :=
  a = -1 ∨ a = 2 ∨ ∃p∈S,a=(p:ℤ)

lemma total_generators {S:Finset ℕ} (hS:∀p∈S,p.Prime ∧ p≠2)
    {a b:ℤ} (ha:Generator S a) (hb:Generator S b) : total S a b=1 := by
  rcases ha with rfl | rfl | ⟨p,hp,rfl⟩ <;>
    rcases hb with rfl | rfl | ⟨q,hq,rfl⟩
  · exact total_neg_neg S (fun p hp => (hS p hp).1)
  · exact total_neg_two S hS
  · exact total_neg_prime hS hq
  · rw [total_comm]
    exact total_neg_two S hS
  · exact total_two_two S hS
  · exact total_two_prime hS hq
  · rw [total_comm]
    exact total_neg_prime hS hp
  · rw [total_comm]
    exact total_two_prime hS hp
  · exact total_prime_prime hS hp hq

lemma total_generator_all {S:Finset ℕ} (hS:∀p∈S,p.Prime ∧ p≠2)
    {a b:ℤ} (ha:Generator S a) (hb:b≠0) (hs:Supported S b) : total S a b=1 := by
  apply int_prime_induction (S:=S) (fun b => total S a b=1) ?_ ?_ ?_ ?_ hb hs
  · rw [total_comm,total_one]
  · exact total_generators hS ha (Or.inl rfl)
  · intro p hp hcover
    apply total_generators hS ha
    rcases hcover with rfl | hm
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨p,hm,rfl⟩)
  · intro b c hb hc hbj hck
    rw [total_mul_right (fun p hp => (hS p hp).1) hb hc,hbj,hck,mul_one]

/-- Elementary Hilbert reciprocity, proved using quadratic reciprocity on prime generators. -/
theorem total_eq_one {S:Finset ℕ} (hS:∀p∈S,p.Prime ∧ p≠2)
    {a b:ℤ} (ha:a≠0) (hb:b≠0) (hsa:Supported S a) (hsb:Supported S b) :
    total S a b=1 := by
  apply int_prime_induction (S:=S) (fun a => total S a b=1) ?_ ?_ ?_ ?_ ha hsa
  · exact total_one S b
  · exact total_generator_all hS (Or.inl rfl) hb hsb
  · intro p hp hcover
    apply total_generator_all hS ?_ hb hsb
    rcases hcover with rfl | hm
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨p,hm,rfl⟩)
  · intro a c ha hc haj hck
    rw [total_mul_left (fun p hp => (hS p hp).1) ha hc,haj,hck,mul_one]

lemma cast_ne_zero_of_not_dvd {p : ℕ} {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    (a : ZMod p) ≠ 0 := by
  simpa only [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd] using ha

lemma jacobi_unit_cases {p : ℕ} [Fact p.Prime] {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    jacobiSym a p = 1 ∨ jacobiSym a p = -1 := by
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  exact legendreSym.eq_one_or_neg_one p (cast_ne_zero_of_not_dvd ha)

lemma oddH_unit_right {p : ℕ} [Fact p.Prime] {a b : ℤ} (hb : ¬ (p : ℤ) ∣ b) :
    oddH p a b = jacobiSym b p ^ padicValInt p a := by
  simp [oddH, oddParts, unitPart, padicValInt.eq_zero_of_not_dvd hb]

lemma jacobi_one_not_dvd {p : ℕ} [Fact p.Prime] {a : ℤ}
    (ha : jacobiSym a p = 1) : ¬ (p : ℤ) ∣ a := by
  intro hd
  have hz : legendreSym p a = 0 := (legendreSym.eq_zero_iff p a).mpr
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd)
  rw [jacobiSym.legendreSym.to_jacobiSym, ha] at hz
  norm_num at hz

lemma oddH_of_jacobi_right {p : ℕ} [Fact p.Prime] {a b : ℤ}
    (hb : jacobiSym b p = 1) : oddH p a b = 1 := by
  rw [oddH_unit_right (jacobi_one_not_dvd hb), hb, one_pow]

lemma oddH_of_jacobi_left {p : ℕ} [Fact p.Prime] {a b : ℤ}
    (ha : jacobiSym a p = 1) : oddH p a b = 1 := by
  rw [oddH_comm]
  exact oddH_of_jacobi_right ha

lemma jacobi_one_of_norm_unit {p : ℕ} [Fact p.Prime] {b r c : ℤ}
    (hb : ¬ (p : ℤ) ∣ b) (hc : ¬ (p : ℤ) ∣ c)
    (hd : (p : ℤ) ∣ r^2-b*c^2) : jacobiSym b p = 1 := by
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  apply legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero
    (cast_ne_zero_of_not_dvd hb) (cast_ne_zero_of_not_dvd hc)
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
  push_cast at h
  exact h

lemma norm_unit_even {p : ℕ} [Fact p.Prime] {d : ℤ} (hl : jacobiSym d p = -1)
    (u v : ℤ) (hn0 : u^2-d*v^2 ≠ 0) : Even (padicValInt p (u^2-d*v^2)) := by
  simpa [sub_eq_add_neg] using QuadraticNorm.norm_even (Fact.out : p.Prime)
    (d := -d) (by simpa using hl) u v (by simpa [sub_eq_add_neg] using hn0)

lemma oddH_norm_unit {p : ℕ} [Fact p.Prime] {b r c : ℤ}
    (hb : ¬ (p : ℤ) ∣ b) (hn : r^2-b*c^2 ≠ 0) :
    oddH p (r^2-b*c^2) b = 1 := by
  rw [oddH_unit_right hb]
  rcases jacobi_unit_cases hb with h | h
  · rw [h, one_pow]
  · rw [h]
    exact (norm_unit_even h r c hn).neg_one_pow

lemma prime_cast {p : ℕ} [Fact p.Prime] : Prime (p : ℤ) := by
  apply Int.prime_iff_natAbs_prime.mpr
  simpa using (show p.Prime from Fact.out)

lemma norm_prime_not_dvd_one {p : ℕ} [Fact p.Prime] : ¬ (p : ℤ) ∣ (1 : ℤ) := by
  exact (prime_cast (p:=p)).not_dvd_one

lemma oddH_square_mul_left {p : ℕ} [Fact p.Prime] {a b z : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hz : z ≠ 0) :
    oddH p (z^2*a) b = oddH p a b := by
  rw [oddH_mul_left (pow_ne_zero _ hz) ha, pow_two, oddH_mul_left hz hz]
  have h := oddH_sq (p:=p) z b hz hb
  rw [←pow_two,h,one_mul]

lemma oddH_square_mul_right {p : ℕ} [Fact p.Prime] {a b z : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hz : z ≠ 0) :
    oddH p a (z^2*b) = oddH p a b := by
  rw [oddH_comm, oddH_square_mul_left hb ha hz, oddH_comm]

lemma oddH_norm_first_unit {p : ℕ} [Fact p.Prime] {a b r c : ℤ}
    (ha : ¬ (p : ℤ) ∣ a) (hb : (p : ℤ) ∣ b)
    (hid : a = r^2-b*c^2) : oddH p a b = 1 := by
  apply oddH_of_jacobi_left
  apply jacobi_one_of_norm_unit ha norm_prime_not_dvd_one (r:=r) (c:=1)
  have he : r^2-a*1^2=b*c^2 := by linear_combination -hid
  rw [he]
  exact dvd_mul_of_dvd_left hb (c^2)

lemma oddH_norm_b_val_one {p : ℕ} [Fact p.Prime] {a b r c : ℤ}
    (hb : ¬ (p : ℤ) ∣ b) (hc : ¬ (p : ℤ) ∣ c)
    (hid : a + b*c^2 = (p : ℤ)*r^2) :
    oddH p ((p:ℤ)*a) ((p:ℤ)*b) = 1 := by
  have ha : ¬ (p : ℤ) ∣ a := by
    intro hd
    have ht : (p:ℤ)∣b*c^2 := by
      have hh : (p:ℤ)∣a+b*c^2 := by rw [hid]; exact dvd_mul_right _ _
      simpa using dvd_sub hh hd
    rcases prime_cast.dvd_mul.mp ht with h | h
    · exact hb h
    · exact hc (prime_cast.dvd_of_dvd_pow h)
  have hn : ¬ (p : ℤ) ∣ -a*b := by
    intro hd
    rcases prime_cast.dvd_mul.mp hd with h | h
    · exact ha (by simpa using h)
    · exact hb h
  have hj : jacobiSym (-a*b) p = 1 := by
    apply jacobi_one_of_norm_unit hn norm_prime_not_dvd_one (r:=b*c) (c:=1)
    have hh : (b*c)^2-(-a*b)*1^2 = b*((p:ℤ)*r^2) := by linear_combination b*hid
    rw [hh]
    exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  have ha' : (p:ℤ)*a = (p:ℤ)^1*a := by ring
  have hb' : (p:ℤ)*b = (p:ℤ)^1*b := by ring
  rw [oddH_of_parts ha hb ha' hb']
  simp only [oddParts, one_mul, pow_one]
  have he : -a*b = (-1:ℤ)*a*b := by ring
  rw [he,jacobiSym.mul_left,jacobiSym.mul_left] at hj
  exact hj

lemma oddH_norm {p : ℕ} [Fact p.Prime] {a b r c : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hid : a = r^2-b*c^2) : oddH p a b = 1 := by
  generalize hk : padicValInt p a + padicValInt p b = k
  induction k using Nat.strong_induction_on generalizing a b r c with
  | h k ih =>
    have hp : p.Prime := Fact.out
    have hp0 : (p:ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hvp : padicValInt p ((p:ℤ)^2) = 2 := by
      simp only [padicValInt,Int.natAbs_pow,Int.natAbs_natCast]
      exact padicValNat.prime_pow 2
    by_cases hpb : (p:ℤ)∣b
    · by_cases hpa : (p:ℤ)∣a
      · have hpr : (p:ℤ)∣r := by
          apply prime_cast.dvd_of_dvd_pow (n:=2)
          have hh := dvd_add hpa (dvd_mul_of_dvd_left hpb (c^2))
          convert hh using 1; nlinarith [hid]
        obtain ⟨r',hr⟩ := hpr
        by_cases hpc : (p:ℤ)∣c
        · obtain ⟨c',hc⟩ := hpc
          let a' := r'^2-b*c'^2
          have hae : a = (p:ℤ)^2*a' := by dsimp [a']; rw [hid,hr,hc]; ring
          have ha0 : a' ≠ 0 := by intro h; apply ha; rw [hae,h,mul_zero]
          have hval : padicValInt p a = 2 + padicValInt p a' := by
            rw [hae,padicValInt.mul (pow_ne_zero _ hp0) ha0,hvp]
          have hi := ih (padicValInt p a'+padicValInt p b) (by omega) ha0 hb (r:=r') (c:=c') rfl rfl
          rw [hae,oddH_square_mul_left ha0 hb hp0]
          exact hi
        · obtain ⟨b',hbe⟩ := hpb
          by_cases hpb' : (p:ℤ)∣b'
          · obtain ⟨b'',hbe'⟩ := hpb'
            have hbex : b = (p:ℤ)^2*b'' := by rw [hbe,hbe']; ring
            let a' := r'^2-b''*c^2
            have hae : a = (p:ℤ)^2*a' := by dsimp [a']; rw [hid,hr,hbex]; ring
            have ha0 : a' ≠ 0 := by intro h; apply ha; rw [hae,h,mul_zero]
            have hb0 : b'' ≠ 0 := by intro h; apply hb; rw [hbex,h,mul_zero]
            have hva : padicValInt p a = 2 + padicValInt p a' := by
              rw [hae,padicValInt.mul (pow_ne_zero _ hp0) ha0,hvp]
            have hvb : padicValInt p b = 2 + padicValInt p b'' := by
              rw [hbex,padicValInt.mul (pow_ne_zero _ hp0) hb0,hvp]
            have hi := ih (padicValInt p a'+padicValInt p b'') (by omega) ha0 hb0 (r:=r') (c:=c) rfl rfl
            rw [hae,oddH_square_mul_left ha0 hb hp0,hbex,oddH_square_mul_right ha0 hb0 hp0]
            exact hi
          · obtain ⟨a',hae⟩ := hpa
            have hrel : a'+b'*c^2 = (p:ℤ)*r'^2 := by
              apply mul_left_cancel₀ hp0
              rw [hid,hr,hbe] at hae
              nlinarith [hae]
            rw [hae,hbe]
            exact oddH_norm_b_val_one hpb' hpc hrel
      · exact oddH_norm_first_unit hpa hpb hid
    · rw [hid]
      exact oddH_norm_unit hpb (by rw [← hid]; exact ha)

/-- Cancel a sign without repeating the same square-and-multiply calculation. -/
private lemma eq_of_mul_eq_one {a b : ℤ} (h : a * b = 1) (hb : b ^ 2 = 1) : a = b := by
  rcases sq_eq_one_iff.mp hb with rfl | rfl <;> linarith

theorem global_except {E : Finset ℕ}
    (hE : ∀ p ∈ E, p.Prime ∧ p ≠ 2)
    {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hodd : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ E → oddH p a b = 1) :
    twoH a b * (∏ p ∈ E, oddH p a b) = infinity a b := by
  let S : Finset ℕ := E ∪ ((a.natAbs.primeFactors ∪ b.natAbs.primeFactors).erase 2)
  have hES : E ⊆ S := Finset.subset_union_left
  have hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2 := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hE p hp
    rcases Finset.mem_erase.mp hp with ⟨hp2, hp⟩
    rcases Finset.mem_union.mp hp with hp | hp
    · exact ⟨(Nat.mem_primeFactors.mp hp).1, hp2⟩
    · exact ⟨(Nat.mem_primeFactors.mp hp).1, hp2⟩
  have supported (c : ℤ) (hc : c ≠ 0)
      (hsub : c.natAbs.primeFactors ⊆ a.natAbs.primeFactors ∪ b.natAbs.primeFactors) :
      Supported S c := by
    intro p hp hd
    by_cases hp2 : p = 2
    · exact Or.inl hp2
    exact Or.inr (Finset.mem_union_right _ (Finset.mem_erase.mpr
      ⟨hp2, hsub (Nat.mem_primeFactors.mpr ⟨hp, hd, Int.natAbs_ne_zero.mpr hc⟩)⟩))
  have hh : (∏ p ∈ S, oddH p a b) = ∏ p ∈ E, oddH p a b := by
    symm
    apply Finset.prod_subset hES
    intro p hp hpE
    exact hodd p (hS p hp).1 (hS p hp).2 hpE
  have ht := total_eq_one hS ha hb
    (supported a ha Finset.subset_union_left) (supported b hb Finset.subset_union_right)
  unfold total at ht
  rw [hh] at ht
  apply eq_of_mul_eq_one ?_ (infinity_sq a b)
  simpa [mul_assoc, mul_comm, mul_left_comm] using ht

lemma infinity_norm {a b r c : ℤ} (hid : a = r^2 - b*c^2) :
    infinity a b = 1 := by
  unfold infinity
  split_ifs with h
  · have hbc : b*c^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt h.2) (sq_nonneg c)
    nlinarith [sq_nonneg r]
  · rfl

/-- The norm identity is split at 2, deduced from odd-prime norms and reciprocity. -/
theorem twoH_norm {a b r c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hid : a = r^2 - b*c^2) : twoH a b = 1 := by
  have hg := global_except (E := ∅) (by simp) ha hb
    (by
      intro p hp _ _
      exact @oddH_norm p ⟨hp⟩ a b r c ha hb hid)
  simpa [infinity_norm hid] using hg

theorem twoH_norm_cofactor {a b t r c : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0)
    (hid : a*t = r^2 - b*c^2) : twoH a b = twoH t b := by
  have hn := twoH_norm (mul_ne_zero ha ht) hb hid
  rw [twoH_mul_left ha ht] at hn
  exact eq_of_mul_eq_one hn (twoH_sq t b)

theorem oddH_norm_cofactor {p : ℕ} [Fact p.Prime] {a b t r c : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0)
    (hid : a*t = r^2 - b*c^2) : oddH p a b = oddH p t b := by
  have hn := oddH_norm (p := p) (mul_ne_zero ha ht) hb hid
  rw [oddH_mul_left ha ht] at hn
  exact eq_of_mul_eq_one hn (oddH_sq t b ht hb)

end RatHilbert

namespace QuadraticNorm
open RatHilbert

theorem eval_mod (f : Coeffs) (x y : ℤ) (m : ℕ) :
    eval f x y % m = eval f (x % m) (y % m) % m := by
  apply (ZMod.intCast_eq_intCast_iff' _ _ m).mp
  simp only [cast_eval, ZMod.intCast_mod]

theorem norm_bezout_symbol {p : ℕ} [Fact p.Prime] {a b r c t e g k : ℤ}
    (hb : ¬ (p : ℤ) ∣ b) (hn : r^2-b*c^2 = a*t)
    (hk : e*r+g*c = k) (hpk : ¬ (p : ℤ) ∣ k) : oddH p a b = 1 := by
  by_cases ha : (p : ℤ) ∣ a
  · apply oddH_of_jacobi_right
    rcases jacobi_unit_cases hb with hj | hj
    · exact hj
    · have hd : (p : ℤ) ∣ r^2-b*c^2 := hn ▸ dvd_mul_of_dvd_left ha t
      obtain ⟨hr, hc⟩ := jacobiSym.prime_dvd_of_eq_neg_one hj hd
      exact (hpk (hk ▸ dvd_add (dvd_mul_of_dvd_right hr e) (dvd_mul_of_dvd_right hc g))).elim
  · exact oddH_units ha hb

/-- The norm's inert valuation condition removes every unramified local symbol. -/
theorem norm_factor_symbol {p : ℕ} [Fact p.Prime] {d h t u v : ℤ}
    (hd : ¬ (p:ℤ) ∣ -d) (hh : h ≠ 0) (hid : h*t=u^2+d*v^2)
    (ht : ∀ p : ℕ, p.Prime → jacobiSym (-d) p = -1 → (p:ℤ) ∣ h →
      ¬ (p:ℤ) ∣ t ∨ Even (padicValInt p h)) : oddH p h (-d) = 1 := by
  rcases jacobi_unit_cases hd with hj | hj
  · exact oddH_of_jacobi_right hj
  by_cases hph : (p:ℤ) ∣ h
  · have hev : Even (padicValInt p h) := by
      rcases ht p Fact.out hj hph with hpt | he
      · have ht0 : t ≠ 0 := by intro he; exact hpt (he ▸ dvd_zero _)
        have he := norm_even (Fact.out : p.Prime) hj u v (hid ▸ mul_ne_zero hh ht0)
        rwa [← hid,padicValInt.mul hh ht0,padicValInt.eq_zero_of_not_dvd hpt,add_zero] at he
      · exact he
    simp [oddH,oddParts,unitPart,padicValInt.eq_zero_of_not_dvd hd,hj,hev.neg_one_pow]
  · exact oddH_units hph hd

theorem pair_off_support {p : ℕ} [Fact p.Prime]
    {a b r c t s d v e g k e' g' k' l m n : ℤ}
    (h1 : r^2-b*c^2 = a*t) (h2 : s^2-a*d^2 = b*v)
    (hb1 : e*r+g*c = k) (hb2 : e'*s+g'*d = k') (hc : l*a+m*b = n)
    (hk : ¬ (p : ℤ) ∣ k) (hk' : ¬ (p : ℤ) ∣ k') (hn : ¬ (p : ℤ) ∣ n) :
    oddH p a b = 1 := by
  by_cases ha : (p : ℤ) ∣ a
  · have hb : ¬ (p : ℤ) ∣ b := by
      intro hb
      exact hn (hc ▸ dvd_add (dvd_mul_of_dvd_right ha l) (dvd_mul_of_dvd_right hb m))
    exact norm_bezout_symbol hb h1 hb1 hk
  · rw [oddH_comm]
    exact norm_bezout_symbol ha h2 hb2 hk'

theorem twoH_unit_square_right (a b : ℤ) (hb : b % 8 = 1) : twoH a b = 1 := by
  have hodd : Odd b := Int.odd_iff.mpr (by omega)
  have hunit : ¬ (2 : ℤ) ∣ b := by intro hd; have := Int.emod_eq_zero_of_dvd hd; omega
  have h4 : b % 4 = 1 := by omega
  simp [twoH, twoParts, unitPart, padicValInt.eq_zero_of_not_dvd hunit, qr, twoChar, hb, h4]

/-- Integer powers dominate the square when the power is even or the base is nonnegative. -/
theorem int_sq_le_pow (x : ℤ) (n : ℕ) (hn : 2 ≤ n)
    (hx : 0 ≤ x ∨ Even n) : x^2 ≤ x^n := by
  have pos (z : ℤ) (hz : 0 ≤ z) : z^2 ≤ z^n := by
    by_cases h : z = 0
    · subst z
      simp [Nat.ne_zero_of_lt (show 0 < n by omega)]
    · exact pow_le_pow_right₀ (by omega : 1 ≤ z) hn
  rcases le_total 0 x with h | h
  · exact pos x h
  · rcases hx with hx | he
    · exact pos x hx
    · simpa only [neg_sq, he.neg_pow] using pos (-x) (by omega)

/-- Conditions visible modulo an odd prime that force a trivial local symbol. -/
abbrev residueSplit (p : ℕ) (a b : ZMod p) : Prop :=
  (a ≠ 0 ∧ b ≠ 0) ∨ (a ≠ 0 ∧ a^(p/2) = 1) ∨ (b ≠ 0 ∧ b^(p/2) = 1)

theorem residueSplit_square_left {p : ℕ} [Fact p.Prime] {a b r : ZMod p}
    (ha : a ≠ 0) (hr : a = r*r) : residueSplit p a b :=
  Or.inr (Or.inl ⟨ha,(ZMod.euler_criterion p ha).mp ⟨r,hr⟩⟩)

theorem residueSplit_square_right {p : ℕ} [Fact p.Prime] {a b r : ZMod p}
    (hb : b ≠ 0) (hr : b = r*r) : residueSplit p a b :=
  Or.inr (Or.inr ⟨hb,(ZMod.euler_criterion p hb).mp ⟨r,hr⟩⟩)

theorem oddH_residueSplit {p : ℕ} [Fact p.Prime] {a b : ℤ}
    (h : residueSplit p (a : ZMod p) (b : ZMod p)) : oddH p a b = 1 := by
  rcases h with ⟨ha,hb⟩ | ⟨ha,hr⟩ | ⟨hb,hr⟩
  · exact oddH_units (fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h))
      (fun h => hb ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h))
  · apply oddH_of_jacobi_left
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    exact (legendreSym.eq_one_iff p ha).mpr ((ZMod.euler_criterion p ha).mpr hr)
  · apply oddH_of_jacobi_right
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    exact (legendreSym.eq_one_iff p hb).mpr ((ZMod.euler_criterion p hb).mpr hr)

/-- Normalize coefficient lists once, for identities and finite kernel checks. -/
macro "norm_expand" : tactic =>
  `(tactic| dsimp +zetaDelta only [QuadraticNorm.eval, List.map, List.sum, List.foldr])
macro "norm_polynomial" : tactic => `(tactic| (norm_expand; ring))
macro "norm_finite" : tactic => `(tactic| (norm_expand; decide +kernel))

end QuadraticNorm

/- Computational polynomial algebra used only to propose certificates.
   Every proposed identity is subsequently proved by `ring` in Lean. -/
elab "without_editor_info " c:command : command =>
  Lean.Elab.withEnableInfoTree false (Lean.Elab.Command.elabCommand c)

namespace QuadraticNorm.Search

-- Separate auxiliary lemmas bound the kernel's memory for finite tables.
private def finiteTableProof (modulus : ℕ) (expand : Bool := false) : String :=
  let row := if expand then "norm_finite" else "decide +kernel"
  if modulus < 64 then row
  else "(intro a; fin_cases a <;> " ++ row ++ ")"


abbrev Poly := List (ℕ × ℕ × ℚ)
abbrev Attempt := Except String
abbrev Lines := List String

def indent (n : ℕ) (ls : Lines) : Lines :=
  ls.map (String.ofList (List.replicate n ' ') ++ ·)
def branch (n : ℕ) : Lines → Lines
  | [] => []
  | line::rest => indent n (("· "++line)::indent 2 rest)
def join (sep : String) (ls : List String) : String := String.intercalate sep ls
def natList (ns : List ℕ) : String := "[" ++ join ", " (ns.map toString) ++ "]"
def znum (n : ℤ) : String := if n < 0 then s!"({n})" else toString n

namespace Poly

def insert (i j : ℕ) (c : ℚ) : Poly → Poly
  | [] => if c == 0 then [] else [(i,j,c)]
  | (a,b,d)::ps =>
    if i == a && j == b then
      if c+d == 0 then ps else (i,j,c+d)::ps
    else if i > a || (i == a && j > b) then
      if c == 0 then (a,b,d)::ps else (i,j,c)::(a,b,d)::ps
    else (a,b,d)::insert i j c ps

def norm (p : Poly) : Poly := p.foldl (fun q (i,j,c) => insert i j c q) []
def c (a : ℚ) : Poly := if a == 0 then [] else [(0,0,a)]
def X : Poly := [(1,0,1)]
def Y : Poly := [(0,1,1)]
/-- Merge normalized terms in linear time. -/
def add : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | (i,j,a)::ps, (k,l,b)::qs =>
    if i == k && j == l then
      if a+b == 0 then add ps qs else (i,j,a+b)::add ps qs
    else if i > k || (i == k && j > l) then (i,j,a)::add ps ((k,l,b)::qs)
    else (k,l,b)::add ((i,j,a)::ps) qs
def scale (a : ℚ) (p : Poly) : Poly :=
  if a == 0 then [] else p.map fun (i,j,b) => (i,j,a*b)
def neg (p : Poly) : Poly := scale (-1) p
def sub (p q : Poly) : Poly := add p (neg q)
def mul (p q : Poly) : Poly := p.foldl (fun r (i,j,a) =>
  add r (q.map fun (k,l,b) => (i+k,j+l,a*b))) []
def pow (p : Poly) (n : ℕ) : Poly :=
  if n = 0 then c 1 else if n = 1 then p else
  let half := pow p (n/2)
  let square := mul half half
  if n%2 == 0 then square else mul p square
termination_by n
decreasing_by omega

instance : Add Poly := ⟨add⟩
instance : Neg Poly := ⟨neg⟩
instance : Sub Poly := ⟨sub⟩
instance : Mul Poly := ⟨mul⟩
instance : Pow Poly ℕ := ⟨pow⟩

def coeff (p : Poly) (i j : ℕ) : ℚ :=
  (p.find? fun t => t.1 == i && t.2.1 == j).map (·.2.2) |>.getD 0
def axis (p : Poly) (v : Bool) (n : ℕ) : Poly := norm (p.filterMap fun (i,j,a) =>
  if (if v then j else i) == n then some (if v then (i,0,a) else (0,j,a)) else none)
def degree (p : Poly) (v : Bool) : ℕ :=
  p.foldl (fun n (i,j,_) => max n (if v then j else i)) 0
def constant? (p : Poly) : Option ℚ :=
  if p.all (fun (i,j,_) => i == 0 && j == 0) then some (coeff p 0 0) else none
def integral (p : Poly) : Bool := p.all (fun (_,_,a) => a.den == 1)
def subst (p a b : Poly) : Poly :=
  p.foldl (fun q (i,j,z) => q + scale z (a^i*b^j)) []
def valueAt (p : Poly) (a b : ℤ) : ℚ :=
  p.foldl (fun z (i,j,c) => z+c*(a:ℚ)^i*(b:ℚ)^j) 0
def atMod (p : Poly) (a b : ℕ) (m : ℕ) : ℕ :=
  ((p.foldl (fun z (i,j,c) => (z+c.num*(a:ℤ)^i*(b:ℤ)^j) % m) 0 : ℤ) % m).toNat

def text (p : Poly) : String :=
  "[" ++ join ", " (p.map fun (i,j,a) => s!"({i}, {j}, {a.num})") ++ "]"
def expr (p : Poly) : String :=
  if p.isEmpty then "0" else "(" ++ join " + " (p.map fun (i,j,a) =>
    znum a.num ++ (if i==0 then "" else if i==1 then " * x" else s!" * x^{i}") ++
    (if j==0 then "" else if j==1 then " * y" else s!" * y^{j}")) ++ ")"

/-- Reduction in a finite coefficient field, or in Q when modulus = 0. -/
def field (modulus : ℕ) (p : Poly) : Poly :=
  if modulus == 0 then p else p.filterMap fun (i,j,a) =>
    let inverse := if a.den == 1 then 1 else Nat.gcdA (a.den % modulus) modulus
    let b := (a.num*inverse) % modulus
    if b == 0 then none else some (i,j,(b:ℚ))

def divRem (p q : Poly) (v : Bool) (modulus : ℕ := 0) : Attempt (Poly × Poly) := do
  if q.isEmpty then throw "Division by zero polynomial"
  let deg := q.degree v
  let some lc := (q.axis v deg).constant? | throw "Polynomial division needs a scalar leading coefficient"
  let mut r := field modulus p
  let mut quotient := []
  for _ in [:256] do
    if r.isEmpty || r.degree v < deg then return (quotient,r)
    let n := r.degree v
    let monomial := if v then [(0,n-deg,(1:ℚ))] else [(n-deg,0,(1:ℚ))]
    let term := field modulus (scale (1/lc) (r.axis v n * monomial))
    quotient := field modulus (quotient+term)
    r := field modulus (r-term*q)
  throw "Polynomial division budget exhausted"

def exactDiv (p q : Poly) (v : Bool) : Attempt Poly := do
  let (s,r) ← divRem p q v
  if !r.isEmpty then throw "Polynomial quotient is not exact"
  return s

def gcdex (a b : Poly) (v : Bool := false) (modulus : ℕ := 0) : Attempt (Poly × Poly × Poly) := do
  let mut r0 := field modulus a
  let mut r1 := field modulus b
  let mut s0 := c 1; let mut s1 := []
  let mut t0 := []; let mut t1 := c 1
  for _ in [:256] do
    if r1.isEmpty then
      if r0.isEmpty then throw "Zero gcd"
      let some lc := (r0.axis v (r0.degree v)).constant? | throw "Non-scalar gcd"
      return (field modulus (scale (1/lc) s0), field modulus (scale (1/lc) t0), field modulus (scale (1/lc) r0))
    let (q,r) ← divRem r0 r1 v modulus
    let ss := field modulus (s0-q*s1)
    let tt := field modulus (t0-q*t1)
    r0 := r1; r1 := r
    s0 := s1; s1 := ss
    t0 := t1; t1 := tt
  throw "Euclidean algorithm budget exhausted"

structure Tracked where
  p : Poly
  ws : List Poly
  deriving Inhabited

def reduce (b : Tracked) (basis : List Tracked) (modulus : ℕ) : Attempt Tracked := do
  let mut b := b
  for _ in [:4096] do
    let mut found := false
    for (i,j,a) in b.p do
      if found then break
      for q in basis do
        let (k,l,d) := q.p.head!
        if k ≤ i && l ≤ j then
          let t := field modulus [(i-k,j-l,a/d)]
          b := ⟨field modulus (b.p-t*q.p), b.ws.zipWith (fun u v => field modulus (u-t*v)) q.ws⟩
          found := true
          break
    if !found then return b
  throw "Polynomial reduction budget exhausted"

/-- Small tracked Groebner calculation, used only when ordinary Bezout fails. -/
def idealOne (ps : List Poly) (modulus : ℕ := 0) (extra : List Poly := [])
    (target : Poly := c 1) : Attempt (List Poly) := do
  let sources := ps++extra
  let mut basis : List Tracked := []
  for (p,i) in ps.zipIdx do
    let row ← reduce ⟨field modulus p, sources.zipIdx |>.map (fun (_,j) => c (if i==j then 1 else 0))⟩ basis modulus
    if row.p.isEmpty then continue
    basis := basis ++ [row]
  let mut pairs := (List.range basis.length).flatMap fun i => (List.range i).map (i,·)
  let mut pending := extra.zipIdx
  for _ in [:4096] do
    let residual ← reduce ⟨target,sources.map (fun _ => [])⟩ basis modulus
    if residual.p.isEmpty then return residual.ws.map (fun w => field modulus (-w))
    if let some row := basis.find? (fun row => row.p.constant?.isSome) then
      let z := row.p.coeff 0 0
      return row.ws.map (fun w => field modulus (scale (1/z) (target*w)))
    if pairs.isEmpty then
      let (p,i)::rest := pending | throw "The polynomial ideal has no constant certificate"
      pending := rest
      let row ← reduce ⟨field modulus p, sources.zipIdx |>.map
        (fun (_,j) => c (if ps.length+i==j then 1 else 0))⟩ basis.reverse modulus
      if row.p.isEmpty then continue
      pairs := (List.range basis.length).map (basis.length,·)
      basis := basis++[row]
      continue
    let (i,j)::rest := pairs | throw "The polynomial ideal has no constant certificate"
    pairs := rest
    let a := basis[i]!
    let b := basis[j]!
    let (ia,ja,ca) := a.p.head!
    let (ib,jb,cb) := b.p.head!
    let u := field modulus [(max ia ib-ia,max ja jb-ja,1/ca)]
    let v := field modulus [(max ia ib-ib,max ja jb-jb,1/cb)]
    let row ← reduce ⟨field modulus (u*a.p-v*b.p), a.ws.zipWith (fun s t => field modulus (u*s-v*t)) b.ws⟩ basis modulus
    if row.p.isEmpty then continue
    pairs := pairs ++ (List.range basis.length).map (basis.length,·)
    basis := basis ++ [row]
  throw "Groebner certificate budget exhausted"

def clearDenominators (ps : List Poly) : List Poly × ℕ :=
  let k : ℕ := ps.foldl (fun d p => p.foldl (fun d (_,_,a) => Nat.lcm d a.den) d) 1
  (ps.map (scale k),k)

end Poly
open Poly

def factors (n : ℕ) : Attempt (List ℕ) := do
  if n == 0 then throw "Zero exceptional-prime bound"
  let mut m := n
  let mut ps := []
  for p in [2:100001] do
    if p*p > m then
      return if m == 1 then ps else ps ++ [m]
    while m % p == 0 do
      ps := ps ++ [p]
      m := m/p
  throw "Integer factorization budget exhausted"

def primesBelow (n : ℕ) : List ℕ :=
  (List.range n).filter fun p => p ≥ 2 && (List.range (Nat.sqrt p+1)).all (fun q => q < 2 || p%q != 0)

def divisors (n : ℕ) : List ℕ := (List.range (n+1)).filter fun d => d > 0 && n%d == 0

def bezout (u v h t : Poly) : Attempt (List Poly × ℕ) := do
  let (e,g,z) ← gcdex u v
  if z == c 1 then return clearDenominators [e,g,[],[]]
  return clearDenominators (← idealOne [u,v,h,t])

structure Datum where
  d : Poly
  kappa : ℤ
  H : Poly
  U : Poly
  V : Poly
  deriving Inhabited

structure Identity extends Datum where
  T : Poly
  M : Poly
  deriving Inhabited

/-- Recover arbitrary quadratic-factor identities by inversion in Q(x)[y]/(H). -/
def quadraticIdentity (f n h : Poly) : Attempt (Poly × Poly) := do
  let (_,r) ← divRem f h true
  let (_,s) ← divRem n h true
  let q := h.coeff 0 2
  let conjugate := -(r.axis true 1*Y)+r.axis true 0-scale (1/q) (r.axis true 1*h.axis true 1)
  let (_,denominator) ← divRem (r*conjugate) h true
  let (_,numerator) ← divRem (s*conjugate) h true
  let m ← exactDiv numerator denominator false
  let t ← exactDiv (n-m*f) h true
  return (t,m)

def directNormIdentity (f : Poly) (r : Datum) : Attempt Identity := do
  if r.kappa == 0 then throw "kappa must be nonzero"
  let n := r.U^2+r.d*r.V^2
  let (t,m) ← if r.H.degree true == 1 then do
      let (sf,rf) ← divRem f r.H true
      let (sn,rn) ← divRem n r.H true
      let m ← exactDiv rn rf false
      if r.d.constant?.isSome then
        let q := r.H.coeff 0 1
        if m != c (-(r.kappa:ℚ)*q^(f.degree true)) then throw "Norm identity does not match kappa"
      pure (sn-m*sf,m)
    else if r.H.degree true == 2 && f.degree true ≥ 2 then do
      if r.d.constant?.isNone then quadraticIdentity f n r.H else do
        let q := r.H.coeff 0 2
        let power := q^(f.degree true-1)
        let (s,rem) ← divRem (scale power f) r.H true
        let l := rem.axis true 1
        let m := rem.axis true 0
        let b := r.H.axis true 1
        let w := scale q (l*Y)+b*l-scale q m
        let t := scale r.kappa (l^2+s*w)
        let m := scale (-r.kappa*power) w
        if n-r.H*t-m*f == [] then pure (t,m) else quadraticIdentity f n r.H
    else throw "Unsupported factor degree"
  if !(t.integral && m.integral) || n-r.H*t-m*f != [] then throw "Invalid integer norm identity"
  return {r with T:=t,M:=m}

/-- A checked ideal-membership fallback also supports nonmonic and higher-degree factors. -/
def normIdentity (f : Poly) (r : Datum) : Attempt Identity := do
  if let .ok result := directNormIdentity f r then return result
  if r.kappa == 0 then throw "kappa must be nonzero"
  let n := r.U^2+r.d*r.V^2
  let [t,m] ← idealOne [r.H,f] 0 [] n | throw "Invalid norm reconstruction"
  if !(t.integral && m.integral) || n-r.H*t-m*f != [] then throw "Invalid integer norm identity"
  return {r with T:=t,M:=m}

def jacobi (a : ℤ) (n : ℕ) : ℤ := Id.run do
  if n == 0 || n%2 == 0 then return 0
  let mut a := (a % n).toNat
  let mut n := n
  let mut sign : ℤ := 1
  while a != 0 do
    while a%2 == 0 do
      a := a/2
      if n%8 == 3 || n%8 == 5 then sign := -sign
    if a%4 == 3 && n%4 == 3 then sign := -sign
    let old := a
    a := n%a
    n := old
  return if n == 1 then sign else 0

structure Cone where
  x : Poly
  y : Poly
  bound : ℕ
  deriving Inhabited

/-- A finite cover of an integer quadrant by translated quadrants, rays, and points. -/
def coneBound (f : Poly) : Option ℕ :=
  (List.range 16).find? fun n =>
    let uniform := fun p : Poly => p.coeff 0 0 != 0 &&
      (p.all (fun (_,_,a) => a ≥ 0) || p.all (fun (_,_,a) => a ≤ 0))
    uniform (subst f (X+c n) (Y+c n)) &&
      (List.range n).all (fun i => uniform (subst f (c i) (Y+c n)) &&
        uniform (subst f (X+c n) (c i)) &&
        (List.range n).all (fun j => valueAt f i j != 0))

structure SignCertificate where
  reflected : Bool := false
  reflectedFactor : Poly := []
  scale : ℚ := 1
  squares : List (ℚ × Poly) := []
  const : ℚ := 0
  linear : Bool := false
  upper : Option ℤ := none
  T : Poly := []
  P : Poly := []
  D : Poly := []
  A : ℚ := 0
  B : Poly := []
  bounds : List (ℤ × ℕ) := []
  exclusions : List (ℤ × ℕ) := []
  box : Option (ℤ × ℤ × ℤ × ℤ) := none
  cutoff : ℕ := 0
  tail : ℕ := 0
  slices : List (Bool × ℤ × ℕ) := []
  factors : Option (Poly × Poly × ℚ × ℚ) := none
  dominance : Option (Bool × ℤ × ℤ × Poly) := none
  cones : List Cone := []
  deriving Inhabited

def positiveSquare (p : Poly) : Option SignCertificate := Id.run do
  if p.any (fun (i,j,_) => i+j > 2) then return none
  for v in [true,false] do
    let a := p.coeff (if v then 0 else 2) (if v then 2 else 0)
    if a ≤ 0 then continue
    let first := if v then Y else X
    let second := if v then X else Y
    let l := p.axis v 1
    let residual := scale (4*a) p-(scale (2*a) first+l)^2
    if residual.degree v > 0 then continue
    let aa := residual.coeff (if v then 2 else 0) (if v then 0 else 2)
    let bb := residual.coeff (if v then 1 else 0) (if v then 0 else 1)
    let cc := residual.coeff 0 0
    if aa > 0 then
      return some {scale:=16*a*aa, squares:=[(4*aa,scale (2*a) first+l),(1,scale (2*aa) second+c bb)], const:=4*aa*cc-bb*bb}
    if aa == 0 && bb == 0 && cc ≥ 0 then
      return some {scale:=4*a,squares:=[(1,scale (2*a) first+l)],const:=cc}
  if let some a := p.constant? then
    if a > 0 then return some {const:=a}
  return none

/-- A positive definite quadratic has only finitely many nonpositive integer values. -/
def boundedSign (f h : Poly) (cert : SignCertificate) : Option SignCertificate := do
  if cert.const > 0 then return cert
  let [(a,p),(b,q)] := cert.squares | none
  if a ≤ 0 || b ≤ 0 then none else do
  let r := Nat.sqrt ((-cert.const/a).floor.toNat)
  let s := Nat.sqrt ((-cert.const/b).floor.toNat)
  let det := p.coeff 1 0*q.coeff 0 1-q.coeff 1 0*p.coeff 0 1
  if det == 0 then none else do
  let cx := (p.coeff 0 1*q.coeff 0 0-q.coeff 0 1*p.coeff 0 0)/det
  let cy := (q.coeff 1 0*p.coeff 0 0-p.coeff 1 0*q.coeff 0 0)/det
  let rx := (abs (q.coeff 0 1)*r+abs (p.coeff 0 1)*s)/abs det
  let ry := (abs (q.coeff 1 0)*r+abs (p.coeff 1 0)*s)/abs det
  let loX := (cx-rx).ceil; let hiX := (cx+rx).floor
  let loY := (cy-ry).ceil; let hiY := (cy+ry).floor
  let nx := (hiX-loX+1).toNat; let ny := (hiY-loY+1).toNat
  if nx*ny > 4096 then none else do
  for i in [:nx] do
    for j in [:ny] do
      if valueAt f (loX+i) (loY+j) == 0 && valueAt h (loX+i) (loY+j) ≤ 0 then none
  return {cert with box:=some (loX,hiX,loY,hiY)}

def linearSign (f h : Poly) (limit : ℕ := 128) : Option SignCertificate := do
  if h.degree true != 1 || f.degree true != 3 then none else do
  let q ← (h.axis true 1).constant?
  let factor := q^3 * (if f.coeff 0 3 < 0 then -1 else 1)
  let (t,rem) ← (divRem (scale factor f) h true).toOption
  let p := -rem
  let a ← (t.axis true 2).constant?
  let b := t.axis true 1
  let d := scale (4*a) (t.axis true 0)-b^2
  if a ≤ 0 || p.degree true > 0 || d.degree true > 0 then none else do
  let bounds : List (ℤ × ℕ) ← [(-1 : ℤ),1].mapM fun (direction : ℤ) => do
    let bound ← (List.range limit).find? fun (n : ℕ) => [p,d].all fun z =>
      let shifted := subst z (scale direction (X+c (n+1))) Y
      shifted.coeff 0 0 > 0 && shifted.all (fun (_,_,a) => a ≥ 0)
    return (direction,bound+1)
  let exclusions ← (List.range (bounds[0]!.2+bounds[1]!.2-1)).filterMapM fun j => do
    let xx : ℤ := (j:ℤ)+1-bounds[0]!.2
    if valueAt p xx 0 > 0 && valueAt d xx 0 > 0 then return none
    let prime ← (primesBelow 200).find? fun p => (List.range p).all fun b =>
      atMod f (xx%p).toNat b p != 0
    return some (xx,prime)
  return {scale:=factor,linear:=true,T:=t,P:=p,D:=d,A:=a,B:=b,bounds,exclusions}

/-- Certify a half-plane by polynomial dominance and finite univariate exclusions. -/
def upperSign (f h : Poly) : Option SignCertificate := do
  if h.degree false != 0 || h.degree true != 1 || h.coeff 0 1 ≤ 0 then none else do
  let support := [(4,0),(1,1),(1,0),(0,0),(0,1),(0,2),(0,3)]
  if f.any (fun (i,j,_) => !support.contains (i,j)) then none else do
  let content : ℕ := f.foldl (fun n (_,_,a) => Nat.gcd n a.num.natAbs) 0
  let g := scale ((if f.coeff 0 3 > 0 then 1 else -1)/(content:ℚ)) f
  if g.coeff 0 3 ≤ 0 || g.coeff 4 0 ≥ 0 then none else do
  let n := (-(h.coeff 0 0)/(h.coeff 0 1)).floor
  let k := max (max 1 (-n).toNat) ((g.coeff 0 2/g.coeff 0 3).floor+1).toNat
  let b : ℕ := 3+g.foldl (fun n (_,_,a) => n+a.num.natAbs) 0
  if b > 128 || (n+(k:ℤ)).toNat > 128 then none else do
  let mut slices := []
  for axis in [true,false] do
    let lo := if axis then 1-(b:ℤ) else 1-(k:ℤ)
    let count : ℕ := if axis then 2*b-1 else (n+(k:ℤ)).toNat
    for i in [:count] do
      let z := lo+i
      let prime := (primesBelow 200).find? fun p => (List.range p).all fun t =>
        atMod f (if axis then (z%p).toNat else t) (if axis then t else (z%p).toNat) p != 0
      if let some p := prime then slices := slices++[(axis,z,p)]
      else
        let cone := -(subst g (c z) (-(c k)-Y))
        if !axis || cone.coeff 0 0 ≤ 0 || cone.any (fun (_,_,a) => a < 0) then none
        slices := slices++[(axis,z,0)]
  return {upper:=some n, P:=g, cutoff:=b, tail:=k, slices}

/-- Exclude the two integer wedges where a split quadratic could be nonpositive. -/
def wedgeSign (f h : Poly) : Option SignCertificate := do
  if h.any (fun (i,j,_) => i+j>2) then none else do
  let a := h.coeff 0 2; let b := h.coeff 1 1; let cc := h.coeff 2 0
  let delta := b*b-4*a*cc
  let s : ℚ := Nat.sqrt delta.num.toNat
  if a ≤ 0 || s ≤ 0 || s*s != delta then none else do
  let r := ((b+s)*h.coeff 0 1-2*a*h.coeff 1 0)/s
  let t := 2*h.coeff 0 1-r
  let p := scale (2*a) Y+scale (b+s) X+c r
  let q := scale (2*a) Y+scale (b-s) X+c t
  let rem := scale (4*a) h-p*q
  let k ← rem.constant?
  if k ≤ 0 || !p.integral || !q.integral then none else do
  let primitive := fun z : Poly =>
    let g := Nat.gcd (z.coeff 1 0).num.natAbs (z.coeff 0 1).num.natAbs
    (scale (1/(g:ℚ)) (z-c (z.coeff 0 0)), g, z.coeff 0 0)
  let (pp,g,pc) := primitive p; let (qq,j,qc) := primitive q
  let det := pp.coeff 1 0*qq.coeff 0 1-pp.coeff 0 1*qq.coeff 1 0
  if det != 1 && det != -1 then none else do
  let cones ← [true,false].mapM fun pos => do
    let u := if pos then X+c ((-pc/(g:ℚ)).floor+1) else -X+c ((-pc/(g:ℚ)).ceil-1)
    let v := if pos then -Y+c ((-qc/(j:ℚ)).ceil-1) else Y+c ((-qc/(j:ℚ)).floor+1)
    let xx := scale (1/det) (scale (qq.coeff 0 1) u-scale (pp.coeff 0 1) v)
    let yy := scale (1/det) (scale (pp.coeff 1 0) v-scale (qq.coeff 1 0) u)
    if !xx.integral || !yy.integral then none else do
    let bound ← coneBound (subst f xx yy)
    return {x:=xx,y:=yy,bound : Cone}
  return {factors:=some (p,q,4*a,k),cones}

/-- Bound higher powers by squares in a half-plane forced by a nonpositive factor. -/
def powerSign (f h : Poly) : Option SignCertificate := do
  for axis in [false,true] do
    let coefficient := h.coeff (if axis then 0 else 1) (if axis then 1 else 0)
    if coefficient == 0 then continue
    let axisPoly := if axis then Y else X
    let rest := h-scale coefficient axisPoly
    if rest.degree axis != 0 then continue
    let some cert := positiveSquare rest | continue
    if cert.const < 0 then continue
    let direction : ℤ := if coefficient < 0 then 1 else -1
    let xx := if axis then X else scale direction X
    let yy := if axis then scale direction Y else Y
    for sign in [(-1:ℤ),1] do
      let g := scale sign (subst f xx yy)
      let high := g.filter fun (i,j,_) => i+j>2
      if high.isEmpty || high.any (fun (i,j,a) => a<0 || (i>0 && j>0) ||
          ((if axis then i else j)%2 != 0)) then continue
      let lower := norm (g.map fun (i,j,a) => if i+j≤2 then (i,j,a) else
        if i>0 then (2,0,a) else (0,2,a))
      let some positive := positiveSquare lower | continue
      if positive.const>0 then return {cert with dominance:=some (axis,direction,sign,g)}
  none

def directSignCertificate (f h : Poly) : Attempt SignCertificate := do
  if let some cert := positiveSquare h >>= boundedSign f h then return cert
  if let some cert := linearSign f h then return cert
  if let some cert := upperSign f h then return cert
  if let some cert := wedgeSign f h then return cert
  if let some cert := powerSign f h then return cert
  throw "No sign certificate found"

def signCertificate (f h : Poly) : Attempt SignCertificate := do
  if let .ok cert := directSignCertificate f h then return cert
  let cert ← directSignCertificate (subst f X (-Y)) (subst h X (-Y))
  return {cert with reflected:=true, reflectedFactor:=subst h X (-Y)}

structure Lift where
  a : ℕ
  b : ℕ
  c : ℕ
  L : Poly
  K : Poly
  deriving Inhabited

def evenLift (f h t : Poly) (p : ℕ) : Attempt (List Lift) := do
  let mut result := []
  for a in [:p] do
    for b in [:p] do
      if atMod f a b p != 0 || atMod h a b p != 0 || atMod t a b p != 0 then continue
      let ff := subst f (c a+scale p X) (c b+scale p Y)
      let hh := subst h (c a+scale p X) (c b+scale p Y)
      let candidate : Option ℕ := (List.range p).find? (fun (cc : ℕ) => (scale (1/(p*p:ℚ)) (hh-scale (cc:ℚ) ff)).integral)
      let some cc := candidate | throw "A deeper valuation certificate is needed"
      let l := scale (1/(p:ℚ)) ff
      let k := scale (1/(p*p:ℚ)) (hh-scale cc ff)
      if (List.range p).any (fun u => (List.range p).any fun v => atMod l u v p == 0 && atMod k u v p == 0) then
        throw "The residual factor need not be a unit"
      result := result ++ [⟨a,b,cc,l,k⟩]
  return result

structure Exceptional where
  prime : ℕ
  lift : List Lift := []
  ideal : List Poly := []
  remainder : Poly := []
  fermat : Bool := false
  roots : Option (List ℕ) := none
  deriving Inhabited

structure Prepared extends Identity where
  value : ℤ
  sign : SignCertificate
  bezout : List Poly
  K : ℕ
  factors : List ℕ
  exceptional : List Exceptional
  nonzeroModulus : ℕ := 0
  cofactorSign : Bool := false
  deriving Inhabited

def prepare (f : Poly) (r : Datum) (allowSigned : Bool := false) : Attempt Prepared := do
  let some dd := r.d.constant? | throw "Use coupled reciprocity for nonconstant d"
  if dd == 0 || dd.den != 1 then throw "d must be a nonzero integer"
  let row ← normIdentity f r
  let common : ℕ := (row.U++row.V).foldl (fun n (_,_,a) => Nat.gcd n a.num.natAbs) 0
  let row := if common > 1 then
      let t := scale (1/(common*common:ℚ)) row.T
      let m := scale (1/(common*common:ℚ)) row.M
      if t.integral && m.integral then
        {row with U:=scale (1/(common:ℚ)) row.U, V:=scale (1/(common:ℚ)) row.V, T:=t, M:=m}
      else row
    else row
  let r := row.toDatum
  let (sign,nonzeroModulus,cofactorSign) ← if allowSigned && dd < 0 then do
      let some p := (primesBelow 100).find? (fun p => (List.range p).all fun a =>
        (List.range p).all fun b => atMod f a b p != 0 || atMod r.H a b p != 0)
        | throw "No finite nonvanishing certificate found"
      pure (default,p,false)
    else if let .ok sign := signCertificate f r.H then pure (sign,0,false)
    else if dd > 0 && (r.V.constant?.any (·!=0) || r.U.constant?.any (·!=0)) then
      pure (← signCertificate f row.T,0,true)
    else throw "No sign certificate found"
  let (ws,k) ← bezout r.U r.V r.H row.T
  let ps ← factors k
  let mut exceptional := []
  for p in ps.eraseDups do
    if p == 2 || jacobi (-dd.num) p != -1 then continue
    if p > 257 then
      if p ≤ 4096 && r.U.degree true == 0 && r.V.degree true == 0 then
        let roots := (List.range p).filter fun a => atMod r.U a 0 p == 0 && atMod r.V a 0 p == 0
        if roots.all (fun a => (List.range p).all fun b =>
            atMod f a b p != 0 || atMod r.H a b p != 0 || atMod row.T a b p != 0) then
          exceptional := exceptional ++ [{prime:=p,roots:=some roots}]
          continue
      let ps := [f,r.H,row.T,r.U,r.V]
      let (ws,ps,fermat) ← match idealOne ps p with
        | .ok ws => pure (ws,ps,false)
        | .error e => do
          if p > 4096 then throw s!"Finite-field degree budget exceeded at prime {p}: {e}"
          let extra := [X^p-X,Y^p-Y]
          pure (← idealOne ps p extra,ps++extra,true)
      let remainder := scale (1/(p:ℚ)) ((ws.zip ps).foldl (fun z (a,b) => z+a*b) []-c 1)
      if !remainder.integral then throw "Invalid finite-field identity"
      exceptional := exceptional ++ [{prime:=p,ideal:=ws,remainder,fermat}]
    else
      exceptional := exceptional ++ [{prime:=p,lift:= ← evenLift f r.H row.T p}]
  return {row with value:=dd.num,sign,bezout:=ws,K:=k,factors:=ps,exceptional,nonzeroModulus,cofactorSign}

structure Choice where
  index : ℕ
  scale : ℕ
  mask : Array Bool
  deriving Inhabited

def characterChoices (d : ℤ) (m : ℕ) : List (ℕ × Array Bool) := Id.run do
  if d == 7 then
    return if m%7 == 0 then [(0,(List.range m).toArray.map fun (r : ℕ) => jacobi (r:ℤ) 7 == -1)] else []
  let l := 4*d.natAbs
  if l == 0 || m%l != 0 then return []
  let mut choices := []
  for s in divisors (m/l) do
    if m%(2*s) != 0 then continue
    let .ok fs := factors s | continue
    if fs.any (fun p => (2*d)%(p:ℤ) != 0) then continue
    choices := choices ++ [(s,(List.range m).toArray.map fun r =>
      r%s == 0 && (r/s)%2 == 1 && jacobi (-d) ((r/s)%l) == -1)]
  return choices

def choices (rows : List Prepared) (m : ℕ) : List Choice :=
  rows.zipIdx.flatMap fun (r,i) => (characterChoices r.value m).map fun (s,mask) => ⟨i,s,mask⟩

structure Projection where
  modulus : ℕ
  allowed : List ℕ
  excluded : List Choice
  deriving Inhabited

structure Cover where
  modulus : ℕ
  choices : List Choice
  projection : Option (ℕ × List Projection) := none
  deriving Inhabited

def localProjection (f : Poly) (rows : List Prepared) (target q : ℕ) : Projection := Id.run do
  let exclusions := (choices rows q).filter (·.index != target)
  let mut values : Array Bool := Array.replicate q false
  for a in [:q] do
    for b in [:q] do
      if atMod f a b q != 0 then continue
      if exclusions.any (fun ch => ch.mask[atMod rows[ch.index]!.H a b q]!) then continue
      values := values.set! (atMod rows[target]!.H a b q) true
  return ⟨q,(List.range q).filter (values[·]!),exclusions⟩

def projectedChoices (cs : List Choice) (ps : List Projection) (m : ℕ) : Option (List Choice) := do
  let mut used := []
  for r in [:m] do
    if !(ps.all fun p => p.allowed.contains (r%p.modulus)) then continue
    let hit ← cs.find? (fun ch => ch.mask[r]!)
    if !(used.any fun ch => ch.index==hit.index && ch.scale==hit.scale) then used:=used++[hit]
  if used.isEmpty then none else return used

def characterCover (f : Poly) (rows : List Prepared) (limit : ℕ := 4096) : Option Cover := Id.run do
  let base := rows.foldl (fun m r => Nat.lcm m (if r.value == 7 then 7 else 4*r.value.natAbs)) 1
  if base == 0 then return none
  let mut cache : List ((ℕ × ℕ) × Projection) := []
  for step in [1:limit/base+1] do
    let m := base*step
    let cs := choices rows m
    if cs.isEmpty then continue
    if m > 100 then
      let .ok fs := factors m | continue
      let primePowers := fs.eraseDups.map (fun p => p^(fs.filter (·==p)).length) |>.filter (·≤256)
      for target in [:rows.length] do
        let extra := (divisors m).filter fun q => q ≤ 256 && !(choices rows q |>.filter (·.index != target)).isEmpty
        let qs := (primePowers++extra).eraseDups.mergeSort (·≤·)
        let mut projections := []
        for q in qs do
          let projection := match cache.find? (·.1 == (target,q)) with
            | some (_,result) => result
            | none => localProjection f rows target q
          if !(cache.any (·.1 == (target,q))) then cache := ((target,q),projection)::cache
          projections := projections ++ [projection]
        let targetChoices := cs.filter (·.index==target)
        if let some initial := projectedChoices targetChoices projections m then
          let mut used := initial
          -- Remove the most expensive redundant finite checks first.
          for p in projections.reverse do
            let smaller := projections.filter (·.modulus != p.modulus)
            if let some choices := projectedChoices targetChoices smaller m then
              projections := smaller
              used := choices
          return some ⟨m,used,some (target,projections)⟩
    if m ≤ 256 then
      let mut used := []
      let mut complete := true
      for a in [:m] do
        if !complete then break
        for b in [:m] do
          if atMod f a b m != 0 then continue
          let some hit := cs.find? (fun ch => ch.mask[atMod rows[ch.index]!.H a b m]!) | complete:=false; break
          if !(used.any fun ch => ch.index==hit.index && ch.scale==hit.scale) then used:=used++[hit]
      if complete && !used.isEmpty then return some ⟨m,used,none⟩
  return none

def splitCases (h : String) (n : ℕ) : String :=
  s!"rcases {h} with " ++ join " | " (List.replicate n h)

def sliceProof (axis : Bool) (z : ℤ) (p : ℕ) : Lines :=
  let left := if axis then s!"({z}) z" else s!"z ({z})"
  let cast := if axis then s!"(({z}:ℤ):ZMod {p}) (y:ZMod {p})" else s!"(x:ZMod {p}) (({z}:ℤ):ZMod {p})"
  [s!"have hc : ∀ z : ZMod {p}, eval F {left} ≠ 0 := by decide +kernel",
   s!"have hz : eval F {cast} = 0 := by rw [← cast_eval,hf,Int.cast_zero]", "exact hc _ hz"]

def coneProof (g : Poly) (n : ℕ) : Lines := Id.run do
  let cell := fun (a b : Option ℕ) =>
    let xx := if let some a := a then c a else X+c n
    let yy := if let some b := b then c b else Y+c n
    let p := subst g xx yy
    let sign : ℤ := if p.coeff 0 0 > 0 then 1 else -1
    let ax := a.map toString |>.getD "x"
    let byy := b.map toString |>.getD "y"
    let rhs := join " + " ((scale sign p).map fun (i,j,z) =>
      s!"({z.num}:ℤ) * ({ax}-{n})^{i} * ({byy}-{n})^{j}")
    [s!"have he : ({sign}:ℤ)*eval G {ax} {byy} = {rhs} := by norm_polynomial",
     s!"have hx0 : 0 ≤ ({ax}:ℤ)-{if a.isSome then 0 else n} := by omega",
     s!"have hy0 : 0 ≤ ({byy}:ℤ)-{if b.isSome then 0 else n} := by omega",
     s!"have hp : 0 < ({sign}:ℤ)*eval G {ax} {byy} := by rw [he]; positivity",
     "intro hz; rw [hz] at hp; norm_num at hp"]
  if n==0 then return ["intro x y hx hy"]++cell none none
  let mut lines := ["intro x y hx hy",s!"by_cases hxn : {n} ≤ x",s!"· by_cases hyn : {n} ≤ y"]
  lines := lines++branch 2 (cell none none)
  lines := lines++[s!"  · have hyb : y ≤ {n-1} := by omega","    interval_cases y"]
  for j in [:n] do lines:=lines++branch 4 (cell none (some j))
  lines:=lines++[s!"· have hxb : x ≤ {n-1} := by omega","  interval_cases x"]
  for j in [:n] do
    lines:=lines++[s!"  · by_cases hyn : {n} ≤ y"]++branch 4 (cell (some j) none)
    lines:=lines++[s!"    · have hyb : y ≤ {n-1} := by omega","      interval_cases y"]
    for _ in [:n] do lines:=lines++["      · norm_num [G,eval]"]
  return lines

def directSignProof (_f : Poly) (i : ℕ) (cert : SignCertificate) : Lines := Id.run do
  if let some (axis,direction,_sign,g) := cert.dominance then
    let axisPoly := if axis then Y else X
    let xx := if axis then X else scale direction X
    let yy := if axis then scale direction Y else Y
    let high := g.filter fun (i,j,_) => i+j>2
    let lower := norm (g.map fun (i,j,a) => if i+j≤2 then (i,j,a) else
      if i>0 then (2,0,a) else (0,2,a))
    let positive := (positiveSquare lower).getD {}
    let squares := cert.squares.map fun (_,p) => s!"sq_nonneg ({p.expr})"
    let rhs := join " + " ((cert.squares.map fun (a,p) => s!"{a.num} * ({p.expr})^2")++[toString cert.const.num])
    let rest := scale (1/cert.scale) ((cert.squares.foldl (fun z (a,p) => z+scale a (p^2)) [])+c cert.const)
    let mut lines := ["by_contra hn",s!"have hrest : 0 ≤ {rest.expr} := by",
      s!"  have he : {cert.scale.num} * ({rest.expr}) = {rhs} := by ring",
      s!"  nlinarith only [he,{join ", " squares}]",
      s!"have haxis : 0 ≤ {(scale direction axisPoly).expr} := by",
      "  dsimp [H"++toString i++",eval,List.map,List.sum,List.foldr] at hn",
      "  nlinarith only [hn,hrest]"]
    for ((a,b,_),j) in high.zipIdx do
      let base := if a>0 then xx else yy
      let power := a+b
      let hyp := if power%2==0 then "Or.inr (by decide)" else "Or.inl haxis"
      lines:=lines++[s!"have hp{j} := int_sq_le_pow ({base.expr}) {power} (by decide) ({hyp})"]
    let sqs := positive.squares.map fun (_,p) => s!"sq_nonneg ({(subst p xx yy).expr})"
    let lower := subst lower xx yy
    let rhs := join " + " ((positive.squares.map fun (a,p) => s!"{a.num} * ({(subst p xx yy).expr})^2")++[toString positive.const.num])
    lines:=lines++[s!"have hl : 0 < {lower.expr} := by",
      s!"  have he : {positive.scale.num} * ({lower.expr}) = {rhs} := by ring",
      s!"  nlinarith only [he,{join ", " sqs}]",
      "have hf' := hf","dsimp [F,eval,List.map,List.sum,List.foldr] at hf'",
      "nlinarith only [hf',hl,"++join ", " (high.zipIdx.map fun (_,j) => s!"hp{j}")++"]"]
    return lines
  if let some (p,q,s,k) := cert.factors then
    let mut lines := [s!"have he : ({s.num}:ℤ)*eval H{i} x y = {p.expr}*{q.expr}+({k.num}:ℤ) := by norm_polynomial",
      "by_contra hn",s!"have hm : {p.expr}*{q.expr} < 0 := by nlinarith only [he,hn]",
      "rcases mul_neg_iff.mp hm with ⟨hp,hq⟩ | ⟨hp,hq⟩"]
    for co in cert.cones do
      let det := co.x.coeff 1 0*co.y.coeff 0 1-co.x.coeff 0 1*co.y.coeff 1 0
      let u := scale (1/det) (scale (co.y.coeff 0 1) (X-c (co.x.coeff 0 0))-scale (co.x.coeff 0 1) (Y-c (co.y.coeff 0 0)))
      let v := scale (1/det) (scale (co.x.coeff 1 0) (Y-c (co.y.coeff 0 0))-scale (co.y.coeff 1 0) (X-c (co.x.coeff 0 0)))
      let g := subst _f co.x co.y
      lines:=lines++[s!"· let u : ℤ := {u.expr}",s!"  let v : ℤ := {v.expr}",
        "  have hu : 0 ≤ u := by dsimp [u]; omega","  have hv : 0 ≤ v := by dsimp [v]; omega",
        s!"  let G : Coeffs := {g.text}","  have hc : ∀ x y : ℤ, 0 ≤ x → 0 ≤ y → eval G x y ≠ 0 := by"]++indent 4 (coneProof g co.bound)++
        ["  apply hc u v hu hv","  have hid : eval F x y = eval G u v := by norm_polynomial","  rw [← hid,hf]"]
    return lines
  if let some n := cert.upper then
    let k := cert.tail; let b := cert.cutoff; let g := cert.P
    let d := g.coeff 0 3*k-g.coeff 0 2
    let square := scale (g.coeff 1 1) X+c (g.coeff 0 1)-scale (2*d) Y
    let mut lines := ["have hf' := hf", "dsimp [F,eval,List.map,List.sum,List.foldr] at hf'", "by_contra hn",
      s!"have hy : y ≤ {n} := by norm_num [H{i},eval] at hn; omega",
      s!"by_cases hneg : y ≤ -{k}",s!"· have hc : y^3 ≤ -({k}:ℤ)*y^2 := by",
      s!"    nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg y) (show y+{k} ≤ 0 by omega)]",
      s!"  by_cases hx : ({b}:ℤ)^2 ≤ x^2",
      s!"  · have hpow : ({b}:ℤ)^2*x^2 ≤ x^4 := by nlinarith only [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx)]",
      s!"    nlinarith only [hf',hc,hpow,hx,sq_nonneg ({square.expr}),sq_nonneg (x+1),sq_nonneg (x-1)]",
      s!"  · obtain ⟨hx0,hx1⟩ := integer_square_bound x {b-1} (by norm_num only [Nat.cast_ofNat]; norm_num at hx ⊢; omega)",
      "    interval_cases x"]
    for (_,z,p) in cert.slices.filter (·.1) do
      let proof := if p != 0 then sliceProof true z p else
        let arg := -(c k)-Y
        let cone := -(subst g (c z) arg)
        let value := -(subst g (c z) Y)
        let rhs := join " + " (cone.map fun (_,j,a) => s!"{a.num} * ({arg.expr})^{j}")
        [s!"have harg : 0 ≤ {arg.expr} := by omega",
         s!"have hid : {value.expr} = {rhs} := by ring",
         s!"have hpos : 0 < {value.expr} := by rw [hid]; positivity", "nlinarith only [hf',hpos]"]
      lines := lines ++ branch 4 proof
    lines := lines ++ [s!"· have hlo : -{k}+1 ≤ y := by omega", "  interval_cases y"]
    for (_,z,p) in cert.slices.filter (! ·.1) do
      let proof := sliceProof false z p
      lines := lines ++ branch 2 proof
    return lines
  if !cert.linear then
    let rhs := join " + " ((cert.squares.map fun (a,p) => s!"{a.num} * ({p.expr})^2")++[toString cert.const.num])
    let sqs := join ", " (cert.squares.map fun (_,p) => s!"sq_nonneg ({p.expr})")
    let mut lines := [s!"have he : {cert.scale.num} * eval H{i} x y = {rhs} := by norm_polynomial"]
    if cert.const > 0 then return lines ++ [s!"nlinarith [{sqs}]"]
    let some (loX,hiX,loY,hiY) := cert.box | return ["fail \"Missing sign bounds\""]
    lines := lines ++ ["by_contra hn",s!"have hle : eval H{i} x y ≤ 0 := by omega"]
    for ((a,p),j) in cert.squares.zipIdx do
      let bound := Nat.sqrt ((-cert.const/a).floor.toNat)
      lines := lines ++ [s!"have hb{j} := integer_square_bound ({p.expr}) {bound} (by norm_num only [Nat.cast_ofNat]; nlinarith only [he,hle,{sqs}])"]
    return lines ++ [s!"obtain ⟨hx0,hx1⟩ : ({loX}:ℤ) ≤ x ∧ x ≤ ({hiX}) := by omega",
      s!"obtain ⟨hy0,hy1⟩ : ({loY}:ℤ) ≤ y ∧ y ≤ ({hiY}) := by omega",
      "interval_cases x <;> interval_cases y <;> norm_num [F,H"++toString i++",eval] at *"]
  let a := cert.A
  let lin := scale (2*a) Y+cert.B
  let t := cert.T
  let p := cert.P
  let disc := cert.D
  let positive := fun (z : Poly) (direction : ℤ) (bound : ℕ) =>
    let shifted := subst z (scale direction (X+c bound)) Y
    let arg := if direction==1 then X-c bound else -(c bound)-X
    let rhs := join " + " (shifted.map fun (j,_,a) => s!"{a.num} * ({arg.expr})^{j}")
    [s!"have hz : {z.expr} = {rhs} := by ring", "rw [hz]; positivity"]
  let mut lines := [s!"have hd : {(4*a).num} * {t.expr} = ({lin.expr})^2 + {disc.expr} := by ring",
    s!"have he : eval H{i} x y * {t.expr} = {p.expr} := by",
    s!"  linear_combination (norm := norm_polynomial) ({znum cert.scale.num}) * hf",
    s!"have hpd : (0 : ℤ) < {p.expr} ∧ (0 : ℤ) < {disc.expr} := by"]
  -- Prove the two univariate inequalities before using the norm identity once.
  for (direction,bound) in cert.bounds do
    let condition := if direction == 1 then s!"{bound} ≤ x" else s!"x ≤ -{bound}"
    let arg := if direction == 1 then X-c bound else -(c bound)-X
    lines := lines ++ [s!"  by_cases hx : {condition}",s!"  · have harg : 0 ≤ {arg.expr} := by omega", "    constructor"]
    for z in [p,disc] do
      let block := positive z direction bound
      lines := lines ++ branch 4 block
  lines := lines ++ ["  interval_cases x"]
  for jj in [1:cert.bounds[0]!.2+cert.bounds[1]!.2] do
    let xx : ℤ := (jj:ℤ)-cert.bounds[0]!.2
    if let some (_,prime) := cert.exclusions.find? (·.1==xx) then
      lines := lines ++ [s!"  · have hc : ∀ z : ZMod {prime}, eval F ({xx}) z ≠ 0 := by decide",
        s!"    have hfz : eval F (({xx} : ℤ) : ZMod {prime}) (y : ZMod {prime}) = 0 := by",
        "      rw [← cast_eval,hf,Int.cast_zero]", "    exact (hc _ (by simpa using hfz)).elim"]
    else lines := lines ++ ["  · norm_num"]
  return lines ++ [s!"have ht : 0 < {t.expr} := by nlinarith only [hd, hpd.2, sq_nonneg ({lin.expr})]",
    s!"have hprod : 0 < eval H{i} x y * {t.expr} := by rw [he]; exact hpd.1",
    "exact (mul_pos_iff_of_pos_right ht).mp hprod"]

def signProof (f : Poly) (i : ℕ) (cert : SignCertificate) : Lines :=
  if !cert.reflected then directSignProof f i cert else
  let g := subst f X (-Y)
  [s!"have haux : ∀ x y : ℤ, eval ({g.text} : Coeffs) x y = 0 → 0 < eval ({cert.reflectedFactor.text} : Coeffs) x y := by",
   "  intro x y hf",s!"  let F : Coeffs := {g.text}",
   s!"  let H{i} : Coeffs := {cert.reflectedFactor.text}",
   "  change eval F x y = 0 at hf", s!"  change 0 < eval H{i} x y"] ++
  indent 2 (directSignProof g i cert) ++
  [s!"have hz : eval ({g.text} : Coeffs) x (-y) = 0 := by convert hf using 1 <;> norm_polynomial",
   "have hh := haux x (-y) hz", "convert hh using 1 <;> norm_polynomial"]

def membership (ps : List ℕ) (divisor label : String) : Lines :=
  if ps.isEmpty then [s!"exact (hp.not_dvd_one {divisor}).elim"] else
  let primes := ps.eraseDups
  [s!"have {label} : " ++ join " ∨ " (primes.map fun p => s!"p = {p}") ++ " := by",
   s!"  have hm := prime_mem_factors hp {natList ps} (by intro q hq; simp at hq; rcases hq with " ++
     join " | " (List.replicate primes.length "rfl") ++ " <;> norm_num) (by norm_num; exact " ++ divisor ++ ")",
   "  simpa using hm",s!"rcases {label} with " ++ join " | " (List.replicate primes.length "rfl")]

def liftProof (i p : ℕ) (ls : List Lift) : Lines := Id.run do
  let residues := join " ∨ " (ls.map fun r => s!"(a = {r.a} ∧ b = {r.b})")
  let mut lines := [s!"have hc : ∀ a b : ZMod {p}, eval F a b = 0 → eval H{i} a b = 0 → eval T{i} a b = 0 → {residues} := by {finiteTableProof p}",
    s!"have hfz : eval F (x : ZMod {p}) (y : ZMod {p}) = 0 := by rw [← cast_eval,hf,Int.cast_zero]",
    s!"have hhz : eval H{i} (x : ZMod {p}) (y : ZMod {p}) = 0 := by rw [← cast_eval]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hh",
    s!"have htz : eval T{i} (x : ZMod {p}) (y : ZMod {p}) = 0 := by rw [← cast_eval]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ht",
    "have hr := hc _ _ hfz hhz htz"]
  if ls.length > 1 then lines := lines ++ [splitCases "hr" ls.length]
  for r in ls do
    let block := [s!"have hx : x % {p} = {r.a} := (ZMod.intCast_eq_intCast_iff' x {r.a} {p}).mp hr.1",
      s!"have hy : y % {p} = {r.b} := (ZMod.intCast_eq_intCast_iff' y {r.b} {p}).mp hr.2",
      s!"let a : ℤ := (x-{r.a})/{p}",s!"let b : ℤ := (y-{r.b})/{p}",
      s!"have hxa : x = {r.a}+{p}*a := by dsimp [a]; omega",s!"have hyb : y = {r.b}+{p}*b := by dsimp [b]; omega",
      s!"let L : Coeffs := {r.L.text}",s!"let K : Coeffs := {r.K.text}",
      s!"have he : eval F x y = {p} * eval L a b := by rw [hxa,hyb]; norm_polynomial",
      "have hl : eval L a b = 0 := by rw [hf] at he; omega",
      s!"have hrel : eval H{i} x y = {p} * ({p} * eval K a b) + {r.c} * eval F x y := by rw [hxa,hyb]; norm_polynomial",
      s!"have hk : ∀ u v : ZMod {p}, eval L u v = 0 → eval K u v ≠ 0 := by {finiteTableProof p}",
      s!"have hkn : ¬ ({p} : ℤ) ∣ eval K a b := by", "  intro hd",s!"  apply hk (a : ZMod {p}) (b : ZMod {p})",
      "  · rw [← cast_eval,hl,Int.cast_zero]", "  · rw [← cast_eval]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd",
      "have hk0 : eval K a b ≠ 0 := by intro hz; exact hkn (hz ▸ dvd_zero _)",
      s!"letI : Fact (Nat.Prime {p}) := ⟨by decide⟩", "rw [hf,mul_zero,add_zero] at hrel",
      "rw [hrel,padicValInt.mul (by norm_num) (mul_ne_zero (by norm_num) hk0), padicValInt.mul (by norm_num) hk0,padicValInt.eq_zero_of_not_dvd hkn]",
      "norm_num [padicValInt_self]"]
    lines := lines ++ if ls.length>1 then branch 0 block else block
  return lines

def idealProof (i : ℕ) (r : Exceptional) : Lines := Id.run do
  let names := ["F",s!"H{i}",s!"T{i}",s!"U{i}",s!"V{i}"] ++ if r.fermat then ["PX","PY"] else []
  let mut lines := r.ideal.zipIdx.map fun (p,j) => s!"let B{j} : Coeffs := {p.text}"
  if r.fermat then
    lines := lines ++ [s!"let PX : Coeffs := {(X^r.prime-X).text}",s!"let PY : Coeffs := {(Y^r.prime-Y).text}",
      s!"have hxdiv : ({r.prime}:ℤ) ∣ eval PX x y := by simpa [PX,eval,sub_eq_add_neg] using prime_dvd_pow_sub {r.prime} (by norm_num) x",
      s!"have hydiv : ({r.prime}:ℤ) ∣ eval PY x y := by simpa [PY,eval,sub_eq_add_neg] using prime_dvd_pow_sub {r.prime} (by norm_num) y"]
  let lhs := join " + " (names.zipIdx.map fun (n,j) => s!"eval B{j} x y * eval {n} x y")
  let ds := ["hfdiv","hh","ht","hu","hv"] ++ if r.fermat then ["hxdiv","hydiv"] else []
  let hd := ds.tail.foldl (fun proof h => s!"dvd_add ({proof}) (dvd_mul_of_dvd_right {h} _)")
    "dvd_mul_of_dvd_right hfdiv _"
  lines := lines ++ [s!"let R : Coeffs := {r.remainder.text}",s!"have he : {lhs} = 1 + {r.prime} * eval R x y := by",
    "  norm_polynomial",
    s!"have hfdiv : ({r.prime} : ℤ) ∣ eval F x y := by rw [hf]; exact dvd_zero _",
    s!"have hd : ({r.prime} : ℤ) ∣ {lhs} := by",
    "  exact "++hd,
    "rw [he] at hd",s!"have hc : ({r.prime} : ℤ) ∣ 1 := by simpa using dvd_sub hd (dvd_mul_right ({r.prime} : ℤ) (eval R x y))",
    "norm_num at hc"]
  return lines

def normSetup (f : Poly) (rows : List Prepared) (introduce : Bool := true)
    (characters : Bool := true) : Lines := Id.run do
  let mut lines := ["by",s!"  let F : Coeffs := {f.text}"]
  for (r,i) in rows.zipIdx do
    for (name,p) in ["H","U","V","T","M","E","G","A","B"].zip ([r.H,r.U,r.V,r.T,r.M]++r.bezout) do
      lines := lines ++ [s!"  let {name}{i} : Coeffs := {p.text}"]
  lines := lines ++ if introduce then ["  change ∀ x y : ℤ, eval F x y ≠ 0", "  intro x y hf"] else ["  have hf : eval F x y = 0 := hf"]
  for (r,i) in rows.zipIdx do
    let d := r.value
    let ev := fun (n : String) => s!"eval {n}{i} x y"
    lines := lines ++ [s!"  have hid{i} : {ev "H"} * {ev "T"} = ({ev "U"})^2 + ({d}) * ({ev "V"})^2 := by",
      s!"    linear_combination (norm := norm_polynomial) -({ev "M"}) * hf"]
    if r.nonzeroModulus == 0 then
      let proof := if !r.cofactorSign then "clear * - hf" :: signProof f i r.sign else
        [s!"have ht : 0 < {ev "T"} := by",s!"  let H{i} : Coeffs := {r.T.text}",
         s!"  change 0 < eval H{i} x y"] ++ indent 2 (signProof f i r.sign) ++
        [s!"have hn : 0 < ({ev "U"})^2+({d})*({ev "V"})^2 := by",
         s!"  dsimp [U{i},V{i},eval,List.map,List.sum,List.foldr]; positivity",s!"nlinarith only [hid{i},ht,hn]"]
      lines:=lines++[s!"  have hpos{i} : 0 < {ev "H"} := by"]++indent 4 proof++
        [s!"  have hneq{i} : {ev "H"} ≠ 0 := ne_of_gt hpos{i}"]
    else
      let p := r.nonzeroModulus
      lines:=lines++[s!"  have hneq{i} : {ev "H"} ≠ 0 := by", "    intro hz",
        s!"    have hc : ∀ a b : ZMod {p}, eval F a b = 0 → eval H{i} a b ≠ 0 := by {finiteTableProof p}",
        s!"    apply hc (x:ZMod {p}) (y:ZMod {p})", "    · rw [← cast_eval,hf,Int.cast_zero]",
        "    · rw [← cast_eval,hz,Int.cast_zero]"]
    lines := lines ++ [s!"  have hunit{i} : ∀ p : ℕ, p.Prime → jacobiSym ({-d}) p = -1 → (p : ℤ) ∣ {ev "H"} → ¬ (p : ℤ) ∣ {ev "T"} ∨ Even (padicValInt p ({ev "H"})) := by",
      "    intro p hp hj hh",s!"    by_cases ht : (p : ℤ) ∣ {ev "T"}","    swap","    · exact Or.inl ht","    right",
      s!"    have hn : (p : ℤ) ∣ ({ev "U"})^2 + ({d}) * ({ev "V"})^2 := by",
      s!"      rw [← hid{i}]; exact dvd_mul_of_dvd_left hh _",
      s!"    obtain ⟨hu,hv⟩ := inert_divides hp (d := {d}) (by simpa using hj) hn",
      s!"    have hb : {ev "E"} * {ev "U"} + {ev "G"} * {ev "V"} + {ev "A"} * {ev "H"} + {ev "B"} * {ev "T"} = {r.K} := by",
      s!"      norm_polynomial",
      s!"    have hk : (p : ℤ) ∣ ({r.K} : ℤ) := by",
      "      rw [← hb]; exact dvd_add (dvd_add (dvd_add (dvd_mul_of_dvd_right hu _) (dvd_mul_of_dvd_right hv _)) (dvd_mul_of_dvd_right hh _)) (dvd_mul_of_dvd_right ht _)",
      s!"    have hkn : p ∣ {r.K} := by exact_mod_cast hk"] ++ indent 4 (membership r.factors "hkn" "hcases")
    for p in r.factors.eraseDups do
      if let some ex := r.exceptional.find? (·.prime==p) then
        if let some roots := ex.roots then
          lines := lines ++ ["    · exfalso",s!"      let R : List ℕ := {natList roots}",
            s!"      have hxcheck : ∀ a : ZMod {p}, eval U{i} a 0 = 0 → eval V{i} a 0 = 0 → a.val ∈ R := by decide +kernel",
            s!"      have hu0 : eval U{i} (x:ZMod {p}) (y:ZMod {p}) = 0 := by rw [← cast_eval]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hu",
            s!"      have hv0 : eval V{i} (x:ZMod {p}) (y:ZMod {p}) = 0 := by rw [← cast_eval]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hv",
            s!"      have hxR : (x:ZMod {p}).val ∈ R := hxcheck _ (by simpa [U{i},eval] using hu0) (by simpa [V{i},eval] using hv0)",
            s!"      have hc : ∀ a : ZMod {p}, a.val ∈ R → ∀ b : ZMod {p}, eval F a b = 0 → eval H{i} a b = 0 → eval T{i} a b ≠ 0 := by decide +kernel",
            s!"      have hfz : eval F (x:ZMod {p}) (y:ZMod {p}) = 0 := by rw [← cast_eval,hf,Int.cast_zero]",
            s!"      have hhz : eval H{i} (x:ZMod {p}) (y:ZMod {p}) = 0 := by rw [← cast_eval]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hh",
            s!"      apply hc _ hxR _ hfz hhz",
            "      rw [← cast_eval]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ht"]
        else if !ex.lift.isEmpty then
          let proof := liftProof i p ex.lift
          lines := lines ++ ["    · "++proof.head!] ++ indent 6 proof.tail
        else if !ex.ideal.isEmpty then
          lines := lines ++ ["    · exfalso"] ++ indent 6 (idealProof i ex)
        else
          lines := lines ++ ["    · exfalso",
            s!"      have hc : ∀ a b : ZMod {p}, eval F a b = 0 → eval H{i} a b = 0 → eval T{i} a b ≠ 0 := by {finiteTableProof p}",
            s!"      have hfz : eval F (x : ZMod {p}) (y : ZMod {p}) = 0 := by rw [← cast_eval,hf,Int.cast_zero]",
            s!"      have hhz : eval H{i} (x : ZMod {p}) (y : ZMod {p}) = 0 := by",
            "        rw [← cast_eval]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hh",
            s!"      apply hc (x : ZMod {p}) (y : ZMod {p}) hfz hhz",
            "      rw [← cast_eval]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ht"]
      else lines := lines ++ [s!"    · exact ((by norm_num : jacobiSym ({-d}) {p} ≠ -1) hj).elim"]
  if !characters then return lines
  for (r,i) in rows.zipIdx do
    let d := r.value
    let l := if d==7 then 7 else 4*d.natAbs
    let negative := (List.range l).filter fun (n : ℕ) => if d==7 then jacobi (n:ℤ) 7 == -1 else n%2==1 && jacobi (-d) n == -1
    let sym := if d==7 then "jacobiSym (r : ℤ) 7" else s!"jacobiSym ({-d}) r"
    lines := lines ++ [s!"  let J{i} : List ℕ := {natList negative}",
      s!"  have hjtable{i} : ∀ r : ℕ, r ∈ J{i} → {sym} = -1 := by",
      s!"    intro r hr; simp only [J{i},List.mem_cons,List.not_mem_nil,or_false] at hr",
      "    rcases hr with " ++ join " | " (List.replicate negative.length "rfl") ++ " <;> norm_num"]
  return lines

def characterPredicate (rows : List Prepared) (ch : Choice) (r : String) : String :=
  if ch.scale == 0 then s!"({r} % 7 ∈ J{ch.index})" else
  s!"({r} % {ch.scale} = 0 ∧ ({r} / {ch.scale}) % 2 = 1 ∧ (({r} / {ch.scale}) % {4*rows[ch.index]!.value.natAbs}) ∈ J{ch.index})"

def closeCases (rows : List Prepared) (m : ℕ) (cs : List Choice) : Lines := Id.run do
  let many := cs.length > 1
  let mut lines := if many then ["  "++splitCases "hr" cs.length] else []
  for ch in cs do
    let i := ch.index
    let s := ch.scale
    let ev := fun (n : String) => s!"eval {n}{i} x y"
    let hh := ev "H"; let tt := ev "T"; let uu := ev "U"; let vv := ev "V"
    let d := rows[i]!.value
    if s==0 then
      if many then lines := lines ++ ["  · have hj := hr"]
      lines := lines ++ indent (if many then 4 else 2) [s!"have hj' : jacobiSym (({hh}).natAbs : ℤ) 7 = -1 := by",
        "  rw [jacobiSym.mod_left]", "  norm_cast at *",s!"  rw [Nat.mod_mod_of_dvd _ (by norm_num : 7 ∣ {m})] at hr",
        s!"  exact hjtable{i} _ hr",s!"have hc' : jacobiSym (-7) ({hh}).natAbs = -1 := by",
        s!"  rw [jacobi_neg_seven _ (Int.natAbs_ne_zero.mpr (ne_of_gt hpos{i}))]; exact hj'",
        s!"exact norm_factor_contradiction 7 ({hh}) ({tt}) ({uu}) ({vv}) (ne_of_gt hpos{i}) hid{i} hc' hunit{i}"]
      continue
    lines := lines ++ [if many then "  · obtain ⟨hdiv,hodd,hj⟩ := hr" else "  obtain ⟨hdiv,hodd,hj⟩ := hr"]
    let mut block := [s!"have hj' : jacobiSym ({-d}) ((({hh}).natAbs % {m} / {s}) % {4*d.natAbs}) = -1 := by",
      s!"  exact hjtable{i} _ hj",s!"have hdivn : ({s} : ℕ) ∣ ({hh}).natAbs := Nat.dvd_of_mod_eq_zero (by omega)",
      s!"have hs : ({s} : ℤ) ∣ {hh} := (Int.natCast_dvd (m := {s})).mpr hdivn",
      s!"have hchar := jacobi_from_residue ({-d}) ({hh}).natAbs {m} {s} (by norm_num) (by norm_num) hodd hj'",
      s!"have hchars : jacobiSym ({-d}) ({hh} / {s}).natAbs = -1 := by",
      "  simpa [Int.natAbs_ediv_of_dvd hs] using hchar",
      s!"apply scaled_norm_factor_contradiction ({d}) ({hh}) ({tt}) ({uu}) ({vv}) {s} hs (ne_of_gt hpos{i}) hid{i} (by simpa using hchars) (by simpa using hunit{i})",
      "intro p hp hsym hps", "norm_num only [neg_neg] at hsym"]
    if s==1 then block := block ++ ["exact (Int.prime_iff_natAbs_prime.mpr (by simpa using hp)).not_dvd_one hps"]
    else
      let fs := (factors s).toOption.getD []
      block := block ++ [s!"have hpn : p ∣ {s} := by exact_mod_cast hps"] ++ membership fs "hpn" "hsCases"
      block := block ++ fs.eraseDups.map (fun p => s!"· exact (by norm_num : jacobiSym ({-d}) {p} ≠ -1) hsym")
    lines := lines ++ indent (if many then 4 else 2) block
  return lines

def projectedProof (rows : List Prepared) (cover : Cover) (target : ℕ) (projections : List Projection) : Lines := Id.run do
  let hh := s!"(eval H{target} x y).natAbs"
  let mut lines := []
  let mut hyps := []
  for p in projections do
    let q := p.modulus
    lines := lines ++ [s!"  let R{q} : List ℕ := {natList p.allowed}"]
    let mut names := []
    for ch in p.excluded do
      let prop := characterPredicate rows ch s!"((eval H{ch.index} x y).natAbs % {q})"
      let name := s!"hn{q}_{ch.index}_{ch.scale}"
      lines := lines ++ [s!"  have {name} : ¬ {prop} := by", "    intro hr"] ++ indent 2 (closeCases rows q [ch])
      names := names ++ [name]
    let pre := p.excluded.map fun ch => "¬ "++characterPredicate rows ch s!"(eval H{ch.index} a b).val"
    let prop := join " → " (["eval F a b = 0"]++pre++[s!"(eval H{target} a b).val ∈ R{q}"])
    lines := lines ++ [s!"  have hc{q} : ∀ a b : ZMod {q}, {prop} := by {finiteTableProof q}",
      s!"  have hfz{q} : eval F (x : ZMod {q}) (y : ZMod {q}) = 0 := by rw [← cast_eval,hf,Int.cast_zero]",
      s!"  have hl{q} : {hh} % {q} ∈ R{q} := by",s!"    have hc := hc{q} (x : ZMod {q}) (y : ZMod {q}) hfz{q}"]
    for i in (target::p.excluded.map (·.index)).eraseDups do
      lines := lines ++ [s!"    rw [eval_residue_natAbs H{i} x y {q} (le_of_lt hpos{i})] at hc"]
    lines := lines ++ ["    exact hc "++join " " names]
    hyps := hyps ++ [s!"n.val % {q} ∈ R{q}"]
  let preds := cover.choices.map (fun ch => characterPredicate rows ch "n.val")
  lines := lines ++ [s!"  have hc : ∀ n : Fin {cover.modulus}, "++join " → " (hyps++[join " ∨ " preds])++" := by decide +kernel",
    s!"  have hr := hc ⟨{hh} % {cover.modulus}, Nat.mod_lt _ (by decide)⟩"]
  for p in projections do
    lines := lines ++ [s!"  have he{p.modulus} : ({hh} % {cover.modulus}) % {p.modulus} = {hh} % {p.modulus} := Nat.mod_mod_of_dvd _ (by norm_num)"]
  lines := lines ++ ["  dsimp only at hr", "  simp only ["++join ", " (projections.map (fun p => s!"he{p.modulus}"))++"] at hr",
    "  have hr := hr "++join " " (projections.map (fun p => s!"hl{p.modulus}"))]
  return lines ++ closeCases rows cover.modulus cover.choices

def constantProof (f : Poly) (rows : List Prepared) (cover : Cover) : String := Id.run do
  let mut lines := normSetup f rows
  if let some (target,projections) := cover.projection then
    return join "\n" (lines++projectedProof rows cover target projections)
  let m := cover.modulus
  let preds := cover.choices.map (fun ch => characterPredicate rows ch s!"(eval H{ch.index} a b).val")
  lines := lines ++ [s!"  have hc : ∀ a b : ZMod {m}, eval F a b = 0 → "++join " ∨ " preds++s!" := by {finiteTableProof m}",
    s!"  have hfz : eval F (x : ZMod {m}) (y : ZMod {m}) = 0 := by rw [← cast_eval,hf,Int.cast_zero]", "  have hr := hc _ _ hfz"]
  for i in (cover.choices.map (·.index)).eraseDups do
    lines := lines ++ [s!"  have hval{i} : (eval H{i} (x : ZMod {m}) (y : ZMod {m})).val = (eval H{i} x y).natAbs % {m} := by",
      s!"    exact eval_residue_natAbs H{i} x y {m} (le_of_lt hpos{i})",s!"  rw [hval{i}] at hr"]
  return join "\n" (lines++closeCases rows m cover.choices)

structure Pair where
  a : Poly
  b : Poly
  r : Poly
  c : Poly
  t : Poly
  s : Poly
  d : Poly
  v : Poly
  bezout1 : List Poly × ℕ
  bezout2 : List Poly × ℕ
  cross : List Poly × ℕ
  support : List ℕ
  deriving Inhabited

def Pair.get (p : Pair) (key : String) : Poly :=
  match key with
  | "a" => p.a | "b" => p.b | "r" => p.r | "c" => p.c
  | "t" => p.t | "s" => p.s | "d" => p.d | "v" => p.v
  | _ => []

def integerBezout (u v : Poly) (f : Poly := []) : Attempt (List Poly × ℕ) := do
  for axis in [false,true] do
    if let .ok (e,g,z) := gcdex u v axis then
      if z == Poly.c 1 then return clearDenominators [e,g,[]]
  return clearDenominators (← idealOne [u,v,f])

def crossBezout (f a b : Poly) : Attempt (List Poly × ℕ) := do
  for swapped in [false,true] do
    let (a,b) := if swapped then (b,a) else (a,b)
    let attempt : Attempt (List Poly) := do
      let (qf,rf) ← divRem f a true
      let (qb,rb) ← divRem b a true
      let (e,g,z) ← gcdex rf rb
      if z != Poly.c 1 then throw "No constant cross Bezout identity"
      return if swapped then [e,g,-(e*qf)-g*qb] else [e,-(e*qf)-g*qb,g]
    if let .ok ws := attempt then return clearDenominators ws
  return clearDenominators (← idealOne [f,a,b])

def mutualPairs (f : Poly) (data : List Datum) : Attempt (List Pair) := do
  let norms ← data.mapM (normIdentity f)
  let reciprocal := (norms.filter fun r => r.d.constant?.isSome).map fun row =>
    {d:= -row.H,kappa:=1,H:= -row.d,U:=[],V:= -row.d,T:=row.H*row.d,M:=[] : Identity}
  let norms := norms++reciprocal
  let mut pairs := []
  for (one,i) in norms.zipIdx do
    for (two,j) in norms.zipIdx do
      if i ≥ j then continue
      if one.H.isEmpty || two.H.isEmpty then continue
      let c1 := one.d.head!.2.2 / two.H.head!.2.2
      let c2 := two.d.head!.2.2 / one.H.head!.2.2
      if one.d != scale c1 two.H || two.d != scale c2 one.H then continue
      if c1*c2 == 0 || c1.den != 1 || c2.den != 1 then continue
      let a := scale (-c2) one.H
      let b := scale (-c1) two.H
      let r := scale (-c2) one.U
      let cc := scale (-c2) one.V
      let t := scale (-c2) one.T
      let s := scale (-c1) two.U
      let d := scale (-c1) two.V
      let v := scale (-c1) two.T
      let bz1 ← integerBezout r cc f
      let bz2 ← integerBezout s d f
      let cross ← crossBezout f a b
      let support := (← factors (2*bz1.2*bz2.2*cross.2)).eraseDups
      pairs := pairs ++ [⟨a,b,r,cc,t,s,d,v,bz1,bz2,cross,support⟩]
  return pairs

def possibleParts (z p depth : ℕ) : List (ℕ × ℤ) := Id.run do
  let mut z := z%(p^depth)
  if z == 0 then
    return [depth,depth+1].flatMap fun e => (if p==2 then [1,3,5,7] else [1,-1]).map (e,·)
  let mut e := 0
  while z%p == 0 do z:=z/p; e:=e+1
  if p != 2 then return [(e,jacobi z p)]
  let k := min (depth-e) 3
  return ([1,3,5,7] : List ℤ).filter (fun u => u%(2^k) == (z:ℤ)%(2^k)) |>.map (e,·)

def possibleValues (a b p depth : ℕ) (secondDepth : ℕ := depth) : List ℤ :=
  ((possibleParts a p depth).flatMap fun (e,u) => (possibleParts b p secondDepth).map fun (f,v) =>
    if p==2 then
      let sign := ((u-1)/2)*((v-1)/2)+(e:ℤ)*((v*v-1)/8)+(f:ℤ)*((u*u-1)/8)
      if sign%2 == 0 then 1 else -1
    else jacobi (-1) p^(e*f)*u^f*v^e).eraseDups

/-- Constants have known valuations and need no coordinate subdivision. -/
def argumentDepth (h : Poly) (p depth : ℕ) : ℕ := Id.run do
  let some z := h.constant? | return depth
  let mut n := z.num.natAbs
  if n == 0 then return depth
  let mut e := 0
  while n%p == 0 do n:=n/p; e:=e+1
  return max depth (e+(if p==2 then 3 else 1))

def localValues (a b : Poly) (x y p depth : ℕ) : List ℤ :=
  let da := argumentDepth a p depth
  let db := argumentDepth b p depth
  possibleValues (atMod a x y (p^da)) (atMod b x y (p^db)) p da db

def productVectors (options : List (List ℤ)) : List (List ℤ) :=
  options.foldr (fun choices rest => choices.flatMap fun v => rest.map (v::·)) [[]]

abbrev Restriction := ℕ × List (ℕ × ℕ)
structure Leaf where
  a : ℕ
  b : ℕ
  depth : ℕ
  vectors : List (List ℤ)
  deriving Inhabited
structure LocalCover where
  vectors : List (List ℤ)
  leaves : List Leaf
  deriving Inhabited

def localCover (f : Poly) (pairs : List Pair) (p : ℕ)
    (restrictions : List Restriction := []) : Attempt LocalCover := do
  let mut frontier := [(0,0,0)]
  let mut leaves := []
  let mut vectors := []
  for _ in [:20000] do
    let (a,b,depth)::rest := frontier | return ⟨vectors.eraseDups,leaves⟩
    frontier := rest
    let m := p^depth
    if depth>0 && restrictions.any (fun (q,allowed) => m%q==0 && !allowed.contains (a%q,b%q)) then continue
    if depth>0 then
      let options := pairs.map fun pair =>
        let tt := atMod pair.t a b (p^argumentDepth pair.t p depth)
        let vv := atMod pair.v a b (p^argumentDepth pair.v p depth)
        let base := localValues pair.a pair.b a b p depth
        base.filter fun value => (tt==0 || (localValues pair.t pair.b a b p depth).contains value) &&
          (vv==0 || (localValues pair.a pair.v a b p depth).contains value)
      let vs := productVectors options |>.eraseDups
      if (vs.length ≤ 1 && (p != 2 || depth ≥ 4)) || depth ≥ 16 then
        vectors := vectors++vs
        leaves := leaves++[⟨a,b,depth,vs⟩]
        continue
    for u in [:p] do
      for v in [:p] do
        let aa:=a+m*u; let bb:=b+m*v
        if atMod f aa bb (m*p)==0 then frontier := (aa,bb,depth+1)::frontier
  throw "Coupled local subdivision budget exhausted"

def auxiliaryNorms (f : Poly) : List Prepared := Id.run do
  let mut found := []
  for j in [:5] do
    let h := Y+Poly.c ((j:ℤ)-2)
    let .ok (_,remainder) := divRem f h true | continue
    let q := -remainder
    if q.degree false != 4 || q.degree true != 0 then continue
    let aa := q.coeff 4 0
    if aa ≤ 0 then continue
    let root := Nat.sqrt aa.num.toNat
    let kappa : ℚ := if aa.den==1 && root*root==aa.num.toNat then 1 else aa
    let q := scale kappa q
    let a := Nat.sqrt (q.coeff 4 0).num.toNat
    if (q.coeff 4 0).den != 1 || (a*a:ℕ) != (q.coeff 4 0).num.toNat then continue
    let b := q.coeff 3 0/(2*a:ℚ)
    if b.den != 1 then continue
    for jj in [:17] do
      let u := scale a (X^2)+scale b X+Poly.c ((jj:ℤ)-8)
      let rem := q-u^2
      if rem.isEmpty then continue
      let aa := rem.coeff 2 0
      let bb := rem.coeff 1 0
      let cc := rem.coeff 0 0
      let (dd,v) := if aa == 0 && bb == 0 then (cc,Poly.c 1) else
        let r := bb/(2*aa)
        (aa/(r.den*r.den:ℚ), scale r.den X+Poly.c r.num)
      if dd == 0 || dd.den != 1 || rem != scale dd (v^2) then continue
      if kappa.den != 1 then continue
      let row : Datum := ⟨Poly.c dd,kappa.num,h,u,v⟩
      if let .ok row := prepare f row then found := found++[row]
  return found

def reachable (covers : List (ℕ × LocalCover)) (count : ℕ) : List (List ℤ) :=
  covers.foldl (fun values (_,cover) => (values.flatMap fun v => cover.vectors.map (v.zipWith (·*·))).eraseDups)
    [List.replicate count 1]

def restrictionProof (f : Poly) (rows : List Prepared) (q : ℕ) (allowed : List (ℕ × ℕ)) : Lines := Id.run do
  let mut lines := (normSetup f rows false).tail
  let cs := choices rows q
  for ch in cs do
    let prop := characterPredicate rows ch s!"((eval H{ch.index} x y).natAbs % {q})"
    lines := lines ++ [s!"  have hn{ch.index}_{ch.scale} : ¬ {prop} := by", "    intro hr"] ++ indent 2 (closeCases rows q [ch])
  let arr := "["++join ", " (allowed.map fun (a,b) => s!"({a},{b})")++"]"
  let pre := ["eval F a b = 0"]++cs.map (fun ch => "¬ "++characterPredicate rows ch s!"(eval H{ch.index} a b).val")++
    [s!"((a.val:ℤ),(b.val:ℤ)) ∈ ({arr} : List (ℤ × ℤ))"]
  lines := lines ++ [s!"  have hc : ∀ a b : ZMod {q}, "++join " → " pre++s!" := by {finiteTableProof q}",
    s!"  have hz : eval F (x:ZMod {q}) (y:ZMod {q}) = 0 := by rw [← cast_eval,hf,Int.cast_zero]",
    s!"  have hr := hc (x:ZMod {q}) (y:ZMod {q}) hz"]
  for i in (cs.map (·.index)).eraseDups do
    lines := lines ++ [s!"  rw [eval_residue_natAbs H{i} x y {q} (le_of_lt hpos{i})] at hr"]
  return lines ++ ["  have hr := hr "++join " " (cs.map fun ch => s!"hn{ch.index}_{ch.scale}"),
    "  simpa only [ZMod.val_intCast,Nat.cast_ofNat] using hr"]

def localSymbolProof (p depth : ℕ) (first second : String) (ra rb : ℕ)
    (firstNe secondNe : String) (secondDepth : ℕ := depth) : Attempt Lines := do
  let lines := if p==2 then [] else [s!"letI : Fact (Nat.Prime {p}) := ⟨by decide⟩"]
  if p==2 && ((depth≥3 && ra%8==1) || (secondDepth≥3 && rb%8==1)) then
    return lines ++ (if secondDepth≥3 && rb%8==1 then [] else ["rw [twoH_comm]"]) ++ ["exact twoH_unit_square_right _ _ (by omega)"]
  if p != 2 && ((ra%p != 0 && jacobi ra p==1) || (rb%p != 0 && jacobi rb p==1)) then
    let right := rb%p != 0 && jacobi rb p==1
    let side := if right then "right" else "left"
    let ex := if right then second else first
    let residue := (if right then rb else ra)%p
    return lines ++ [s!"apply oddH_of_jacobi_{side}",s!"have hm : ({ex}) % {p} = {residue} := by omega",
      "rw [jacobiSym.mod_left]; norm_num only [Nat.cast_ofNat]; rw [hm]; norm_num"]
  if p != 2 then
    for (side,ex,residue,otherNe) in [("left",first,ra,secondNe),("right",second,rb,firstNe)] do
      if residue==0 then continue
      let mut e:=0; let mut r:=residue
      while r%p==0 do r:=r/p; e:=e+1
      if e%2==0 && jacobi r p==1 then
        let neq := if side=="left" then "hu0 "++otherNe else otherNe++" hu0"
        return lines ++ [s!"let u : ℤ := ({ex})/{p^e}",
          s!"have hu : {ex} = (({p}:ℤ)^{e/2})^2*u := by dsimp [u]; norm_num <;> omega",
          s!"have hm : u % {p} = {r%p} := by dsimp [u]; omega",
          "have hu0 : u ≠ 0 := by intro hz; rw [hz] at hm; norm_num at hm",
          s!"rw [hu,oddH_square_mul_{side} {neq} (by norm_num)]",s!"apply oddH_of_jacobi_{side}",
          "rw [jacobiSym.mod_left]; norm_num only [Nat.cast_ofNat]; rw [hm]; norm_num"]
  let mut lines := lines
  for (label,ex,residue,precision) in [("u",first,ra,depth),("v",second,rb,secondDepth)] do
    if residue==0 then throw "Unresolved zero symbol argument"
    let mut e:=0; let mut r:=residue
    while r%p==0 do r:=r/p; e:=e+1
    let k := if p==2 then min 3 (precision-e) else 1
    let m := p^k
    lines := lines ++ [s!"let {label} : ℤ := ({ex})/{p^e}",
      s!"have h{label} : {ex} = ({p}:ℤ)^{e} * {label} := by dsimp [{label}]; norm_num <;> omega",
      s!"have hm{label} : {label} % {m} = {r%m} := by dsimp [{label}]; omega"]
    if p==2 then lines:=lines++[s!"have ho{label} : Odd {label} := Int.odd_iff.mpr (by omega)"]
    else lines:=lines++[s!"have hn{label} : ¬ ({p}:ℤ) ∣ {label} := by intro hd; have := Int.emod_eq_zero_of_dvd hd; omega",
      s!"have hj{label} : jacobiSym {label} {p} = {jacobi r p} := by rw [jacobiSym.mod_left]; norm_num only [Nat.cast_ofNat]; rw [hm{label}]; norm_num"]
  return lines ++ if p==2 then ["rw [twoH_of_parts hou hov hu hv]", "simp only [twoParts,qr,twoChar]", "split_ifs <;> norm_num <;> omega"]
    else ["rw [oddH_of_parts hnu hnv hu hv]", "norm_num [oddParts,hju,hjv]"]

partial def localTreeNode (f : Poly) (pairs : List Pair) (p : ℕ) (cover : LocalCover)
    (restrictions : List Restriction) (aa bb depth : ℕ) : StateT ℕ Attempt Lines := do
  let idx ← get
  modify (·+1)
  let context := "clear * - " ++ join " " (["hf","hx","hy"] ++
    (pairs.zipIdx.flatMap fun (_,j) => [s!"ha{j}",s!"hb{j}",s!"hid{j}a",s!"hid{j}b"]) ++
    restrictions.map (fun (q,_) => s!"hrestriction{q}"))
  let m := p^depth
  for (q,allowed) in restrictions do
    if m%q==0 && !allowed.contains (aa%q,bb%q) then
      return [s!"have hxq : x % {q} = {aa%q} := by omega",s!"have hyq : y % {q} = {bb%q} := by omega",
        s!"norm_num [hxq,hyq] at hrestriction{q}"]
  if let some leaf := cover.leaves.find? (fun r => r.a==aa && r.b==bb && r.depth==depth) then
    let [values] := leaf.vectors | throw "A terminal local cell needs a singleton vector"
    let mut lines := []
    for (pair,j) in pairs.zipIdx do
      let ev := fun (k : String) => s!"eval P{j}{k} x y"
      let precision := fun k => argumentDepth (pair.get k) p depth
      let residue := fun k => atMod (pair.get k) aa bb (p^precision k)
      let candidates := [("a","b"),("t","b"),("a","v")]
      let good := fun (u,v) =>
        (u=="a" || residue u  !=  0) && (v=="b" || residue v  !=  0) &&
        localValues (pair.get u) (pair.get v) aa bb p depth == [values[j]!]
      let choice := (candidates.find? fun (u,v) => residue u  !=  0 && residue v  !=  0 && good (u,v))
        |>.or (candidates.find? good)
      let some (u,v) := choice | throw "No cofactor proves the local symbol value"
      let sym := if p==2 then "twoH" else s!"oddH {p}"
      lines := lines ++ [s!"have hv{j} : {sym} ({ev "a"}) ({ev "b"}) = {values[j]!} := by"]
      let mut block := []
      for k in [u,v].eraseDups do
        block := block ++ [s!"have hr{k} : {ev k} % {p^precision k} = {residue k} := by"] ++
          if precision k > depth then [s!"  norm_num [P{j}{k},eval]"] else
          [s!"  have he := eval_mod P{j}{k} x y {m}","  norm_num only [Nat.cast_ofNat] at he",
           s!"  rw [he,hx,hy]; norm_num [P{j}{k},eval]"]
      if u=="t" || v=="v" then
        let k := if u=="t" then "t" else "v"
        block := block ++ [s!"have ht0 : {ev k} ≠ 0 := by intro hz; rw [hz] at hr{k}; norm_num at hr{k}"]
        let thm := if p==2 then "twoH_norm_cofactor" else "oddH_norm_cofactor"
        let comm := if p==2 then "twoH_comm" else "oddH_comm"
        if p != 2 then block := block ++ [s!"letI : Fact (Nat.Prime {p}) := ⟨by decide⟩"]
        block := block ++ if u=="t" then [s!"rw [{thm} ha{j} hb{j} ht0 hid{j}a]"] else
          [s!"rw [{comm}]",s!"rw [{thm} hb{j} ha{j} ht0 hid{j}b]",s!"rw [{comm}]"]
      let firstNe := if u=="a" then s!"ha{j}" else "ht0"
      let secondNe := if v=="b" then s!"hb{j}" else "ht0"
      -- Arithmetic in a terminal cell needs only its two residues and units.
      block := block ++ ["clear * - " ++ join " " ([s!"hr{u}",s!"hr{v}",firstNe,secondNe].eraseDups)] ++
        (← localSymbolProof p (precision u) (ev u) (ev v) (residue u) (residue v) firstNe secondNe (precision v))
      lines := lines ++ indent 2 block
    return context :: (lines ++ ["simp ["++join ", " ((List.range pairs.length).map (fun j => s!"hv{j}"))++"]"])
  if depth≥16 then throw "Local proof subdivision budget exceeded"
  let children := (List.range p).flatMap fun a => (List.range p).filterMap fun b =>
    if atMod f (aa+m*a) (bb+m*b) (m*p)==0 then some (a,b) else none
  let ll := scale (1/(m:ℚ)) (subst f (Poly.c aa+scale m X) (Poly.c bb+scale m Y))
  let cond := if children.isEmpty then "False" else join " ∨ " (children.map fun (a,b) => s!"(u = {a} ∧ v = {b})")
  let mut lines := [context,s!"let u{idx} : ℤ := (x-{aa})/{m}",s!"let v{idx} : ℤ := (y-{bb})/{m}",
    s!"have hx' : x = {aa}+{m}*u{idx} := by dsimp [u{idx}]; omega",s!"have hy' : y = {bb}+{m}*v{idx} := by dsimp [v{idx}]; omega",
    s!"let L{idx} : Coeffs := {ll.text}",
    s!"have he : eval F x y = {m}*eval L{idx} u{idx} v{idx} := by rw [hx',hy']; norm_polynomial",
    s!"have hl : eval L{idx} u{idx} v{idx} = 0 := by rw [hf] at he; omega",
    s!"have hc : ∀ u v : ZMod {p}, eval L{idx} u v = 0 → {cond} := by set_option synthInstance.maxSize 100000 in {finiteTableProof p}",
    s!"have hz : eval L{idx} (u{idx}:ZMod {p}) (v{idx}:ZMod {p}) = 0 := by rw [← cast_eval,hl,Int.cast_zero]",
    "have hr := hc _ _ hz"]
  if children.isEmpty then return lines ++ ["exact hr.elim"]
  if children.length>1 then lines := lines ++ [splitCases "hr" children.length]
  for (a,b) in children do
    let block := [s!"have hu : u{idx} % {p} = {a} := (ZMod.intCast_eq_intCast_iff' _ {a} {p}).mp hr.1",
      s!"have hv : v{idx} % {p} = {b} := (ZMod.intCast_eq_intCast_iff' _ {b} {p}).mp hr.2",
      s!"have hx : x % {m*p} = {aa+m*a} := by omega",s!"have hy : y % {m*p} = {bb+m*b} := by omega"] ++
      (← localTreeNode f pairs p cover restrictions (aa+m*a) (bb+m*b) (depth+1))
    lines := lines ++ if children.length>1 then branch 0 block else block
  return lines

/-- Substitute certified residues before evaluating expensive finite predicates. -/
def residueCases (varName hypothesis : String) (p : ℕ) (values : List ℕ)
    (body : ℕ → Lines) : Lines := Id.run do
  let mut lines := [s!"simp only [List.mem_cons,List.not_mem_nil,or_false] at {hypothesis}"]
  if values.length>1 then lines:=lines++[splitCases hypothesis values.length]
  for value in values do
    let proof := [s!"have he : {varName} = ({value}:ZMod {p}) := (ZMod.val_injective {p}) ({hypothesis}.trans (by decide +kernel : {value} = ({value}:ZMod {p}).val))",
      s!"subst {varName}"]++body value
    lines:=lines++if values.length>1 then branch 0 proof else proof
  return lines

/-- Select one sufficient condition before normalizing a ground field expression. -/
def pointProof (pair : Pair) (p x y : ℕ) : Lines := Id.run do
  for (a,b,position) in [(pair.a,pair.b,0),(pair.t,pair.b,1),(pair.a,pair.v,2)] do
    let aa := atMod a x y p; let bb := atMod b x y p
    if (position==1 && aa==0) || (position==2 && bb==0) then continue
    let close := "constructor <;> norm_expand <;> norm_num <;> decide +kernel"
    let square := fun (side : String) (value : ℕ) =>
      let root := ((List.range p).find? fun r => r*r%p==value).getD 0
      [s!"apply residueSplit_square_{side} (r := ({root}:ZMod {p}))",
       "· norm_expand; norm_num <;> decide +kernel", "· norm_expand; norm_num <;> decide +kernel"]
    let proof := if aa != 0 && bb != 0 then ["left; "++close] else
      if aa != 0 && jacobi aa p==1 then square "left" aa else
      if bb != 0 && jacobi bb p==1 then square "right" bb else []
    if proof.isEmpty then continue
    if position==0 then return "left"::proof
    return [if position==1 then "right; left" else "right; right", "constructor",
      "· norm_expand; norm_num <;> decide +kernel"] ++ branch 0 proof
  return ["norm_expand; norm_num [residueSplit] <;> decide +kernel"]

def finitePointProof (f : Poly) (pair : Pair) (p : ℕ) (roots : List ℕ) : Lines :=
  ["intro x hx"]++residueCases "x" "hx" p roots fun a =>
    let ys := (List.range p).filter fun b => atMod f a b p == 0
    ["intro y hf",s!"have hycheck : ∀ z : ZMod {p}, eval F ({a}) z = 0 → z.val ∈ ({natList ys} : List ℕ) := by norm_finite",
     "have hy := hycheck y hf"]++residueCases "y" "hy" p ys (pointProof pair p a)

/-- Project exceptional zero loci to the first coordinate before checking residues. -/
def projectedResidueProof (f : Poly) (pair : Pair) (j p : ℕ) (goal : String) : Option Lines := do
  let ev := fun (k : String) => s!"eval P{j}{k} x y"
  let mut lines := ["intro x y hf"]
  for side in ["a","b"] do
    let (q,r) ← (divRem f (pair.get side) true p).toOption
    if r.isEmpty || r.degree true != 0 then none
    let correction := scale (1/(p:ℚ)) (r-f+q*pair.get side)
    if !correction.integral then none
    let roots := (List.range p).filter fun a => atMod r a 0 p == 0
    lines := lines ++ [s!"by_cases h{side} : {ev side} = 0",
      s!"· let R : Coeffs := {r.text}",s!"  let Q : Coeffs := {q.text}",
      s!"  let M : Coeffs := {correction.text}",
      s!"  have hr : eval R x 0 = 0 := by",
      s!"    have he : eval R x 0 = eval F x y - eval Q x y * {ev side} + ({p}:ZMod {p})*eval M x y := by norm_polynomial",
      s!"    have hp0 : ({p}:ZMod {p}) = 0 := by decide +kernel",
      s!"    simpa [hf,h{side},hp0] using he",
      s!"  have hxcheck : ∀ z : ZMod {p}, eval R z 0 = 0 → z.val ∈ ({natList roots} : List ℕ) := by norm_finite",
      s!"  have hc : ∀ x : ZMod {p}, x.val ∈ ({natList roots} : List ℕ) → ∀ y : ZMod {p}, eval F x y = 0 → {goal} := by"]++
      indent 4 (finitePointProof f pair p roots)++["  exact hc x (hxcheck x hr) y hf"]
  return lines ++ ["exact Or.inl (Or.inl ⟨ha,hb⟩)"]

/-- Share the arithmetic proof across all residue pairs when no lifting is needed. -/
def oddResidueProof (f : Poly) (pairs : List Pair) (p : ℕ) : Lines := Id.run do
  let mut lines := [s!"letI : Fact (Nat.Prime {p}) := ⟨by decide⟩"]
  for (pair,j) in pairs.zipIdx do
    let ev := fun (k : String) => s!"eval P{j}{k} x y"
    let split := fun (a b : String) => s!"residueSplit {p} ({ev a}) ({ev b})"
    lines:=lines++[s!"have hv{j} : oddH {p} ({ev "a"}) ({ev "b"}) = 1 := by"]
    if !pair.support.isEmpty && !pair.support.contains p then
      lines:=lines++[s!"  exact pair_off_support hid{j}a.symm hid{j}b.symm hbez{j}_1 hbez{j}_2 hcross{j} (by norm_num) (by norm_num) (by norm_num)"]
      continue
    let goal := s!"{split "a" "b"} ∨ ({ev "t"} ≠ 0 ∧ {split "t" "b"}) ∨ ({ev "v"} ≠ 0 ∧ {split "a" "v"})"
    let check := if p ≥ 100 then projectedResidueProof f pair j p goal else none
    lines:=lines++[s!"  have hc : ∀ x y : ZMod {p}, eval F x y = 0 → {goal} := by"]++
      indent 4 (check.getD [finiteTableProof p true])++[
      s!"  have hz : eval F (x:ZMod {p}) (y:ZMod {p}) = 0 := by rw [← cast_eval,hf,Int.cast_zero]",
      "  rcases hc _ _ hz with hr | ⟨ht,hr⟩ | ⟨ht,hr⟩",
      "  · rw [← cast_eval,← cast_eval] at hr; exact oddH_residueSplit hr"]
    for side in ["t","v"] do
      lines:=lines++[s!"  · have ht0 : {ev side} ≠ 0 := by",
        "      intro he; rw [← cast_eval,he,Int.cast_zero] at ht; exact ht rfl",
        "    rw [← cast_eval,← cast_eval] at hr"]
      lines:=lines++if side=="t" then
        [s!"    rw [oddH_norm_cofactor ha{j} hb{j} ht0 hid{j}a]", "    exact oddH_residueSplit hr"] else
        [s!"    rw [oddH_comm,oddH_norm_cofactor hb{j} ha{j} ht0 hid{j}b,oddH_comm]",
         "    exact oddH_residueSplit hr"]
  return lines++["simp ["++join ", " (pairs.zipIdx.map fun (_,j) => s!"hv{j}")++"]"]

def localTreeProof (f : Poly) (pairs : List Pair) (p : ℕ) (cover : LocalCover)
    (restrictions : List Restriction := []) : Attempt Lines := do
  let split := fun a b => (a != 0 && b != 0) ||
    (a != 0 && jacobi a p == 1) || (b != 0 && jacobi b p == 1)
  let complete := fun _ : Unit => (List.range p).all fun x => (List.range p).all fun y =>
    atMod f x y p != 0 || pairs.all fun pair =>
      let a := atMod pair.a x y p; let b := atMod pair.b x y p
      let t := atMod pair.t x y p; let v := atMod pair.v x y p
      split a b || (t != 0 && split t b) || (v != 0 && split a v)
  if p != 2 && restrictions.isEmpty && cover.leaves.all (·.depth==1) &&
      cover.vectors == [List.replicate pairs.length 1] && complete () then return oddResidueProof f pairs p
  let (ls,_) ← (localTreeNode f pairs p cover restrictions 0 0 0).run 0
  return ["have hx : x % 1 = 0 := by omega","have hy : y % 1 = 0 := by omega"] ++ ls

/-- A factor may have a certified sign, or only a certified nonzero residue. -/
structure FactorEvidence where
  sign : ℤ := 0
  certificate : SignCertificate := {}
  reflected : Bool := false
  modulus : ℕ := 0
  cofactor : Bool := false
  deriving Inhabited

def factorEvidence (f h : Poly) : Attempt FactorEvidence := do
  for sign in [(1:ℤ),-1] do
    for reflected in [false,true] do
      let yy := if reflected then -Y else Y
      if let .ok certificate := signCertificate (subst f X yy) (scale sign (subst h X yy)) then
        return {sign,certificate,reflected}
  let some modulus := (primesBelow 100).find? (fun p => (List.range p).all fun a =>
    (List.range p).all fun b => atMod f a b p != 0 || atMod h a b p != 0)
    | throw "No sign or nonvanishing certificate for a coupled factor"
  return {modulus}

def factorPositiveProof (f h : Poly) (e : FactorEvidence) : Lines :=
  let yy := if e.reflected then -Y else Y
  let g := subst f X yy
  let k := scale e.sign (subst h X yy)
  [s!"have haux : ∀ x y : ℤ, eval ({g.text} : Coeffs) x y = 0 →",
   s!"    0 < eval ({k.text} : Coeffs) x y := by",
   "  intro x y hf",s!"  let F : Coeffs := {g.text}",s!"  let H0 : Coeffs := {k.text}",
   "  change eval F x y = 0 at hf", "  change 0 < eval H0 x y"] ++
   indent 2 (signProof g 0 e.certificate) ++
   [s!"have hz : eval ({g.text} : Coeffs) x ({yy.expr}) = 0 := by",
    "  convert hf using 1 <;> norm_polynomial",
    s!"have hh := haux x ({yy.expr}) hz",
    "convert hh using 1 <;> norm_polynomial"]

/-- Apply reciprocity to a pair after its finite support and real sign are proved. -/
def globalProof (j : ℕ) (primes : List ℕ) (value : ℤ) (sign : Lines) : Lines :=
  let set := if primes.isEmpty then "∅" else "{"++join ", " (primes.map toString)++"}"
  let primeProof := if primes.isEmpty then "by simp" else
    "by intro p hp; simp only [Finset.mem_insert,Finset.mem_singleton] at hp; rcases hp with "++
    join " | " (List.replicate primes.length "rfl")++" <;> norm_num"
  [s!"  have hglobal{j} := global_except (E := {set}) ({primeProof}) ha{j} hb{j} hoff{j}",
   s!"  have hinf{j} : infinity (eval P{j}a x y) (eval P{j}b x y) = {value} := by"] ++
   indent 4 sign ++ [s!"  rw [hinf{j}] at hglobal{j}",
    s!"  norm_num [Finset.prod_insert,Finset.prod_singleton] at hglobal{j}"]

/-- Prove the local vectors and close their common reciprocity contradiction. -/
def localConclusion (f : Poly) (pairs : List Pair) (covers : List (ℕ × LocalCover))
    (restrictions : List Restriction := []) : Attempt Lines := do
  let mut lines := []
  for (p,cover) in covers do
    let sym := if p==2 then "twoH" else s!"oddH {p}"
    let vector := "["++join ", " ((List.range pairs.length).map fun j => s!"{sym} (eval P{j}a x y) (eval P{j}b x y)")++"]"
    let vectors := "["++join ", " (cover.vectors.map fun v => "["++join ", " (v.map znum)++"]")++"]"
    lines:=lines++[s!"  have hlocal{p} : {vector} ∈ ({vectors} : List (List ℤ)) := by"]++
      indent 4 (← localTreeProof f pairs p cover (if p==2 then restrictions else []))
  lines:=lines++["  clear * - "++join " " ((pairs.zipIdx.map fun (_,j) => s!"hglobal{j}")++covers.map (fun (p,_) => s!"hlocal{p}")),
    "  simp only [List.mem_cons,List.not_mem_nil,or_false,List.cons.injEq,and_true] at "++join " " (covers.map fun (p,_) => s!"hlocal{p}"),"  aesop"]
  return lines

def coupledProof (f : Poly) (data : List Datum) : Attempt String := do
  let pairs ← mutualPairs f data
  if pairs.isEmpty then throw "No mutually dependent norm pair"
  let primes := (pairs.flatMap (·.support)).eraseDups.mergeSort (·≤·)
  if primes.any (·>4096) then throw "Coupled support exceeds the current local budget"
  let evidence ← pairs.mapM fun pair => do
    let mut a ← factorEvidence f pair.a
    let mut b ← factorEvidence f pair.b
    if a.sign == 0 && b.sign < 0 && pair.c.constant?.any (·!=0) then
      if let .ok e := factorEvidence f pair.t then
        if e.sign != 0 then a := {e with cofactor:=true}
    if b.sign == 0 && a.sign < 0 && !a.cofactor && pair.d.constant?.any (·!=0) then
      if let .ok e := factorEvidence f pair.v then
        if e.sign != 0 then b := {e with cofactor:=true}
    return (a,b)
  let infinite ← evidence.mapM fun (a,b) =>
    if a.sign>0 || b.sign>0 then pure (1:ℤ) else
    if a.sign<0 && b.sign<0 then pure (-1:ℤ) else throw "Undetermined real symbol"
  let mut covers ← primes.mapM (fun p => return (p, ← localCover f pairs p))
  let mut extra := []
  let mut restrictions := []
  if (reachable covers pairs.length).contains infinite then
    extra := auxiliaryNorms f
    for q in [4,8,16,32] do
      let cs := choices extra q
      let allowed := (List.range q).flatMap fun a => (List.range q).filterMap fun b =>
        if atMod f a b q==0 && !(cs.any fun ch => ch.mask[atMod extra[ch.index]!.H a b q]!) then some (a,b) else none
      let candidate ← localCover f pairs 2 [(q,allowed)]
      covers := covers.map fun (p,old) => (p,if p==2 then candidate else old)
      if !(reachable covers pairs.length).contains infinite then
        restrictions := [(q,allowed)]
        break
  if (reachable covers pairs.length).contains infinite then throw "Local vectors do not contradict reciprocity"
  let mut lines := ["by",s!"  let F : Coeffs := {f.text}"]
  for (pair,j) in pairs.zipIdx do
    for k in ["a","b","r","c","t","s","d","v"] do
      lines:=lines++[s!"  let P{j}{k} : Coeffs := {(pair.get k).text}"]
    let ws := ["E","G","M1","E2","G2","M2","C0","C1","C2"].zip (pair.bezout1.1++pair.bezout2.1++pair.cross.1)
    for (k,p) in ws do lines:=lines++[s!"  let P{j}{k} : Coeffs := {p.text}"]
  lines:=lines++["  change ∀ x y : ℤ, eval F x y ≠ 0","  intro x y hf"]
  for (q,allowed) in restrictions do
    let arr := "["++join ", " (allowed.map fun (a,b) => s!"({a},{b})")++"]"
    lines:=lines++[s!"  have hrestriction{q} : (x%{q},y%{q}) ∈ ({arr} : List (ℤ × ℤ)) := by"]++indent 2 (restrictionProof f extra q allowed)
  let oddPrimes := primes.filter (· != 2)
  let ee := "{"++join ", " (oddPrimes.map toString)++"}"
  for (pair,j) in pairs.zipIdx do
    let ev := fun (k : String) => s!"eval P{j}{k} x y"
    for (side,e) in [("a",evidence[j]!.1),("b",evidence[j]!.2)] do
      if e.sign != 0 then
        let proof ← if !e.cofactor then pure (factorPositiveProof f (pair.get side) e) else do
          let (other,root,unit,cofactor,otherEvidence) := if side=="a" then
            ("b","r","c","t",evidence[j]!.2) else ("a","s","d","v",evidence[j]!.1)
          let mult ← exactDiv (pair.get side*pair.get cofactor-(pair.get root)^2+pair.get other*(pair.get unit)^2) f true
          pure ([s!"have ht : 0 < ({e.sign}) * {ev cofactor} := by"]++
            indent 2 (factorPositiveProof f (pair.get cofactor) e)++
            [s!"have ho : 0 < (-1:ℤ) * {ev other} := by"]++
            indent 2 (factorPositiveProof f (pair.get other) otherEvidence)++
            [s!"have hid : {ev side}*{ev cofactor} = ({ev root})^2-{ev other}*({ev unit})^2 := by",
             s!"  linear_combination (norm := norm_polynomial) ({mult.expr}) * hf",
             s!"have hunit : {ev unit} = ({(pair.get unit).coeff 0 0}) := by norm_num [P{j}{unit},eval]",
             "rw [hunit] at hid", "norm_num only [Int.reduceNeg,Int.reducePow] at hid",
             s!"change 0 < ({e.sign}) * {ev side}",
             s!"nlinarith only [ht,ho,hid,sq_nonneg ({ev root})]"])
        lines:=lines++[s!"  have hp{j}{side} : 0 < ({e.sign}) * {ev side} := by",
          s!"    change 0 < ({e.sign}) * eval ({(pair.get side).text} : Coeffs) x y"]++
          indent 4 proof++
          [s!"  have hsign{j}{side} : {ev side} {if e.sign<0 then "<" else ">"} 0 := by nlinarith only [hp{j}{side}]",
           s!"  have h{side}{j} : {ev side} ≠ 0 := ne_of_{if e.sign<0 then "lt" else "gt"} hsign{j}{side}"]
      else
        let p := e.modulus
        lines:=lines++[s!"  have h{side}{j} : {ev side} ≠ 0 := by",
          s!"    have hc : ∀ a b : ZMod {p}, eval F a b = 0 → eval P{j}{side} a b ≠ 0 := by {finiteTableProof p}",
          "    intro hz",s!"    apply hc (x:ZMod {p}) (y:ZMod {p})",
          "    · rw [← cast_eval,hf,Int.cast_zero]","    · rw [← cast_eval,hz,Int.cast_zero]"]
    for (a,b,r,cc,t) in [("a","b","r","c","t"),("b","a","s","d","v")] do
      let mult ← exactDiv (pair.get a*pair.get t-(pair.get r)^2+pair.get b*(pair.get cc)^2) f true
      lines:=lines++[s!"  let M{j}{a} : Coeffs := {mult.text}",
        s!"  have hid{j}{a} : {ev a} * {ev t} = ({ev r})^2 - {ev b} * ({ev cc})^2 := by",
        s!"    linear_combination (norm := norm_polynomial) (eval M{j}{a} x y) * hf"]
    let k1:=pair.bezout1.2; let k2:=pair.bezout2.2; let k3:=pair.cross.2
    for (suffix,r,cc,e,g,k) in [("1","r","c","E","G",k1),("2","s","d","E2","G2",k2)] do
      lines:=lines++[s!"  have hbez{j}_{suffix} : {ev e}*{ev r} + {ev g}*{ev cc} = {k} := by",
        s!"    linear_combination (norm := norm_polynomial) -({ev ("M"++suffix)}) * hf"]
    lines:=lines++[s!"  have hcross{j} : {ev "C1"}*{ev "a"} + {ev "C2"}*{ev "b"} = {k3} := by",
      s!"    linear_combination (norm := norm_polynomial) -({ev "C0"}) * hf",
      s!"  have hoff{j} : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ ({ee} : Finset ℕ) → oddH p ({ev "a"}) ({ev "b"}) = 1 := by",
      "    intro p hp hp2 hpE","    letI : Fact p.Prime := ⟨hp⟩",
      s!"    have hk : ¬ (p:ℤ) ∣ {k1*k2*k3} := by","      intro hd",s!"      have hdn : p ∣ {k1*k2*k3} := by exact_mod_cast hd"]
    let mem := membership (← factors (k1*k2*k3)) "hdn" "hcases"
    lines:=lines++indent 6 (mem.take (mem.length-1)++["simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hpE; omega"])
    lines:=lines++[s!"    apply pair_off_support hid{j}a.symm hid{j}b.symm hbez{j}_1 hbez{j}_2 hcross{j}"]
    for k in [k1,k2,k3] do lines:=lines++[s!"    · intro hd; exact hk (dvd_trans hd (by norm_num : ({k}:ℤ) ∣ {k1*k2*k3}))"]
    let sign := if infinite[j]! == -1 then [s!"exact if_pos ⟨hsign{j}a,hsign{j}b⟩"] else
      [s!"simp [infinity,not_lt_of_ge (le_of_lt hsign{j}{if evidence[j]!.1.sign>0 then "a" else "b"})]"]
    lines := lines ++ globalProof j oddPrimes infinite[j]! sign
  lines := lines ++ (← localConclusion f pairs covers restrictions)
  return join "\n" lines

/-- Regard a constant-field norm as a Hilbert-symbol pair, keeping its cofactor. -/
def constantPair (r : Prepared) : Pair :=
  let b := Poly.c (-r.value)
  {a:=r.H,b,r:=r.U,c:=r.V,t:=r.T,s:=[],d:=b,v:=-(r.H*b),
   bezout1:=([],1),bezout2:=([],1),cross:=([],1),support:=[]}

/-- Preserve joint local symbol vectors instead of projecting each factor separately. -/
def constantReciprocity (f : Poly) (rows : List Prepared) (limit : ℕ := 4096) : Attempt String := do
  if rows.isEmpty then throw "No prepared constant norm"
  let pairs := rows.map constantPair
  let primes := (2::(← rows.flatMapM fun r => factors r.value.natAbs)).eraseDups.mergeSort (·≤·)
  if primes.any (·>100) then throw "Local prime budget exceeded"
  let covers ← primes.mapM fun p => return (p,← localCover f pairs p)
  if covers.any (fun (p,cover) => cover.leaves.any (fun cell => p^cell.depth > limit)) then
    throw "Local modulus budget exceeded"
  if (reachable covers pairs.length).contains (List.replicate rows.length 1) then
    throw "Joint local vectors do not yet contradict reciprocity"
  let oddPrimes := primes.filter (·!=2)
  let ee := if oddPrimes.isEmpty then "∅" else "{"++join ", " (oddPrimes.map toString)++"}"
  let mut lines := normSetup f rows true false
  for (pair,j) in pairs.zipIdx do
    let row := rows[j]!
    let ev := fun k => s!"eval P{j}{k} x y"
    for k in ["a","b","r","c","t","s","d","v"] do
      lines:=lines++[s!"  let P{j}{k} : Coeffs := {(pair.get k).text}"]
    lines:=lines++[s!"  have ha{j} : {ev "a"} ≠ 0 := hneq{j}",
      s!"  have hb{j} : {ev "b"} ≠ 0 := by norm_num [P{j}b,eval]",
      s!"  have hid{j}a : {ev "a"}*{ev "t"} = ({ev "r"})^2-{ev "b"}*({ev "c"})^2 := by",
      s!"    convert hid{j} using 1 <;> norm_polynomial",
      s!"  have hid{j}b : {ev "b"}*{ev "v"} = ({ev "s"})^2-{ev "a"}*({ev "d"})^2 := by",
      s!"    norm_polynomial",
      s!"  have hoff{j} : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ ({ee}:Finset ℕ) → oddH p ({ev "a"}) ({ev "b"}) = 1 := by",
      "    intro p hp hp2 hpE", "    letI : Fact p.Prime := ⟨hp⟩",
      s!"    have hd : ¬ (p:ℤ) ∣ ({-row.value}:ℤ) := by", "      intro hd",
      "      norm_num only [Int.dvd_neg,neg_neg] at hd",
      s!"      have hdn : p ∣ {row.value.natAbs} := by exact_mod_cast hd"]
    let fs ← factors row.value.natAbs
    let mem := membership fs "hdn" "hpCases"
    lines:=lines++indent 6 (if fs.isEmpty then mem else mem.take (mem.length-1)++
      ["try simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hpE", "omega"])
    lines:=lines++[s!"    simpa [P{j}a,P{j}b,H{j},eval] using norm_factor_symbol hd hneq{j} hid{j} hunit{j}"]
    let sign := if row.value<0 then [s!"norm_num [infinity,P{j}b,eval]"] else
      [s!"exact if_neg (fun h => (not_lt_of_gt hpos{j}) h.1)"]
    lines := lines ++ globalProof j oddPrimes 1 sign
  lines := lines ++ (← localConclusion f pairs covers)
  return join "\n" lines

open Lean Meta Elab Tactic

/-- Reify ordinary integer expressions; `ring` checks the resulting interpretation. -/
partial def readPoly (e x y : Expr) (definitions : Option (IO.Ref (List Name)) := none) : TermElabM Poly := do
  let e := (← instantiateMVars e).headBeta
  let remember := fun name => do
    if let some ref := definitions then
      ref.modify fun names => if names.contains name then names else name::names
  if e.isConst then
    if let some name := e.constName? then remember name
  if e == x then return Poly.X
  if e == y then return Poly.Y
  if !e.hasFVar then
    if let some n ← getIntValue? e then return Poly.c n
  let args := e.getAppArgs
  let name := e.getAppFn.constName?
  if args.size == 1 && [``Int.ofNat,``Int.negSucc].any (some · == name) then
    let some n ← getNatValue? args[0]! | throwError "Expected an integer constant"
    return Poly.c (if name == some ``Int.ofNat then (n:ℤ) else -(n+1:ℤ))
  if args.size ≥ 2 then
    let a := args[args.size-2]!
    let b := args[args.size-1]!
    if [``HAdd.hAdd,``Add.add,``Int.add].any (some · == name) then
      return (← readPoly a x y definitions)+(← readPoly b x y definitions)
    if [``HSub.hSub,``Sub.sub,``Int.sub].any (some · == name) then
      return (← readPoly a x y definitions)-(← readPoly b x y definitions)
    if [``HMul.hMul,``Mul.mul,``Int.mul].any (some · == name) then
      return (← readPoly a x y definitions)*(← readPoly b x y definitions)
    if [``HPow.hPow,``Pow.pow].any (some · == name) then
      let some n ← getNatValue? b | throwError "Expected a natural-number exponent"
      if n > 64 then throwError "Polynomial degree budget exceeded"
      return (← readPoly a x y definitions)^n
  if args.size ≥ 1 && [``Neg.neg,``Int.neg].any (some · == name) then
    return -(← readPoly args.back! x y definitions)
  if let some e' ← unfoldDefinition? e true then
    if let some name := e.getAppFn.constName? then remember name
    return ← readPoly e' x y definitions
  let reduced ← withConfig (fun cfg => {cfg with proj := .yesWithDelta}) (whnfCore e)
  if reduced != e then return ← readPoly reduced x y definitions
  throwError "Expected an integer polynomial, got {e}"

def readValue (value x y : Expr) (definitions : Option (IO.Ref (List Name)) := none) : TermElabM Poly := do
  let mut e := value
  for arg in [x,y] do
    if (← whnf (← inferType e)).isForall then e := (mkApp (← whnf e) arg).headBeta
  unless ← isDefEq (← inferType e) (mkConst ``Int) do
    throwError "Expected ℤ, ℤ → ℤ, or ℤ → ℤ → ℤ"
  readPoly e x y definitions

/-- Read tuple fields after unfolding definitions and the optional `cert` adapter. -/
def readRow (row x y : Expr) : TermElabM Datum := do
  let mut tail := row
  let mut fields := #[]
  for _ in [:4] do
    let e ← whnf tail
    unless e.isAppOfArity ``Prod.mk 4 do
      throwError "Expected a certificate tuple (d, kappa, H, U, V)"
    fields := fields.push e.getAppArgs[2]!
    tail := e.getAppArgs[3]!
  let kp ← readValue fields[1]! x y
  let some k := kp.constant? | throwError "kappa must be an integer constant"
  return {
    d := (← readValue fields[0]! x y), kappa := k.num,
    H := (← readValue fields[2]! x y), U := (← readValue fields[3]! x y),
    V := (← readValue tail x y) }

partial def readRows (value x y : Expr) : TermElabM (List Datum) := do
  let e ← whnf value
  if e.isAppOfArity ``List.nil 1 then return []
  if e.isAppOfArity ``List.cons 3 then
    return (← readRow e.getAppArgs[1]! x y) :: (← readRows e.getAppArgs[2]! x y)
  throwError "Expected a reducible list of certificate tuples"

def generateConstant (f : Poly) (data : List Datum) (limit : ℕ := 4096) : Attempt String := do
  let mut rows := []
  let mut signed := []
  let mut reasons := []
  for (r,i) in data.zipIdx do
    let row ← match prepare f r with
      | .ok row => pure row
      | .error e => do
          reasons := reasons++[s!"certificate {i+1}: {e}"]
          if r.d.constant?.any (·<0) then
            if let .ok row := prepare f r true then signed := signed++[row]
          continue
    signed := signed++[row]
    if let some cover := characterCover f [row] limit then return constantProof f [row] cover
    rows := rows ++ [row]
  if rows.length > 1 then
    if let some cover := characterCover f rows limit then return constantProof f rows cover
  if let .ok proof := constantReciprocity f signed limit then return proof
  -- Simple linear sections can supply extra norm restrictions directly from the input polynomial.
  if !signed.isEmpty then
    for extra in auxiliaryNorms f do
      let enriched := signed++[extra]
      if let .ok proof := constantReciprocity f enriched limit then return proof
  let stage := if rows.isEmpty then "no certificate completed preparation" else
    s!"modular cover incomplete up to modulus {limit} ({rows.length}/{data.length} certificates prepared)"
  throw ("unknown: "++join "; " (stage::reasons))

syntax (name := normTactic) "quadratic_norm " term " using " term (" max_modulus " num)? : tactic

@[tactic normTactic] def elabNormTactic : Tactic := fun stx =>
    withOptions (fun o => (o.set `linter.unusedSimpArgs false).set `synthInstance.maxSize
      (max 4096 (o.get `synthInstance.maxSize (128:ℕ)))) <| withMainContext do
  let `(tactic| quadratic_norm $f using $rows $[max_modulus $limit:num]?) := stx | throwUnsupportedSyntax
  let limit := (limit.map (·.getNat)).getD 4096
  evalTactic (← `(tactic| change ¬ ∃ x y : ℤ, $f x y = 0))
  let definitions ← IO.mkRef ([] : List Name)
  let (fp,data) ← withLocalDeclD `x (mkConst ``Int) fun x =>
    withLocalDeclD `y (mkConst ``Int) fun y => do
      let fp ← readValue (← Term.elabTermAndSynthesize f none) x y (some definitions)
      let data ← match rows with
        -- Elaborate literal rows separately to preserve support for different input types.
        | `(term| [$items,*]) => items.getElems.toList.mapM fun row => do
            readRow (← Term.elabTermAndSynthesize row none) x y
        | _ => readRows (← Term.elabTermAndSynthesize rows none) x y
      return (fp,data)
  let proof ← match generateConstant fp data limit with
    | .ok p => pure p
    | .error e =>
      if data.any (fun r => r.d.constant?.isNone) then
        match coupledProof fp data with
        | .ok p => pure p
        | .error reason => throwError "unknown: {reason}"
      else throwError "{e}"
  let parse := fun (text : String) => do
    match Parser.runParserCategory (← getEnv) `term text with
    | .ok stx => pure (⟨stx⟩ : TSyntax `term)
    | .error e => throwError "{e}"
  let coeffs ← parse fp.text
  let proof ← parse ("open QuadraticNorm RatHilbert in "++proof)
  let unfoldF ← `(Parser.Tactic.simpLemma| $f:term)
  let extra ← (← definitions.get).toArray.mapM fun name =>
    `(Parser.Tactic.simpLemma| $(mkIdent name):term)
  let unfolds := #[unfoldF]++extra
  evalTactic (← `(tactic| exact (by
    have hnorm : QuadraticNorm.NoIntZero $coeffs := $proof
    rintro ⟨x,y,hxy⟩
    apply hnorm x y
    convert hxy using 1 <;> dsimp [QuadraticNorm.eval, $unfolds,*, List.map, List.sum, List.foldr] <;> ring)))

end QuadraticNorm.Search




namespace OriginalEquation
def f (x y : ℤ) : ℤ := -x^4 + x*y - 2*x + 2*y^3 + 1
def d0 : ℤ := 1
def kappa0 : ℤ := 8192
def H0 (x y : ℤ) : ℤ := 4*x^2 - 2*x + 2*y + 5
def U0 (x : ℤ) : ℤ := 1024*x^3 - 768*x^2 + 1536*x
def V0 (x : ℤ) : ℤ := -1024*x^2 + 768*x - 1408
def cert_list := [
  QuadraticNorm.cert d0 kappa0 H0 U0 V0
]
without_editor_info theorem no_integer_solutions : ¬ ∃ x y : ℤ, f x y = 0 := by
  quadratic_norm f using cert_list
end OriginalEquation


                                      
theorem E65786409_2 : ¬ ∃ x y : ℤ, x^4 + x*y + 2*x + 2*y^3 - 1 = 0 := by
  rintro ⟨x, y, h⟩
  apply OriginalEquation.no_integer_solutions
  refine ⟨x, -y, ?_⟩
  dsimp [OriginalEquation.f]
  linear_combination (-1 : ℤ) * h

#print axioms E65786409_2
