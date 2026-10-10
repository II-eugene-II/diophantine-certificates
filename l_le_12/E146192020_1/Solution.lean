import Lean.Elab.Command
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity

set_option maxHeartbeats 0
set_option maxRecDepth 100000

                                      
                                                                      
                                                                       

set_option Elab.async false
set_option linter.all false
elab "without_editor_info " c:command : command =>
  Lean.Elab.withEnableInfoTree false (Lean.Elab.Command.elabCommand c)

                                     
/-! Input data for graph certificates. Polynomial and arithmetic witnesses are
checked by the corresponding backend; a well-formed matrix is not a proof. -/

namespace GraphCert

abbrev Polynomial := ℤ → ℤ → ℤ
abbrev Pair := ℤ × ℤ

inductive BaseField where
  | rational
  | eisenstein
  | gaussian
  deriving DecidableEq, Repr

/-- A vertex, its constant, and a numerator/denominator for its power root.
The parameter is optional for the usual chart whose free coordinate is x. -/
structure VertexData where
  re : Polynomial
  im : Polynomial
  constant : Pair
  rootNumerator : ℤ → Pair
  rootDenominator : ℕ
  parameter : ℤ → ℤ → Pair := fun x _ => (x, 0)

/-- The graph carries and validates the power; vertex data are independent of it. -/
abbrev Vertex (_power : ℕ) := VertexData

/-- Constructor with an optional chart parameter. -/
def vertex (re im : Polynomial) (constant : Pair) (rootNumerator : ℤ → Pair)
    (rootDenominator : ℕ) (parameter : ℤ → ℤ → Pair := fun x _ => (x, 0)) : VertexData :=
  ⟨re, im, constant, rootNumerator, rootDenominator, parameter⟩

/-- The complete matrix is supplied. Its lower triangle is the negative of
the upper triangle modulo the power, rather than a second set of edges. -/
structure Graph where
  field : BaseField
  power : ℕ
  vertices : List (Vertex power)
  weights : List String

def rational (H : List (Vertex 2)) (weights : List String) : Graph :=
  ⟨.rational, 2, H, weights⟩

def eisenstein (power : ℕ) (H : List (Vertex power))
    (weights : List String) : Graph :=
  ⟨.eisenstein, power, H, weights⟩

def gaussian (H : List (Vertex 4)) (weights : List String) : Graph :=
  ⟨.gaussian, 4, H, weights⟩

namespace Matrix

def digit (c : Char) : Except String ℕ :=
  if c == '.' then .ok 0
  else if '0' ≤ c && c ≤ '9' then .ok (c.toNat - '0'.toNat)
  else .error s!"Invalid matrix character: {c}"

def parse (power size : ℕ) (rows : List String) : Except String (Array (Array ℕ)) := do
  if power < 2 then throw "The power must be at least two"
  if rows.length != size then throw "The matrix height must equal the vertex count"
  let matrix ← rows.toArray.mapM fun row => do
    let entries ← row.toList.toArray.mapM digit
    if entries.size != size then throw "The matrix width must equal the vertex count"
    if entries.any (· ≥ power) then throw "A matrix weight is outside the residue range"
    return entries
  for i in [:size] do
    if (matrix[i]!)[i]! != 0 then throw "The matrix diagonal must be zero"
    for j in [i+1:size] do
      if ((matrix[i]!)[j]! + (matrix[j]!)[i]!) % power != 0 then
        throw s!"The matrix is not skew-symmetric at ({i}, {j})"
  return matrix

structure Edge where
  src : ℕ
  dst : ℕ
  weight : ℕ
  deriving DecidableEq, Repr

/-- Compile the upper triangle once; subsequent arithmetic uses sparse edges. -/
def edges (matrix : Array (Array ℕ)) : Array Edge := Id.run do
  let mut result := #[]
  for i in [:matrix.size] do
    for j in [i+1:matrix.size] do
      let weight := (matrix[i]!)[j]!
      if weight != 0 then result := result.push ⟨i, j, weight⟩
  return result

end Matrix

/-- Check data shape only. This deliberately returns no mathematical theorem. -/
def Graph.validate (g : Graph) : Except String (Array Matrix.Edge) := do
  match g.field, g.power with
  | .rational, 2 | .eisenstein, 2 | .eisenstein, 3 | .gaussian, 4 => pure ()
  | _, _ => throw "This base field and power are not supported"
  for v in g.vertices do
    if v.rootDenominator == 0 then throw "A root denominator must be positive"
    if v.constant == (0, 0) then throw "A vertex constant must be nonzero"
  return Matrix.edges (← Matrix.parse g.power g.vertices.length g.weights)

end GraphCert

                                                
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

                                        
                                                            
                                                      

namespace QuadraticNorm

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
private lemma privateNormBase_eq_of_mul_eq_one {a b : ℤ} (h : a * b = 1) (hb : b ^ 2 = 1) : a = b := by
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
  apply privateNormBase_eq_of_mul_eq_one ?_ (infinity_sq a b)
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
  exact privateNormBase_eq_of_mul_eq_one hn (twoH_sq t b)

theorem oddH_norm_cofactor {p : ℕ} [Fact p.Prime] {a b t r c : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0)
    (hid : a*t = r^2 - b*c^2) : oddH p a b = oddH p t b := by
  have hn := oddH_norm (p := p) (mul_ne_zero ha ht) hb hid
  rw [oddH_mul_left ha ht] at hn
  exact privateNormBase_eq_of_mul_eq_one hn (oddH_sq t b ht hb)

end RatHilbert

                                              
                                                                                    

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

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩


private lemma privateNormAutomation_eq_of_mul_eq_one {a b : ℤ} (h : a * b = 1) (hb : b ^ 2 = 1) : a = b := by
  rcases sq_eq_one_iff.mp hb with rfl | rfl <;> linarith


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

namespace QuadraticNorm.Search


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
  return lines ++ [s!"have ht : 0 < {t.expr} := by",
    s!"  have hsum := add_pos_of_nonneg_of_pos (sq_nonneg ({lin.expr})) hpd.2",
    "  rw [← hd] at hsum",
    "  exact (mul_pos_iff_of_pos_left (by norm_num)).mp hsum",
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


end QuadraticNorm.Search

                                             
namespace GraphCert.Auto
open Lean Meta Elab QuadraticNorm.Search QuadraticNorm.Search.Poly

/-- Reuse the norm checker's general polynomial sign search. Its output is
ordinary proof text, checked again when the graph certificate is elaborated. -/
def rationalSigns (f : Expr) (vertices : List Expr) (x y : Expr) : TermElabM Json := do
  let fp ← readValue f x y
  let mut result := #[]
  for v in vertices do
    let h ← readValue (← mkAppM ``VertexData.re #[v]) x y
    let mut entry := Json.null
    for s in [1, -1] do
      if let .ok certificate := signCertificate fp (scale s h) then
        let lines := [s!"let F : QuadraticNorm.Coeffs := {fp.text}",
          s!"let H0 : QuadraticNorm.Coeffs := {(scale s h).text}",
          "have hf : QuadraticNorm.eval F x y = 0 := by convert hf using 1 <;> norm_polynomial",
          "have hs : 0 < QuadraticNorm.eval H0 x y := by"] ++
          indent 2 (signProof fp 0 certificate) ++
          ["convert hs using 1 <;> norm_polynomial"]
        entry := Json.mkObj [("sign", toJson s.num), ("proof", toJson (join "\n" lines))]
        break
    result := result.push entry
  return Json.arr result

end GraphCert.Auto

                                         
/- Rational quadratic graph reciprocity. Graphs contain arbitrary integer
   symbol arguments; polynomial evaluation belongs to the input certificate. -/
namespace GraphCert.Quadratic

open RatHilbert

abbrev Arguments := List (ℤ × ℤ)

def value (symbol : ℤ → ℤ → ℤ) (arguments : Arguments) : ℤ :=
  (arguments.map fun pair => symbol pair.1 pair.2).prod

def Nonzero (arguments : Arguments) : Prop :=
  ∀ pair ∈ arguments, pair.1 ≠ 0 ∧ pair.2 ≠ 0

lemma value_congr {f g : ℤ → ℤ → ℤ} (arguments : Arguments)
    (h : ∀ pair ∈ arguments, f pair.1 pair.2 = g pair.1 pair.2) :
    value f arguments = value g arguments := by
  unfold value
  congr 1
  exact List.map_congr_left h

lemma value_mul (f g : ℤ → ℤ → ℤ) (arguments : Arguments) :
    value (fun a b => f a b * g a b) arguments =
      value f arguments * value g arguments := by
  induction arguments with
  | nil => simp [value]
  | cons pair rest ih =>
    simp only [value, List.map_cons, List.prod_cons] at *
    rw [ih]
    ring

lemma value_prod (S : Finset ℕ) (f : ℕ → ℤ → ℤ → ℤ)
    (arguments : Arguments) :
    value (fun a b => ∏ p ∈ S, f p a b) arguments =
      ∏ p ∈ S, value (f p) arguments := by
  induction S using Finset.induction_on with
  | empty => simp [value]
  | @insert p S hp ih =>
    simp only [Finset.prod_insert hp]
    rw [value_mul, ih]

lemma value_sq (f : ℤ → ℤ → ℤ) (arguments : Arguments)
    (hf : ∀ pair ∈ arguments, f pair.1 pair.2 ^ 2 = 1) :
    value f arguments ^ 2 = 1 := by
  induction arguments with
  | nil => simp [value]
  | cons pair rest ih =>
    change (f pair.1 pair.2 * value f rest) ^ 2 = 1
    rw [mul_pow]
    rw [hf pair (by simp), ih (fun q hq => hf q (by simp [hq])), one_mul]

lemma value_odd_sq {p : ℕ} [Fact p.Prime] (arguments : Arguments)
    (hn : Nonzero arguments) : value (oddH p) arguments ^ 2 = 1 :=
  value_sq (oddH p) arguments (fun pair h => oddH_sq _ _ (hn pair h).1 (hn pair h).2)

theorem global_except (arguments : Arguments) {E : Finset ℕ}
    (hE : ∀ p ∈ E, p.Prime ∧ p ≠ 2) (hn : Nonzero arguments)
    (hoff : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ E →
      value (oddH p) arguments = 1) :
    value twoH arguments * (∏ p ∈ E, value (oddH p) arguments) =
      value infinity arguments := by
  let support (pair : ℤ × ℤ) :=
    (pair.1.natAbs.primeFactors ∪ pair.2.natAbs.primeFactors).erase 2
  let S := E ∪ arguments.toFinset.biUnion support
  have hES : E ⊆ S := Finset.subset_union_left
  have hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2 := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hE p hp
    rcases Finset.mem_biUnion.mp hp with ⟨pair, _, hp⟩
    rcases Finset.mem_erase.mp hp with ⟨hp2, hp⟩
    rcases Finset.mem_union.mp hp with hp | hp
    · exact ⟨(Nat.mem_primeFactors.mp hp).1, hp2⟩
    · exact ⟨(Nat.mem_primeFactors.mp hp).1, hp2⟩
  have hs (pair : ℤ × ℤ) (hpair : pair ∈ arguments) :
      Supported S pair.1 ∧ Supported S pair.2 := by
    have mem {p : ℕ} (hp2 : p ≠ 2)
        (hp : p ∈ pair.1.natAbs.primeFactors ∪ pair.2.natAbs.primeFactors) : p ∈ S :=
      Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨pair, List.mem_toFinset.mpr hpair, Finset.mem_erase.mpr ⟨hp2, hp⟩⟩)
    constructor
    · intro p hp hd
      by_cases hp2 : p = 2
      · exact Or.inl hp2
      exact Or.inr (mem hp2 (Finset.mem_union_left _
        (Nat.mem_primeFactors.mpr ⟨hp, hd, Int.natAbs_ne_zero.mpr (hn pair hpair).1⟩)))
    · intro p hp hd
      by_cases hp2 : p = 2
      · exact Or.inl hp2
      exact Or.inr (mem hp2 (Finset.mem_union_right _
        (Nat.mem_primeFactors.mpr ⟨hp, hd, Int.natAbs_ne_zero.mpr (hn pair hpair).2⟩)))
  have ht : value (total S) arguments = 1 := by
    apply List.prod_eq_one
    intro a ha
    rcases List.mem_map.mp ha with ⟨pair, hpair, rfl⟩
    exact total_eq_one hS (hn pair hpair).1 (hn pair hpair).2
      (hs pair hpair).1 (hs pair hpair).2
  have reduce : (∏ p ∈ S, value (oddH p) arguments) =
      ∏ p ∈ E, value (oddH p) arguments := by
    symm
    apply Finset.prod_subset hES
    intro p hp hpE
    exact hoff p (hS p hp).1 (hS p hp).2 hpE
  unfold total at ht
  rw [value_mul, value_mul, value_prod, reduce] at ht
  have hi : value infinity arguments ^ 2 = 1 :=
    value_sq infinity arguments (fun pair _ => infinity_sq pair.1 pair.2)
  rcases sq_eq_one_iff.mp hi with hi | hi
  · rw [hi, one_mul] at ht
    simpa [hi] using ht
  · rw [hi, neg_one_mul] at ht
    rw [hi]
    have := congrArg Neg.neg ht
    simpa only [neg_mul, neg_neg, neg_one_mul] using this

lemma odd_edge {p : ℕ} (a b : ℤ)
    (h : ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b)) :
    oddH p a b = jacobiSym a p ^ padicValInt p b *
      jacobiSym b p ^ padicValInt p a := by
  by_cases ha : (p : ℤ) ∣ a
  · have hb : ¬ (p : ℤ) ∣ b := fun hb => h ⟨ha, hb⟩
    simp [oddH, oddParts, padicValInt.eq_zero_of_not_dvd hb,
      unitPart]
  · simp [oddH, oddParts, padicValInt.eq_zero_of_not_dvd ha,
      unitPart]

lemma star_term {p : ℕ} (a b : ℤ)
    (h : (p : ℤ) ∣ a → jacobiSym b p = 1) :
    jacobiSym b p ^ padicValInt p a = 1 := by
  by_cases ha : (p : ℤ) ∣ a
  · rw [h ha, one_pow]
  · rw [padicValInt.eq_zero_of_not_dvd ha, pow_zero]

/-- Mathematical evidence accompanies data; the conclusion is always checked
    through the same graph product formula. -/
structure Certificate (f : ℤ → ℤ → ℤ) (n : ℕ) where
  graphs : Fin n → ℤ → ℤ → Arguments
  exceptional : Finset ℕ
  primes : ∀ p ∈ exceptional, p.Prime ∧ p ≠ 2
  nonzero : ∀ x y, f x y = 0 → ∀ i, Nonzero (graphs i x y)
  ordinary : ∀ x y, f x y = 0 → ∀ i p, p.Prime → p ≠ 2 →
    p ∉ exceptional → value (oddH p) (graphs i x y) = 1
  finiteRows : List (Fin n → ℤ)
  realRows : List (Fin n → ℤ)
  finite : ∀ x y, f x y = 0 →
    (fun i => value twoH (graphs i x y) *
      ∏ p ∈ exceptional, value (oddH p) (graphs i x y)) ∈ finiteRows
  real : ∀ x y, f x y = 0 →
    (fun i => value infinity (graphs i x y)) ∈ realRows
  disjoint : ∀ row ∈ finiteRows, row ∉ realRows

theorem Certificate.sound {f : ℤ → ℤ → ℤ} {n : ℕ}
    (certificate : Certificate f n) : ¬ ∃ x y : ℤ, f x y = 0 := by
  rintro ⟨x, y, hf⟩
  have hg : (fun i => value twoH (certificate.graphs i x y) *
      ∏ p ∈ certificate.exceptional, value (oddH p) (certificate.graphs i x y)) =
      (fun i => value infinity (certificate.graphs i x y)) := by
    funext i
    exact global_except _ certificate.primes (certificate.nonzero x y hf i)
      (certificate.ordinary x y hf i)
  have hfinite := certificate.finite x y hf
  rw [hg] at hfinite
  exact certificate.disjoint _ hfinite (certificate.real x y hf)

end GraphCert.Quadratic

                                              
namespace GraphCert.Quadratic

lemma cast_three (a : ℤ) : ((a : ZMod 4) = 3) ↔ a % 4 = 3 := by
  simpa using ZMod.intCast_eq_intCast_iff' a 3 4

end GraphCert.Quadratic

namespace LocalSymbols

def unitPart (p : ℕ) (a : ℤ) := a/(p:ℤ)^padicValInt p a

lemma decompose (p : ℕ) (a : ℤ) : (p:ℤ)^padicValInt p a*unitPart p a=a := by
  exact Int.mul_ediv_cancel' (padicValInt_dvd a)

lemma unitPart_not_dvd {p : ℕ} [Fact p.Prime] (a : ℤ) (ha : a≠0) : ¬(p:ℤ)∣unitPart p a := by
  rintro ⟨k,hk⟩
  have hd : (p:ℤ)^(padicValInt p a+1)∣a := by
    refine ⟨k,?_⟩
    conv_lhs => rw [←decompose p a,hk]
    rw [pow_succ]
    ring
  have ht := (padicValInt_dvd_iff (padicValInt p a+1) a).mp hd
  omega

lemma unitPart_eq_of_not_dvd {p : ℕ} (a : ℤ) (ha : ¬(p:ℤ)∣a) : unitPart p a=a := by
  simp [unitPart,padicValInt.eq_zero_of_not_dvd ha]

def c4Pair (a b : ZMod 4) : ℤ := if a=3 ∧ b=3 then -1 else 1

def oddSymbol (p : ℕ) (a b : ℤ) : ℤ :=
  jacobiSym (-1) p^(padicValInt p a*padicValInt p b)*
  jacobiSym (unitPart p a) p^padicValInt p b*
  jacobiSym (unitPart p b) p^padicValInt p a

def twoSymbol (a b : ℤ) : ℤ :=
  c4Pair (unitPart 2 a:ZMod 4) (unitPart 2 b:ZMod 4)*
  ZMod.χ₈ (unitPart 2 a:ZMod 8)^padicValInt 2 b*
  ZMod.χ₈ (unitPart 2 b:ZMod 8)^padicValInt 2 a

def symbol (p : ℕ) (a b : ℤ) : ℤ := if p=2 then twoSymbol a b else oddSymbol p a b

lemma prime_not_dvd_other {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p≠q) :
    ¬(p:ℤ)∣(q:ℤ) := by
  intro hd
  have hd' : p∣q := by exact_mod_cast hd
  exact hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd')

lemma prime_not_dvd_neg_one {p : ℕ} (hp : p.Prime) : ¬(p:ℤ)∣(-1:ℤ) := by
  intro h
  have hd : (p:ℤ)∣1 := (dvd_neg.mp h)
  have hd' : p∣1 := by exact_mod_cast hd
  exact hp.not_dvd_one hd'

lemma jacobi_square_mod {p : ℕ} [Fact p.Prime] (a : ℤ) (ha : ¬(p:ℤ)∣a)
    (hs : IsSquare (a:ZMod p)) : jacobiSym a p=1 := by
  rw [←jacobiSym.legendreSym.to_jacobiSym]
  apply (legendreSym.eq_one_iff p _).mpr hs
  intro he
  exact ha ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he)

lemma odd_edge (p : ℕ) (hp2 : p≠2) (a b : ℤ) (h : ¬((p:ℤ)∣a ∧ (p:ℤ)∣b)) :
    symbol p a b=jacobiSym a p^padicValInt p b*jacobiSym b p^padicValInt p a := by
  by_cases ha : (p:ℤ)∣a
  · have hb : ¬(p:ℤ)∣b := fun hh => h ⟨ha,hh⟩
    simp [symbol,hp2,oddSymbol,padicValInt.eq_zero_of_not_dvd hb,unitPart_eq_of_not_dvd b hb]
  · simp [symbol,hp2,oddSymbol,padicValInt.eq_zero_of_not_dvd ha,unitPart_eq_of_not_dvd a ha]

lemma val_factor {p : ℕ} [Fact p.Prime] (a u : ℤ) (e : ℕ)
    (ha : a=(p:ℤ)^e*u) (hu : ¬(p:ℤ)∣u) : padicValInt p a=e := by
  have hp : (p:ℤ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hu0 : u≠0 := by intro he; exact hu (he ▸ dvd_zero _)
  have he : padicValInt p ((p:ℤ)^e)=e := by
    simp only [padicValInt,Int.natAbs_pow,Int.natAbs_natCast]
    exact padicValNat.prime_pow e
  rw [ha,padicValInt.mul (pow_ne_zero e hp) hu0,he,padicValInt.eq_zero_of_not_dvd hu,add_zero]

lemma unitPart_factor {p : ℕ} [Fact p.Prime] (a u : ℤ) (e : ℕ)
    (ha : a=(p:ℤ)^e*u) (hu : ¬(p:ℤ)∣u) : unitPart p a=u := by
  have hp : (p:ℤ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  dsimp [unitPart]
  rw [val_factor a u e ha hu,ha]
  exact Int.mul_ediv_cancel_left u (pow_ne_zero e hp)

end LocalSymbols

namespace GraphCert.Quadratic

lemma odd_symbol {p : ℕ} (hp : p ≠ 2) (a b : ℤ) :
    RatHilbert.oddH p a b = LocalSymbols.symbol p a b := by
  simp [RatHilbert.oddH, RatHilbert.oddParts, RatHilbert.unitPart,
    LocalSymbols.symbol, hp, LocalSymbols.oddSymbol, LocalSymbols.unitPart]

set_option backward.isDefEq.respectTransparency false in
lemma two_symbol (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    RatHilbert.twoH a b = LocalSymbols.symbol 2 a b := by
  have hau := RatHilbert.unitPart_two_odd ha
  have hbu := RatHilbert.unitPart_two_odd hb
  simp only [RatHilbert.twoH, RatHilbert.twoParts,
    RatHilbert.twoChar_eq_chi _ hau, RatHilbert.twoChar_eq_chi _ hbu]
  simp [RatHilbert.qr, RatHilbert.unitPart, LocalSymbols.symbol,
    LocalSymbols.twoSymbol, LocalSymbols.unitPart, LocalSymbols.c4Pair, cast_three, ite_mul]

lemma value_odd_symbol {p : ℕ} (hp : p ≠ 2) (arguments : Arguments) :
    value (RatHilbert.oddH p) arguments =
      value (LocalSymbols.symbol p) arguments :=
  value_congr arguments (fun _ _ => odd_symbol hp _ _)

lemma value_two_symbol (arguments : Arguments) (hn : Nonzero arguments) :
    value RatHilbert.twoH arguments =
      value (LocalSymbols.symbol 2) arguments :=
  value_congr arguments (fun pair h => two_symbol _ _ (hn pair h).1 (hn pair h).2)

end GraphCert.Quadratic



namespace LinearNormPositivity

theorem positive (a b c k R u : ℤ)
    (hf : u^3+a*u^2+b*u+c=0)
    (hd : a^2*b^2-4*b^3-4*a^3*c-27*c^2+18*a*b*c<0)
    (hQ : 0<R^3-a*k*R^2+b*k^2*R-c*k^3) : 0<k*u+R := by
  have hc : c=-u^3-a*u^2-b*u := by linarith
  let s := a+u
  let w := u^2+a*u+b
  let T := R^2-k*R*s+k^2*w
  have hi : (4*w-s^2)*(3*u^2+2*a*u+b)^2 =
      -(a^2*b^2-4*b^3-4*a^3*c-27*c^2+18*a*b*c) := by
    dsimp [w,s]
    rw [hc]
    ring
  have hdelta : 0<4*w-s^2 := by
    by_contra hh
    have hm := mul_nonpos_of_nonpos_of_nonneg (show 4*w-s^2≤0 by omega)
      (sq_nonneg (3*u^2+2*a*u+b))
    linarith
  have heT : 4*T=(2*R-k*s)^2+k^2*(4*w-s^2) := by dsimp [T]; ring
  have hT : 0≤T := by
    have hm := mul_nonneg (sq_nonneg k) hdelta.le
    nlinarith [sq_nonneg (2*R-k*s)]
  have heQ : R^3-a*k*R^2+b*k^2*R-c*k^3=(k*u+R)*T := by
    dsimp [T,w,s]
    rw [hc]
    ring
  by_contra hh
  have hm := mul_nonpos_of_nonpos_of_nonneg (show k*u+R≤0 by omega) hT
  rw [heQ] at hQ
  omega

end LinearNormPositivity


namespace CubicGap

theorem no_root (a b c step lo u : ℤ) (hstep : 0<step)
    (hf : (step*u)^3+a*(step*u)^2+b*(step*u)+c=0)
    (hd : a^2*b^2-4*b^3-4*a^3*c-27*c^2+18*a*b*c<0)
    (hl : (step*lo)^3+a*(step*lo)^2+b*(step*lo)+c<0)
    (hh : 0<(step*(lo+1))^3+a*(step*(lo+1))^2+b*(step*(lo+1))+c) : False := by
  have hlo : 0<step*u-step*lo := by
    have hp := LinearNormPositivity.positive a b c 1 (-step*lo) (step*u) hf hd
      (by convert neg_pos.mpr hl using 1 <;> ring)
    convert hp using 1 <;> ring
  have hhi : 0<step*(lo+1)-step*u := by
    have hp := LinearNormPositivity.positive a b c (-1) (step*(lo+1)) (step*u) hf hd
      (by convert hh using 1 <;> ring)
    convert hp using 1 <;> ring
  have h1 : lo<u := by
    by_contra hh
    have hm := mul_le_mul_of_nonneg_left (show u≤lo by omega) hstep.le
    linarith only [hm,hlo]
  have h2 : u<lo+1 := by
    by_contra hh
    have hm := mul_le_mul_of_nonneg_left (show lo+1≤u by omega) hstep.le
    linarith only [hm,hhi]
  omega

end CubicGap

namespace PrimeClasses
open LocalSymbols

def exponent2 (c:Fin 8):ℕ:=c.val/4
def unit2 (c:Fin 8):ℕ:=2*(c.val%4)+1
abbrev Spec2 (a:ℤ) (c:Fin 8):Prop:=
  exponent2 c=padicValInt 2 a%2 ∧ (unit2 c:ZMod 8)=(unitPart 2 a:ZMod 8)
def eval2 (a b:Fin 8):ℤ:=
  c4Pair (unit2 a:ZMod 4) (unit2 b:ZMod 4)*
  ZMod.χ₈ (unit2 a:ZMod 8)^exponent2 b*ZMod.χ₈ (unit2 b:ZMod 8)^exponent2 a

lemma exists2 (a:ℤ) (ha:a≠0) : ∃c:Fin 8,Spec2 a c := by
  have hodd:¬(2:ℤ)∣unitPart 2 a:=unitPart_not_dvd _ ha
  let r:ℕ:=(unitPart 2 a%8).toNat
  have hr:(r:ℤ)=unitPart 2 a%8 := by dsimp [r]; exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  have hlt:r<8:=by have hh:=Int.emod_lt_of_pos (unitPart 2 a) (show (0:ℤ)<8 by decide); omega
  have ho:r%2=1:=by omega
  let c:Fin 8:=⟨4*(padicValInt 2 a%2)+r/2,by omega⟩
  refine ⟨c,?_,?_⟩
  · dsimp [exponent2,c]; omega
  · apply (ZMod.intCast_eq_intCast_iff' (unit2 c:ℤ) (unitPart 2 a) 8).mpr
    dsimp [unit2,c]
    omega

lemma pow_parity (a:ℤ) (n:ℕ) (ha:a^2=1) : a^n=a^(n%2) := by
  conv_lhs => rw [←Nat.mod_add_div n 2]
  rw [pow_add,pow_mul,ha,one_pow,mul_one]

lemma pow_sq (a:ℤ) (n:ℕ) (ha:a^2=1) : (a^n)^2=1 := by
  rw [←pow_mul,Nat.mul_comm n 2,pow_mul,ha,one_pow]

lemma pow_product_parity (a:ℤ) (n m:ℕ) (ha:a^2=1) : a^(n*m)=a^((n%2)*(m%2)) := by
  rw [pow_mul,pow_parity a n ha,pow_parity (a^(n%2)) m (pow_sq a (n%2) ha),←pow_mul]

private lemma chi8_sq : ∀c:Fin 8, ZMod.χ₈ (unit2 c:ZMod 8)^2=1 := by decide

lemma symbol_two (a b:ℤ) (ca cb:Fin 8) (ha:Spec2 a ca) (hb:Spec2 b cb) :
    symbol 2 a b=eval2 ca cb := by
  have ha4:=congrArg (fun u:ZMod 8 => (ZMod.cast u:ZMod 4)) ha.2
  have hb4:=congrArg (fun u:ZMod 8 => (ZMod.cast u:ZMod 4)) hb.2
  simp only [ZMod.cast_natCast (show 4∣8 by decide),ZMod.cast_intCast (show 4∣8 by decide)] at ha4 hb4
  simp only [symbol,↓reduceIte,twoSymbol,eval2,←ha.2,←hb.2,←ha4,←hb4]
  rw [pow_parity _ _ (chi8_sq ca),pow_parity _ _ (chi8_sq cb),←ha.1,←hb.1]

abbrev Compatible2 (r:ZMod 32) (c:Fin 8):Prop:=
  if r.val=0 then True
  else if r.val%2=1 then exponent2 c=0 ∧ unit2 c=r.val%8
  else if r.val%4=2 then exponent2 c=1 ∧ unit2 c=(r.val/2)%8
  else if r.val%8=4 then exponent2 c=0 ∧ unit2 c=(r.val/4)%8
  else if r.val%16=8 then exponent2 c=1 ∧ unit2 c%4=(r.val/8)%4
  else exponent2 c=0

instance (r:ZMod 32) (c:Fin 8) : Decidable (Compatible2 r c) := by
  unfold Compatible2
  split_ifs <;> infer_instance

lemma compatible2 (a:ℤ) (ha:a≠0) (c:Fin 8) (hs:Spec2 a c) : Compatible2 (a:ZMod 32) c := by
  have he:=decompose 2 a
  have ho:¬(2:ℤ)∣unitPart 2 a:=unitPart_not_dvd _ ha
  have hr:(((a:ZMod 32).val:ℕ):ℤ)=a%32:=by rw [ZMod.val_intCast]; norm_num
  have hc:((unit2 c:ℕ):ℤ)%8=unitPart 2 a%8 := by
    apply (ZMod.intCast_eq_intCast_iff' (unit2 c:ℤ) (unitPart 2 a) 8).mp
    simpa using hs.2
  have hec:=hs.1
  have hclt:=c.isLt
  by_cases hv:padicValInt 2 a<5
  · interval_cases hh:padicValInt 2 a
    all_goals
      norm_num only [hh,pow_zero,pow_one,Nat.reducePow,one_mul] at he
      dsimp [Compatible2,exponent2,unit2] at hec hc ⊢
      split_ifs <;> omega
  · have hd:(2:ℤ)^5∣a := (padicValInt_dvd_iff (p:=2) 5 a).mpr (Or.inr (by omega))
    have hz:(a:ZMod 32).val=0:=by norm_num at hd; omega
    simp [Compatible2,hz]

private instance : Fact (Nat.Prime 3):=⟨by decide⟩
def exponent3 (c:Fin 4):ℕ:=c.val/2
def unit3 (c:Fin 4):ℕ:=c.val%2+1
def sign3 (c:Fin 4):ℤ:=if c.val%2=0 then 1 else -1
abbrev Spec3 (a:ℤ) (c:Fin 4):Prop:=
  exponent3 c=padicValInt 3 a%2 ∧ (unit3 c:ZMod 3)=(unitPart 3 a:ZMod 3)
def eval3 (a b:Fin 4):ℤ:=(-1)^(exponent3 a*exponent3 b)*sign3 a^exponent3 b*sign3 b^exponent3 a

lemma exists3 (a:ℤ) (ha:a≠0) : ∃c:Fin 4,Spec3 a c := by
  have hodd:¬(3:ℤ)∣unitPart 3 a:=unitPart_not_dvd _ ha
  let r:ℕ:=(unitPart 3 a%3).toNat
  have hr:(r:ℤ)=unitPart 3 a%3 := by dsimp [r]; exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  have hlt:r<3:=by have hh:=Int.emod_lt_of_pos (unitPart 3 a) (show (0:ℤ)<3 by decide); omega
  have ho:0<r:=by omega
  let c:Fin 4:=⟨2*(padicValInt 3 a%2)+(r-1),by omega⟩
  refine ⟨c,?_,?_⟩
  · dsimp [exponent3,c]; omega
  · apply (ZMod.intCast_eq_intCast_iff' (unit3 c:ℤ) (unitPart 3 a) 3).mpr
    dsimp [unit3,c]
    omega

private lemma jacobi3 : ∀c:Fin 4, jacobiSym (unit3 c:ℤ) 3=sign3 c := by
  intro c; fin_cases c <;> norm_num [unit3,sign3]
private lemma sign3_sq : ∀c:Fin 4, sign3 c^2=1 := by decide

lemma jacobi3_spec (a:ℤ) (c:Fin 4) (hs:Spec3 a c) : jacobiSym (unitPart 3 a) 3=sign3 c := by
  rw [←jacobi3]
  apply jacobiSym.mod_left'
  have hh:= (ZMod.intCast_eq_intCast_iff' (unit3 c:ℤ) (unitPart 3 a) 3).mp (by simpa using hs.2)
  simpa using hh.symm

lemma symbol_three (a b:ℤ) (ca cb:Fin 4) (ha:Spec3 a ca) (hb:Spec3 b cb) :
    symbol 3 a b=eval3 ca cb := by
  simp only [symbol,show ¬(3:ℕ)=2 by decide,↓reduceIte,oddSymbol,eval3,
    jacobi3_spec a ca ha,jacobi3_spec b cb hb]
  have hm:jacobiSym (-1) 3=-1:=by norm_num
  rw [hm,pow_product_parity (-1) _ _ (by norm_num),pow_parity _ _ (sign3_sq ca),pow_parity _ _ (sign3_sq cb),←ha.1,←hb.1]

abbrev Compatible3 (r:ZMod 27) (c:Fin 4):Prop:=
  if r.val=0 then True
  else if r.val%3≠0 then exponent3 c=0 ∧ unit3 c=r.val%3
  else if r.val%9≠0 then exponent3 c=1 ∧ unit3 c=(r.val/3)%3
  else exponent3 c=0 ∧ unit3 c=(r.val/9)%3

instance (r:ZMod 27) (c:Fin 4) : Decidable (Compatible3 r c) := by
  unfold Compatible3
  split_ifs <;> infer_instance

lemma compatible3 (a:ℤ) (ha:a≠0) (c:Fin 4) (hs:Spec3 a c) : Compatible3 (a:ZMod 27) c := by
  have he:=decompose 3 a
  have ho:¬(3:ℤ)∣unitPart 3 a:=unitPart_not_dvd _ ha
  have hr:(((a:ZMod 27).val:ℕ):ℤ)=a%27:=by rw [ZMod.val_intCast]; norm_num
  have hc:((unit3 c:ℕ):ℤ)%3=unitPart 3 a%3 := by
    apply (ZMod.intCast_eq_intCast_iff' (unit3 c:ℤ) (unitPart 3 a) 3).mp
    simpa using hs.2
  have hec:=hs.1
  have hclt:=c.isLt
  by_cases hv:padicValInt 3 a<3
  · interval_cases hh:padicValInt 3 a
    all_goals
      norm_num only [hh,pow_zero,pow_one,Nat.reducePow,one_mul] at he
      dsimp [Compatible3,exponent3,unit3] at hec hc ⊢
      split_ifs <;> omega
  · have hd:(3:ℤ)^3∣a := (padicValInt_dvd_iff (p:=3) 3 a).mpr (Or.inr (by omega))
    have hz:(a:ZMod 27).val=0:=by norm_num at hd; omega
    simp [Compatible3,hz]

end PrimeClasses



namespace PrimeClasses
open LocalSymbols

abbrev Compatible2_3 (r:ZMod 8) (c:Fin 8):Prop:=
  if r.val=0 then True
  else if r.val%2≠0 then exponent2 c=0 ∧ unit2 c%8=(r.val/1)%8
  else if r.val%4≠0 then exponent2 c=1 ∧ unit2 c%4=(r.val/2)%4
  else exponent2 c=0

instance (r:ZMod 8) (c:Fin 8) : Decidable (Compatible2_3 r c) := by
  unfold Compatible2_3
  infer_instance
lemma compatible2_3 (a:ℤ) (ha:a≠0) (c:Fin 8) (hs:Spec2 a c) : Compatible2_3 (a:ZMod 8) c := by
  have he:=decompose 2 a
  have ho:¬(2:ℤ)∣unitPart 2 a:=unitPart_not_dvd _ ha
  have hr:(((a:ZMod 8).val:ℕ):ℤ)=a%8:=by rw [ZMod.val_intCast]; norm_num
  have hc:((unit2 c:ℕ):ℤ)%8=unitPart 2 a%8 := by
    apply (ZMod.intCast_eq_intCast_iff' (unit2 c:ℤ) (unitPart 2 a) 8).mp
    simpa using hs.2
  have hec:=hs.1
  have hclt:=c.isLt
  by_cases hv:padicValInt 2 a<3
  · interval_cases hh:padicValInt 2 a
    all_goals norm_num only [hh,pow_zero,pow_one,Nat.reducePow,one_mul] at he hec
    · have hz:(a:ZMod 8).val≠0:=by omega
      have ht:(a:ZMod 8).val%2≠0:=by omega
      simp only [Compatible2_3,if_neg hz,if_pos ht]
      dsimp [exponent2,unit2] at hc hec ⊢
      omega
    · have hz:(a:ZMod 8).val≠0:=by omega
      have hd2:(a:ZMod 8).val%2=0:=by omega
      have ht:(a:ZMod 8).val%4≠0:=by omega
      simp only [Compatible2_3,if_neg hz,if_neg (not_not.mpr hd2),if_pos ht]
      dsimp [exponent2,unit2] at hc hec ⊢
      omega
    · have hz:(a:ZMod 8).val≠0:=by omega
      have hd2:(a:ZMod 8).val%2=0:=by omega
      have hd4:(a:ZMod 8).val%4=0:=by omega
      simp only [Compatible2_3,if_neg hz,if_neg (not_not.mpr hd2),if_neg (not_not.mpr hd4)]
      dsimp [exponent2,unit2] at hc hec ⊢
      omega
  · have hd:(2:ℤ)^3∣a := (padicValInt_dvd_iff (p:=2) 3 a).mpr (Or.inr (by omega))
    have hz:(a:ZMod 8).val=0:=by norm_num at hd; omega
    simp [Compatible2_3,hz]

private instance : Fact (Nat.Prime 5):=⟨by decide⟩
def exponent5 (c:Fin 8):ℕ:=c.val/4
def unit5 (c:Fin 8):ℕ:=c.val%4+1
def sign5 (c:Fin 8):ℤ:=if unit5 c=1 ∨ unit5 c=4 then 1 else -1
abbrev Spec5 (a:ℤ) (c:Fin 8):Prop:=
  exponent5 c=padicValInt 5 a%2 ∧ (unit5 c:ZMod 5)=(unitPart 5 a:ZMod 5)
def eval5 (a b:Fin 8):ℤ:=(1)^(exponent5 a*exponent5 b)*sign5 a^exponent5 b*sign5 b^exponent5 a
lemma exists5 (a:ℤ) (ha:a≠0) : ∃c:Fin 8,Spec5 a c := by
  have hodd:¬(5:ℤ)∣unitPart 5 a:=unitPart_not_dvd _ ha
  let r:ℕ:=(unitPart 5 a%5).toNat
  have hr:(r:ℤ)=unitPart 5 a%5:=by dsimp [r]; exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  have hlt:r<5:=by have hh:=Int.emod_lt_of_pos (unitPart 5 a) (show (0:ℤ)<5 by decide); omega
  have ho:0<r:=by omega
  let c:Fin 8:=⟨4*(padicValInt 5 a%2)+(r-1),by omega⟩
  refine ⟨c,?_,?_⟩
  · dsimp [exponent5,c]; omega
  · apply (ZMod.intCast_eq_intCast_iff' (unit5 c:ℤ) (unitPart 5 a) 5).mpr
    dsimp [unit5,c]
    omega
private lemma jacobi5 : ∀c:Fin 8,jacobiSym (unit5 c:ℤ) 5=sign5 c := by
  intro c; fin_cases c <;> norm_num [unit5,sign5]
private lemma sign5_sq : ∀c:Fin 8,sign5 c^2=1 := by decide
lemma jacobi5_spec (a:ℤ) (c:Fin 8) (hs:Spec5 a c) : jacobiSym (unitPart 5 a) 5=sign5 c := by
  rw [←jacobi5]
  apply jacobiSym.mod_left'
  have hh:=(ZMod.intCast_eq_intCast_iff' (unit5 c:ℤ) (unitPart 5 a) 5).mp (by simpa using hs.2)
  simpa using hh.symm
lemma symbol_5 (a b:ℤ) (ca cb:Fin 8) (ha:Spec5 a ca) (hb:Spec5 b cb) :
    symbol 5 a b=eval5 ca cb := by
  simp only [symbol,show ¬(5:ℕ)=2 by decide,↓reduceIte,oddSymbol,eval5,
    jacobi5_spec a ca ha,jacobi5_spec b cb hb]
  have hm:jacobiSym (-1) 5=1:=by norm_num
  rw [hm,pow_product_parity (1) _ _ (by norm_num),pow_parity _ _ (sign5_sq ca),pow_parity _ _ (sign5_sq cb),←ha.1,←hb.1]
abbrev Compatible5 (r:ZMod 625) (c:Fin 8):Prop:=
  if r.val=0 then True
  else if r.val%5≠0 then exponent5 c=0 ∧ unit5 c=(r.val/1)%5
  else if r.val%25≠0 then exponent5 c=1 ∧ unit5 c=(r.val/5)%5
  else if r.val%125≠0 then exponent5 c=0 ∧ unit5 c=(r.val/25)%5
  else exponent5 c=1 ∧ unit5 c=(r.val/125)%5

instance (r:ZMod 625) (c:Fin 8) : Decidable (Compatible5 r c) := by
  unfold Compatible5
  split_ifs <;> infer_instance
lemma compatible5 (a:ℤ) (ha:a≠0) (c:Fin 8) (hs:Spec5 a c) : Compatible5 (a:ZMod 625) c := by
  have he:=decompose 5 a
  have ho:¬(5:ℤ)∣unitPart 5 a:=unitPart_not_dvd _ ha
  have hr:(((a:ZMod 625).val:ℕ):ℤ)=a%625:=by rw [ZMod.val_intCast]; norm_num
  have hc:((unit5 c:ℕ):ℤ)%5=unitPart 5 a%5 := by
    apply (ZMod.intCast_eq_intCast_iff' (unit5 c:ℤ) (unitPart 5 a) 5).mp
    simpa using hs.2
  have hec:=hs.1
  have hclt:=c.isLt
  by_cases hv:padicValInt 5 a<4
  · interval_cases hh:padicValInt 5 a
    all_goals
      norm_num only [hh,pow_zero,pow_one,Nat.reducePow,one_mul] at he
      dsimp [Compatible5,exponent5,unit5] at hec hc ⊢
      split_ifs <;> omega
  · have hd:(5:ℤ)^4∣a := (padicValInt_dvd_iff (p:=5) 4 a).mpr (Or.inr (by omega))
    have hz:(a:ZMod 625).val=0:=by norm_num at hd; omega
    simp [Compatible5,hz]
end PrimeClasses

namespace PrimeClasses
open LocalSymbols
private instance : Fact (Nat.Prime 3):=⟨by decide⟩
abbrev Compatible3_6 (r:ZMod 729) (c:Fin 4):Prop:=
  if r.val=0 then True
  else if r.val%3≠0 then exponent3 c=0 ∧ unit3 c=r.val%3
  else if r.val%9≠0 then exponent3 c=1 ∧ unit3 c=(r.val/3)%3
  else if r.val%27≠0 then exponent3 c=0 ∧ unit3 c=(r.val/9)%3
  else if r.val%81≠0 then exponent3 c=1 ∧ unit3 c=(r.val/27)%3
  else if r.val%243≠0 then exponent3 c=0 ∧ unit3 c=(r.val/81)%3
  else exponent3 c=1 ∧ unit3 c=(r.val/243)%3
instance (r:ZMod 729) (c:Fin 4) : Decidable (Compatible3_6 r c) := by
  unfold Compatible3_6
  split_ifs <;> infer_instance
lemma compatible3_6 (a:ℤ) (ha:a≠0) (c:Fin 4) (hs:Spec3 a c) : Compatible3_6 (a:ZMod 729) c := by
  have he:=decompose 3 a
  have ho:¬(3:ℤ)∣unitPart 3 a:=unitPart_not_dvd _ ha
  have hr:(((a:ZMod 729).val:ℕ):ℤ)=a%729:=by rw [ZMod.val_intCast]; norm_num
  have hc:((unit3 c:ℕ):ℤ)%3=unitPart 3 a%3:=by
    apply (ZMod.intCast_eq_intCast_iff' (unit3 c:ℤ) (unitPart 3 a) 3).mp
    simpa using hs.2
  have hec:=hs.1
  have hclt:=c.isLt
  by_cases hv:padicValInt 3 a<6
  · interval_cases hh:padicValInt 3 a
    all_goals
      norm_num only [hh,pow_zero,pow_one,Nat.reducePow,one_mul] at he
      dsimp [Compatible3_6,exponent3,unit3] at hec hc ⊢
      split_ifs <;> omega
  · have hd:(3:ℤ)^6∣a:=(padicValInt_dvd_iff (p:=3) 6 a).mpr (Or.inr (by omega))
    have hz:(a:ZMod 729).val=0:=by norm_num at hd; omega
    simp [Compatible3_6,hz]
end PrimeClasses


namespace ResidueLift

def res (m:ℕ) (x:ℤ):ℕ := (x%(m:ℤ)).toNat
lemma res_cast (m:ℕ) (hm:0<m) (x:ℤ) : (res m x:ℤ)=x%(m:ℤ) := by
  dsimp [res]
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by exact_mod_cast hm.ne')
lemma res_lt (m:ℕ) (hm:0<m) (x:ℤ) : res m x<m := by
  have hh:=Int.emod_lt_of_pos x (show (0:ℤ)<m by exact_mod_cast hm)
  rw [←res_cast m hm x] at hh
  exact_mod_cast hh
lemma res_mul_mod (m p:ℕ) (hm:0<m) (hp:0<p) (x:ℤ) : res (m*p) x%m=res m x := by
  have hi:((res (m*p) x%m:ℕ):ℤ)=(res m x:ℤ):=by
    rw [Int.natCast_emod,res_cast (m*p) (Nat.mul_pos hm hp),res_cast m hm]
    exact Int.emod_emod_of_dvd x (by exact_mod_cast (dvd_mul_right m p))
  exact_mod_cast hi

def lifts (m p:ℕ) (rs:List (ℕ×ℕ)) : List (ℕ×ℕ) :=
  rs.flatMap fun q => (List.range p).flatMap fun a =>
    (List.range p).map fun b => (q.1+m*a,q.2+m*b)

def roots (f:ℤ→ℤ→ℤ) (p:ℕ) : ℕ → List (ℕ×ℕ)
  | 0 => [(0,0)]
  | k+1 => (lifts (p^k) p (roots f p k)).filter fun q =>
      decide (f q.1 q.2 % (p^(k+1):ℕ)=0)

lemma lifts_complete (m p:ℕ) (hm:0<m) (hp:0<p) (rs:List (ℕ×ℕ)) (x z:ℤ)
    (hxz:(res m x,res m z)∈rs) :
    (res (m*p) x,res (m*p) z)∈lifts m p rs := by
  let a:=res (m*p) x
  let b:=res (m*p) z
  have ha:a/m<p:=(Nat.div_lt_iff_lt_mul hm).mpr (by simpa [a,mul_comm] using res_lt (m*p) (Nat.mul_pos hm hp) x)
  have hb:b/m<p:=(Nat.div_lt_iff_lt_mul hm).mpr (by simpa [b,mul_comm] using res_lt (m*p) (Nat.mul_pos hm hp) z)
  have ax:res m x+m*(a/m)=a:=by rw [←res_mul_mod m p hm hp x]; exact Nat.mod_add_div a m
  have bz:res m z+m*(b/m)=b:=by rw [←res_mul_mod m p hm hp z]; exact Nat.mod_add_div b m
  apply List.mem_flatMap.mpr
  refine ⟨(res m x,res m z),hxz,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨a/m,List.mem_range.mpr ha,?_⟩
  apply List.mem_map.mpr
  exact ⟨b/m,List.mem_range.mpr hb,by simp only [ax,bz,a,b]⟩

lemma complete (f:ℤ→ℤ→ℤ) (p:ℕ) (hp:0<p) (x z:ℤ)
    (hvalid:∀k:ℕ,f (res (p^k) x) (res (p^k) z) % (p^k:ℕ)=0) (k:ℕ) :
    (res (p^k) x,res (p^k) z)∈roots f p k := by
  induction k with
  | zero => simp [roots,res]
  | succ k ih =>
    apply List.mem_filter.mpr
    constructor
    · rw [pow_succ]
      exact lifts_complete (p^k) p (pow_pos hp _) hp _ x z ih
    · simpa only [decide_eq_true_eq] using hvalid (k+1)

lemma complete_of_periodic (f:ℤ→ℤ→ℤ)
    (periodic:∀m:ℕ,∀x z:ℤ,f (x%m) (z%m)%m=f x z%m)
    (p:ℕ) (hp:0<p) (x z:ℤ) (hf:f x z=0) (k:ℕ) :
    (res (p^k) x,res (p^k) z)∈roots f p k := by
  apply complete f p hp x z _ k
  intro j
  rw [res_cast _ (pow_pos hp _) x,res_cast _ (pow_pos hp _) z,periodic,hf,Int.zero_emod]

lemma res_zmod (m:ℕ) (hm:0<m) (x:ℤ) : (res m x:ZMod m)=(x:ZMod m) := by
  have hh:=congrArg (fun n:ℤ=>(n:ZMod m)) (res_cast m hm x)
  simpa using hh
end ResidueLift


namespace ClassChoices
def allowed {n:ℕ} (P:Fin n→Prop) [DecidablePred P] : List (Fin n) :=
  (List.finRange n).filter fun c=>decide (P c)
lemma mem_allowed {n:ℕ} {P:Fin n→Prop} [DecidablePred P] {c:Fin n} (hc:P c) : c∈allowed P := by
  simp [allowed,hc]
def vectors {α:Type*} : List (List α) → List (List α)
  | [] => [[]]
  | xs::xss => xs.flatMap fun x => (vectors xss).map fun ys=>x::ys
lemma cons_mem {α:Type*} {x:α} {xs ys:List α} {xss:List (List α)}
    (hx:x∈xs) (hy:ys∈vectors xss) : x::ys∈vectors (xs::xss) := by
  exact List.mem_flatMap.mpr ⟨x,hx,List.mem_map.mpr ⟨ys,hy,rfl⟩⟩
end ClassChoices

                                             
namespace GraphCert.Quadratic

theorem square_of_identity {p : ℕ} [Fact p.Prime]
    {D A W F H Q R : ℤ} (hF : F = 0) (hH : (p:ℤ) ∣ H)
    (hD : ¬ (p:ℤ) ∣ D) (hid : D^2*A-W^2=F*Q+H*R) :
    IsSquare (A : ZMod p) := by
  have hd : (D : ZMod p) ≠ 0 := fun h => hD ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have hh : (H : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hH
  have he := congrArg (fun z : ℤ => (z : ZMod p)) hid
  push_cast at he
  simp only [hF, Int.cast_zero, hh, zero_mul, add_zero] at he
  refine ⟨(W : ZMod p)/(D : ZMod p), ?_⟩
  rw [← sq, div_pow, eq_div_iff (pow_ne_zero 2 hd)]
  linear_combination he

theorem separate_of_identity {p : ℕ} {F H K A B C D : ℤ}
    (hF : F=0) (hD : ¬ (p:ℤ) ∣ D) (hid : F*A+H*B+K*C=D) :
    ¬ ((p:ℤ) ∣ H ∧ (p:ℤ) ∣ K) := by
  rintro ⟨hH,hK⟩
  apply hD
  rw [← hid,hF,zero_mul,zero_add]
  exact dvd_add (dvd_mul_of_dvd_left hH _) (dvd_mul_of_dvd_left hK _)

end GraphCert.Quadratic

                                               
/-! Finite local square classes for rational quadratic graph certificates. -/

namespace GraphCert.RationalClasses
open RatHilbert


abbrev Vector := Fin 3 → ZMod 2

def sign (z : ZMod 2) : ℤ := (-1)^z.val
def bit (z : ℤ) : ZMod 2 := if z=1 then 0 else 1

theorem sign_add (a b : ZMod 2) : sign (a+b)=sign a*sign b := by
  fin_cases a <;> fin_cases b <;> decide

theorem sign_bit {z : ℤ} (h : z=1 ∨ z = -1) : sign (bit z)=z := by
  rcases h with rfl | rfl <;> decide

theorem sign_nat_mul (e : ℕ) (a : ZMod 2) : sign ((e : ZMod 2)*a)=sign a^e := by
  induction e with
  | zero => simp [sign]
  | succ e ih =>
    rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,sign_add,ih,pow_succ]

def localClass (p : ℕ) (a : ℤ) : Vector :=
  ![(padicValInt p a : ZMod 2),
    if p=2 then (if unitPart p a % 4=3 then 1 else 0) else bit (jacobiSym (unitPart p a) p),
    if p=2 then bit (twoChar (unitPart p a)) else 0]

def form (p : ℕ) (a b : Vector) : ZMod 2 :=
  if p=2 then a 1*b 1+a 0*b 2+a 2*b 0
  else bit (jacobiSym (-1) p)*a 0*b 0+a 1*b 0+a 0*b 1

def pairing (p : ℕ) : Vector →ₗ[ZMod 2] Vector →ₗ[ZMod 2] ZMod 2 where
  toFun a := {
    toFun := form p a
    map_add' b c := by
      simp only [form,Pi.add_apply]
      split_ifs <;> ring
    map_smul' c b := by
      simp only [form,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
      split_ifs <;> ring }
  map_add' a b := by
    apply LinearMap.ext
    intro c
    simp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.add_apply,form,Pi.add_apply]
    split_ifs <;> ring
  map_smul' c a := by
    apply LinearMap.ext
    intro b
    simp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.smul_apply,form,
      Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    split_ifs <;> ring

theorem form_symmetric (p : ℕ) (a b : Vector) : form p a b=form p b a := by
  unfold form
  split_ifs <;> ring

theorem twoChar_cases (u : ℤ) : twoChar u=1 ∨ twoChar u = -1 := by
  unfold twoChar
  split_ifs <;> simp

theorem two_parts (e f : ℕ) (u v : ℤ) :
    twoParts e f u v = sign (form 2
      ![(e : ZMod 2),if u%4=3 then 1 else 0,bit (twoChar u)]
      ![(f : ZMod 2),if v%4=3 then 1 else 0,bit (twoChar v)]) := by
  change _ = sign ((if u%4=3 then 1 else 0)*(if v%4=3 then 1 else 0)+
    (e:ZMod 2)*bit (twoChar v)+bit (twoChar u)*(f:ZMod 2))
  simp only [sign_add,sign_nat_mul]
  rw [mul_comm (bit (twoChar u)),sign_nat_mul,
    sign_bit (twoChar_cases u),sign_bit (twoChar_cases v)]
  have h0 : sign 0=1 := by decide
  have h1 : sign 1 = -1 := by decide
  by_cases hu : u%4=3 <;> by_cases hv : v%4=3 <;>
    simp [twoParts,qr,hu,hv,h0,h1] <;> ring

theorem odd_parts (p e f : ℕ) [Fact p.Prime] (hp2 : p≠2) (u v : ℤ)
    (hu : ¬(p:ℤ)∣u) (hv : ¬(p:ℤ)∣v) :
    oddParts p e f u v = sign (form p
      ![(e : ZMod 2),bit (jacobiSym u p),0]
      ![(f : ZMod 2),bit (jacobiSym v p),0]) := by
  have hm : ¬(p:ℤ)∣(-1:ℤ) := LocalSymbols.prime_not_dvd_neg_one Fact.out
  simp only [form,hp2,ite_false,Matrix.cons_val_zero,Matrix.cons_val_one,
    sign_add]
  rw [show bit (jacobiSym (-1) p)*(e:ZMod 2)*(f:ZMod 2)=
      ((e*f:ℕ):ZMod 2)*bit (jacobiSym (-1) p) by push_cast; ring,
    mul_comm (bit (jacobiSym u p)),sign_nat_mul,sign_nat_mul,sign_nat_mul,
    sign_bit (jacobi_unit_cases hm),sign_bit (jacobi_unit_cases hu),
    sign_bit (jacobi_unit_cases hv)]
  rfl

theorem symbol_class (p : ℕ) [Fact p.Prime] {a b : ℤ} (ha : a≠0) (hb : b≠0) :
    (if p=2 then twoH a b else oddH p a b) =
      sign (form p (localClass p a) (localClass p b)) := by
  by_cases hp : p=2
  · subst p
    simpa only [localClass,ite_true,twoH] using
      two_parts (padicValInt 2 a) (padicValInt 2 b) (unitPart 2 a) (unitPart 2 b)
  · simpa only [localClass,hp,ite_false,oddH] using
      odd_parts p (padicValInt p a) (padicValInt p b) hp (unitPart p a) (unitPart p b)
        (unitPart_not_dvd ha) (unitPart_not_dvd hb)

theorem parts_congr (p : ℕ) [Fact p.Prime] {a b : ℤ} (hb : b≠0) (r : ℕ)
    (hr : 0<r) (hd : (p:ℤ)^(padicValInt p b+r) ∣ a-b) :
    a≠0 ∧ padicValInt p a=padicValInt p b ∧ (p:ℤ)^r ∣ unitPart p a-unitPart p b := by
  obtain ⟨t,ht⟩ := hd
  have hp : (p:ℤ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hu : ¬(p:ℤ)∣unitPart p b+(p:ℤ)^r*t := by
    intro h
    apply unitPart_not_dvd (p:=p) hb
    have ht : (p:ℤ)∣(p:ℤ)^r*t := dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _
    convert dvd_sub h ht using 1 <;> ring
  have he : a=(p:ℤ)^padicValInt p b*(unitPart p b+(p:ℤ)^r*t) := by
    rw [pow_add] at ht
    linear_combination ht-unitPart_spec p b
  refine ⟨?_,val_of_parts hu he,?_⟩
  · rw [he]
    exact mul_ne_zero (pow_ne_zero _ hp) (fun h => hu (h ▸ dvd_zero _))
  · rw [unitPart_of_parts hu he]
    exact ⟨t,by ring⟩

def precision (p : ℕ) : ℕ := if p=2 then 3 else 1

theorem class_stable (p : ℕ) [Fact p.Prime] {a b : ℤ} (hb : b≠0) (k : ℕ)
    (hk : padicValInt p b+precision p≤k) (hd : (p:ℤ)^k ∣ a-b) :
    localClass p a=localClass p b := by
  obtain ⟨_,hv,hu⟩ := parts_congr p hb (precision p)
    (by unfold precision; split_ifs <;> decide)
    (dvd_trans (pow_dvd_pow _ hk) hd)
  by_cases hp : p=2
  · subst p
    have hu8 : unitPart 2 a % 8=unitPart 2 b % 8 := by
      have h : (8:ℤ) ∣ unitPart 2 a-unitPart 2 b := by simpa [precision] using hu
      exact (Int.emod_eq_emod_iff_emod_sub_eq_zero).mpr (Int.emod_eq_zero_of_dvd h)
    have hu4 : unitPart 2 a % 4=unitPart 2 b % 4 := by omega
    simp only [localClass,ite_true,hv,hu4,twoChar,hu8]
  · have hup : unitPart p a % p=unitPart p b % p := by
      have h : (p:ℤ)∣unitPart p a-unitPart p b := by simpa [precision,hp] using hu
      exact (Int.emod_eq_emod_iff_emod_sub_eq_zero).mpr (Int.emod_eq_zero_of_dvd h)
    simp only [localClass,hp,ite_false,hv,jacobiSym.mod_left' hup]

theorem low_order_congr (p : ℕ) [Fact p.Prime] {a b : ℤ} (hb : b≠0) (k : ℕ)
    (hk : padicValInt p b<k) (hd : (p:ℤ)^k ∣ a-b) :
    a≠0 ∧ padicValInt p a=padicValInt p b := by
  obtain ⟨hn,hv,_⟩ := parts_congr p hb (k-padicValInt p b) (by omega)
    (by rwa [Nat.add_sub_of_le hk.le])
  exact ⟨hn,hv⟩

theorem finite_lifts (p : ℕ) [Fact p.Prime] {a b : ℤ} (hb : b≠0) (k : ℕ)
    (hk : padicValInt p b<k) (hd : (p:ℤ)^k ∣ a-b) :
    ∃ i : Fin (p^precision p), localClass p a=localClass p (b+(p:ℤ)^k*i.val) := by
  obtain ⟨t,ht⟩ := hd
  have hm : 0<p^precision p := pow_pos (Fact.out : p.Prime).pos _
  let i : Fin (p^precision p) := ⟨(t % (p^precision p:ℕ)).toNat,by
    have := Int.emod_nonneg t (show ((p^precision p:ℕ):ℤ)≠0 by positivity)
    have := Int.emod_lt_of_pos t (show 0<((p^precision p:ℕ):ℤ) by positivity)
    omega⟩
  have hi : (i.val:ℤ)=t % (p^precision p:ℕ) := by
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))
  have hdb : (p:ℤ)^k ∣ (b+(p:ℤ)^k*i.val)-b := ⟨i.val,by ring⟩
  obtain ⟨hb',hv⟩ := low_order_congr p hb k hk hdb
  refine ⟨i,class_stable p hb' (k+precision p) (by rw [hv]; omega) ?_⟩
  refine ⟨t/(p^precision p:ℕ),?_⟩
  rw [hi,pow_add]
  have ht' := Int.emod_add_mul_ediv t ((p^precision p:ℕ):ℤ)
  push_cast at ht'
  push_cast
  linear_combination ht-(p:ℤ)^k*ht'

end GraphCert.RationalClasses

                                                
namespace GraphCert.RationalClasses
open RatHilbert

structure Envelope where
  base : Vector
  directions : Fin 3 → Vector

def Envelope.contains (E : Envelope) (v : Vector) : Prop :=
  ∃ c : Fin 3 → ZMod 2, v=E.base+∑ j, c j • E.directions j

instance (E : Envelope) (v : Vector) : Decidable (E.contains v) :=
  inferInstanceAs (Decidable (∃ c : Fin 3 → ZMod 2, v=E.base+∑ j, c j • E.directions j))

def Envelope.check (E : Envelope) (p k : ℕ) (b : ℤ) : Prop :=
  if b=0 ∨ k≤padicValInt p b then
    ∀ v : Vector, (p=2 ∨ v 2=0) → E.contains v
  else if padicValInt p b+precision p≤k then E.contains (localClass p b)
  else ∀ i : Fin (p^precision p), E.contains (localClass p (b+(p:ℤ)^k*i.val))

instance (E : Envelope) (p k : ℕ) (b : ℤ) : Decidable (E.check p k b) := by
  unfold Envelope.check
  infer_instance

theorem Envelope.check_sound (E : Envelope) (p : ℕ) [Fact p.Prime]
    (k : ℕ) {a b : ℤ} (hd : (p:ℤ)^k ∣ a-b) (he : E.check p k b) :
    E.contains (localClass p a) := by
  unfold Envelope.check at he
  split_ifs at he with hsmall hlarge
  · apply he
    by_cases hp : p=2
    · exact Or.inl hp
    · exact Or.inr (by simp [localClass,hp])
  · have hb : b≠0 := fun h => hsmall (Or.inl h)
    rwa [class_stable p hb k hlarge hd]
  · have hb : b≠0 := fun h => hsmall (Or.inl h)
    have hk : padicValInt p b<k := by omega
    obtain ⟨i,hi⟩ := finite_lifts p hb k hk hd
    rw [hi]
    exact he i

abbrev Edge (n : ℕ) := Fin n × Fin n

def graphForm (p : ℕ) {n m : ℕ} (edges : Fin m → Edge n)
    (H C : Fin n → Vector) : ZMod 2 :=
  (∑ e, (pairing p) (H (edges e).1) (H (edges e).2)) + ∑ i, (pairing p) (H i) (C i)

def star (p : ℕ) {n m : ℕ} (edges : Fin m → Edge n)
    (H C : Fin n → Vector) (i : Fin n) : Vector :=
  C i + ∑ e, ((if (edges e).1=i then H (edges e).2 else 0) +
    (if (edges e).2=i then H (edges e).1 else 0))

def neighbors {n m : ℕ} (edges : Fin m → Edge n) (i : Fin n) : List (Fin n) :=
  (List.finRange m).flatMap fun e =>
    (if (edges e).1=i then [(edges e).2] else []) ++
    (if (edges e).2=i then [(edges e).1] else [])

theorem star_neighbors (p : ℕ) {n m : ℕ} (edges : Fin m → Edge n)
    (H C : Fin n → Vector) (i : Fin n) :
    star p edges H C i = C i + ((neighbors edges i).map H).sum := by
  simp only [star, neighbors, Fin.sum_univ_def]
  congr 1
  generalize List.finRange m = es
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append]
    rw [← ih]
    congr 1
    split_ifs <;> simp

theorem star_pairing (p : ℕ) {n m : ℕ} (edges : Fin m → Edge n)
    (H C d : Fin n → Vector) :
    (∑ i, (pairing p) (d i) (star p edges H C i)) =
      (∑ e, ((pairing p) (d (edges e).1) (H (edges e).2) +
        (pairing p) (H (edges e).1) (d (edges e).2))) + ∑ i, (pairing p) (d i) (C i) := by
  classical
  simp only [star,map_add,map_sum]
  rw [Finset.sum_add_distrib,Finset.sum_comm]
  have he (e : Fin m) :
      (∑ i, ((pairing p) (d i) (if (edges e).1=i then H (edges e).2 else 0) +
        (pairing p) (d i) (if (edges e).2=i then H (edges e).1 else 0))) =
      (pairing p) (d (edges e).1) (H (edges e).2) + (pairing p) (H (edges e).1) (d (edges e).2) := by
    rw [Finset.sum_add_distrib]
    simp only [apply_ite,map_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]
    change form p _ _ + form p _ _ = _
    rw [form_symmetric p (d (edges e).2)]
    rfl
  simp_rw [he]
  ring

theorem graphForm_add (p : ℕ) {n m : ℕ} (edges : Fin m → Edge n)
    (H C d : Fin n → Vector) :
    graphForm p edges (fun i => H i+d i) C = graphForm p edges H C +
      (∑ i, (pairing p) (d i) (star p edges H C i)) +
      ∑ e, (pairing p) (d (edges e).1) (d (edges e).2) := by
  rw [star_pairing p]
  simp only [graphForm,map_add,LinearMap.add_apply,Finset.sum_add_distrib]
  ring

theorem graphForm_constant (p : ℕ) {n m r : ℕ} (edges : Fin m → Edge n)
    (H C : Fin n → Vector) (D : Fin n → Fin r → Vector)
    (hl : ∀ i k, (pairing p) (D i k) (star p edges H C i)=0)
    (hc : ∀ e k l, (pairing p) (D (edges e).1 k) (D (edges e).2 l)=0)
    (a : Fin n → Fin r → ZMod 2) :
    graphForm p edges (fun i => H i+∑ k, a i k • D i k) C = graphForm p edges H C := by
  rw [graphForm_add p]
  have h1 (i : Fin n) : (pairing p) (∑ k, a i k • D i k) (star p edges H C i)=0 := by
    simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,
      hl,smul_zero,Finset.sum_const_zero]
  have h2 (e : Fin m) : (pairing p) (∑ k, a (edges e).1 k • D (edges e).1 k)
      (∑ l, a (edges e).2 l • D (edges e).2 l)=0 := by
    simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,
      hc,smul_zero,Finset.sum_const_zero]
  simp only [h1,h2,Finset.sum_const_zero,add_zero]

theorem graphForm_envelopes (p : ℕ) {n m : ℕ} (edges : Fin m → Edge n)
    (H C : Fin n → Vector) (E : Fin n → Envelope)
    (hH : ∀ i, (E i).contains (H i))
    (hl : ∀ i k, pairing p ((E i).directions k) (star p edges (fun i => (E i).base) C i)=0)
    (hc : ∀ e k l, pairing p ((E (edges e).1).directions k) ((E (edges e).2).directions l)=0) :
    graphForm p edges H C = graphForm p edges (fun i => (E i).base) C := by
  classical
  choose a ha using hH
  rw [funext ha]
  exact graphForm_constant p edges (fun i => (E i).base) C (fun i => (E i).directions) hl hc a

theorem sign_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    sign (∑ i ∈ s, f i)=∏ i ∈ s, sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sign]
  | @insert i s hi ih => rw [Finset.sum_insert hi,sign_add,Finset.prod_insert hi,ih]

def graphArguments {n m : ℕ} (edges : Fin m → Edge n) (H C : Fin n → ℤ) : Quadratic.Arguments :=
  (List.finRange m).map (fun e => (H (edges e).1,H (edges e).2)) ++
    (List.finRange n).map (fun i => (H i,C i))

theorem graphArguments_nonzero {n m : ℕ} (edges : Fin m → Edge n) (H C : Fin n → ℤ)
    (hH : ∀ i, H i≠0) (hC : ∀ i, C i≠0) : Quadratic.Nonzero (graphArguments edges H C) := by
  intro pair hp
  simp only [graphArguments,List.mem_append,List.mem_map] at hp
  rcases hp with ⟨i,_,rfl⟩ | ⟨i,_,rfl⟩
  · exact ⟨hH _,hH _⟩
  · exact ⟨hH _,hC _⟩

theorem graph_value (p : ℕ) [Fact p.Prime] {n m : ℕ}
    (edges : Fin m → Edge n) (H C : Fin n → ℤ)
    (hH : ∀ i, H i≠0) (hC : ∀ i, C i≠0) :
    Quadratic.value (fun a b => if p=2 then twoH a b else oddH p a b)
      (graphArguments edges H C) =
      sign (graphForm p edges (fun i => localClass p (H i)) (fun i => localClass p (C i))) := by
  simp only [Quadratic.value,graphArguments,List.map_append,List.prod_append,List.map_map]
  rw [graphForm,sign_add,sign_sum,sign_sum]
  congr 1
  · rw [← Fin.prod_univ_def]
    apply Finset.prod_congr rfl
    intro i _
    exact symbol_class p (hH _) (hH _)
  · rw [← Fin.prod_univ_def]
    apply Finset.prod_congr rfl
    intro i _
    exact symbol_class p (hH _) (hC _)


def edgeArguments {n m : ℕ} (edges : Fin m → Edge n) (H : Fin n → ℤ) : Quadratic.Arguments :=
  (List.finRange m).map (fun e => (H (edges e).1,H (edges e).2))

theorem edgeArguments_nonzero {n m : ℕ} (edges : Fin m → Edge n) (H : Fin n → ℤ)
    (hH : ∀ i, H i≠0) : Quadratic.Nonzero (edgeArguments edges H) := by
  intro pair hp
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hp
  exact ⟨hH _,hH _⟩

theorem edge_value (p : ℕ) [Fact p.Prime] {n m : ℕ}
    (edges : Fin m → Edge n) (H : Fin n → ℤ) (hH : ∀ i, H i≠0) :
    Quadratic.value (fun a b => if p=2 then twoH a b else oddH p a b)
      (edgeArguments edges H) =
      sign (graphForm p edges (fun i => localClass p (H i)) (fun _ => 0)) := by
  simp only [Quadratic.value,edgeArguments,List.map_map]
  simp only [graphForm,map_zero,Finset.sum_const_zero,add_zero]
  rw [sign_sum,← Fin.prod_univ_def]
  apply Finset.prod_congr rfl
  intro i _
  exact symbol_class p (hH _) (hH _)

theorem eval_congr (F : QuadraticNorm.Coeffs) {m x y a b : ℤ}
    (hx : m∣x-a) (hy : m∣y-b) :
    m∣QuadraticNorm.eval F x y-QuadraticNorm.eval F a b := by
  apply Int.modEq_iff_dvd.mp
  have hx' : a ≡ x [ZMOD m] := Int.modEq_iff_dvd.mpr hx
  have hy' : b ≡ y [ZMOD m] := Int.modEq_iff_dvd.mpr hy
  induction F with
  | nil => exact Int.ModEq.refl _
  | cons term rest ih =>
    rcases term with ⟨i,j,c⟩
    change c*a^i*b^j+QuadraticNorm.eval rest a b ≡
      c*x^i*y^j+QuadraticNorm.eval rest x y [ZMOD m]
    exact (((Int.ModEq.refl c).mul (hx'.pow i)).mul (hy'.pow j)).add ih

end GraphCert.RationalClasses

/- Integer residue lifting. -/
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


namespace GraphCert.Generated.gd2742d1b04aace1cbd711c94

open QuadraticNorm RatHilbert GraphCert.Quadratic PrimeClasses



set_option Elab.async false

without_editor_info def F : Coeffs := [(0,0,2),(0,1,1),(0,3,2),(1,1,1),(4,0,1)]

without_editor_info def equation (x y : ℤ) := eval F x y

without_editor_info def H0 : Coeffs := [(0,0,-2),(0,1,-2)]

without_editor_info def H1 : Coeffs := [(0,0,-1),(0,1,-2),(1,0,1)]

without_editor_info def H2 : Coeffs := [(0,0,1)]

without_editor_info def H3 : Coeffs := [(0,0,2),(0,1,-2),(0,2,4),(1,0,2),(2,0,-4)]

without_editor_info def H4 : Coeffs := [(0,0,-2)]

without_editor_info theorem nonzero0 {x y : ℤ} (hf : equation x y=0) : (eval H0 x y) ≠ 0 := by
  have hc : ∀ a b : ZMod 3, eval F a b=0 → eval H0 a b≠0 := by norm_finite
  intro hz
  apply hc (x:_ ) (y:_)
  · rw [← cast_eval, show eval F x y=0 from hf, Int.cast_zero]
  · rw [← cast_eval,hz,Int.cast_zero]

without_editor_info theorem nonzero1 {x y : ℤ} (hf : equation x y=0) : (eval H1 x y) ≠ 0 := by
  have hc : ∀ a b : ZMod 2, eval F a b=0 → eval H1 a b≠0 := by norm_finite
  intro hz
  apply hc (x:_ ) (y:_)
  · rw [← cast_eval, show eval F x y=0 from hf, Int.cast_zero]
  · rw [← cast_eval,hz,Int.cast_zero]

without_editor_info theorem nonzero2 {x y : ℤ} (hf : equation x y=0) : (eval H2 x y) ≠ 0 := by
  have hc : ∀ a b : ZMod 2, eval F a b=0 → eval H2 a b≠0 := by norm_finite
  intro hz
  apply hc (x:_ ) (y:_)
  · rw [← cast_eval, show eval F x y=0 from hf, Int.cast_zero]
  · rw [← cast_eval,hz,Int.cast_zero]

without_editor_info theorem nonzero3 {x y : ℤ} (hf : equation x y=0) : (eval H3 x y) ≠ 0 := by
  have hc : ∀ a b : ZMod 4, eval F a b=0 → eval H3 a b≠0 := by norm_finite
  intro hz
  apply hc (x:_ ) (y:_)
  · rw [← cast_eval, show eval F x y=0 from hf, Int.cast_zero]
  · rw [← cast_eval,hz,Int.cast_zero]

without_editor_info theorem nonzero4 {x y : ℤ} (hf : equation x y=0) : (eval H4 x y) ≠ 0 := by
  have hc : ∀ a b : ZMod 3, eval F a b=0 → eval H4 a b≠0 := by norm_finite
  intro hz
  apply hc (x:_ ) (y:_)
  · rw [← cast_eval, show eval F x y=0 from hf, Int.cast_zero]
  · rw [← cast_eval,hz,Int.cast_zero]

without_editor_info theorem positive0 {x y : ℤ} (hf : equation x y=0) : 0 < (1:ℤ)*(eval H0 x y) := by
  dsimp [equation,F,H0,eval] at hf ⊢
  let F : QuadraticNorm.Coeffs := [(4, 0, 1), (1, 1, 1), (0, 3, 2), (0, 1, 1), (0, 0, 2)]
  let H0 : QuadraticNorm.Coeffs := [(0, 1, -2), (0, 0, -2)]
  have hf : QuadraticNorm.eval F x y = 0 := by convert hf using 1 <;> norm_polynomial
  have hs : 0 < QuadraticNorm.eval H0 x y := by
    have haux : ∀ x y : ℤ, eval ([(4, 0, 1), (1, 1, -1), (0, 3, -2), (0, 1, -1), (0, 0, 2)] : Coeffs) x y = 0 → 0 < eval ([(0, 1, 2), (0, 0, -2)] : Coeffs) x y := by
      intro x y hf
      let F : Coeffs := [(4, 0, 1), (1, 1, -1), (0, 3, -2), (0, 1, -1), (0, 0, 2)]
      let H0 : Coeffs := [(0, 1, 2), (0, 0, -2)]
      change eval F x y = 0 at hf
      change 0 < eval H0 x y
      have hf' := hf
      dsimp [F,eval,List.map,List.sum,List.foldr] at hf'
      by_contra hn
      have hy : y ≤ 1 := by norm_num [H0,eval] at hn; omega
      by_cases hneg : y ≤ -1
      · have hc : y^3 ≤ -(1:ℤ)*y^2 := by
          nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg y) (show y+1 ≤ 0 by omega)]
        by_cases hx : (10:ℤ)^2 ≤ x^2
        · have hpow : (10:ℤ)^2*x^2 ≤ x^4 := by nlinarith only [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx)]
          nlinarith only [hf',hc,hpow,hx,sq_nonneg ((1 * x + (-4) * y + 1)),sq_nonneg (x+1),sq_nonneg (x-1)]
        · obtain ⟨hx0,hx1⟩ := integer_square_bound x 9 (by norm_num only [Nat.cast_ofNat]; norm_num at hx ⊢; omega)
          interval_cases x
          · have hc : ∀ z : ZMod 2, eval F (-9) z ≠ 0 := by decide +kernel
            have hz : eval F ((-9:ℤ):ZMod 2) (y:ZMod 2) = 0 := by rw [← cast_eval,hf,Int.cast_zero]
            exact hc _ hz
          · have hc : ∀ z : ZMod 7, eval F (-8) z ≠ 0 := by decide +kernel
            have hz : eval F ((-8:ℤ):ZMod 7) (y:ZMod 7) = 0 := by rw [← cast_eval,hf,Int.cast_zero]
            exact hc _ hz
          · have hc : ∀ z : ZMod 2, eval F (-7) z ≠ 0 := by decide +kernel
            have hz : eval F ((-7:ℤ):ZMod 2) (y:ZMod 2) = 0 := by rw [← cast_eval,hf,Int.cast_zero]
            exact hc _ hz
          · have hc : ∀ z : ZMod 3, eval F (-6) z ≠ 0 := by decide +kernel
            have hz : eval F ((-6:ℤ):ZMod 3) (y:ZMod 3) = 0 := by rw [← cast_eval,hf,Int.cast_zero]
            exact hc _ hz
          · have hc : ∀ z : ZMod 2, eval F (-5) z ≠ 0 := by decide +kernel
            have hz : eval F ((-5:ℤ):ZMod 2) (y:ZMod 2) = 0 := by rw [← cast_eval,hf,Int.cast_zero]
            exact hc _ hz
          · have hc : ∀ z : ZMod 5, eval F (-4) z ≠ 0 := by decide +kernel
            have hz : eval F ((-4:ℤ):ZMod 5) (y:ZMod 5) = 0 := by rw [← cast_eval,hf,Int.cast_zero]
            exact hc _ hz
          · have hc : ∀ z : ZMod 2, eval F (-3) z ≠ 0 := by decide +kernel
            have hz : eval F ((-3:ℤ):ZMod 2) (y:ZMod 2) = 0 := by rw [← cast_eval,hf,Int.cast_zero]
            exact hc _ hz
          · have hc : ∀ z : ZMod 5, eval F (-2) z ≠ 0 := by decide +kernel
            have hz : eval F ((-2:ℤ):ZMod 5) (y:ZMod 5) = 0 := by rw [← cast_eval,hf,Int.cast_zero]
            exact hc _ hz
          · have hc : ∀ z : ZMod 2, eval F (-1) z ≠ 0 := by decide +kernel
            have hz : eval F ((-1:ℤ):ZMod 2) (y:ZMod 2) = 0 := by rw [← cast_eval,hf,Int.cast_zero]
            exact hc _ hz
          · have hc : ∀ z : ZMod 3, eval F (0) z ≠ 0 := by decide +kernel
            have hz : eval F ((0:ℤ):ZMod 3) (y:ZMod 3) = 0 := by rw [← cast_eval,hf,Int.cast_zero]
            exact hc _ hz
          · have hc : ∀ z : ZMod 2, eval F (1) z ≠ 0 := by decide +kernel
            have hz : eval F ((1:ℤ):ZMod 2) (y:ZMod 2) = 0 := by rw [← cast_eval,hf,Int.cast_zero]
            exact hc _ hz
          · have hc : ∀ z : ZMod 7, eval F (2) z ≠ 0 := by decide +kernel
            have hz : eval F ((2:ℤ):ZMod 7) (y:ZMod 7) = 0 := by rw [← cast_eval,hf,Int.cast_zero]
            exact hc _ hz
          · have hc : ∀ z : ZMod 2, eval F (3) z ≠ 0 := by decide +kernel
            have hz : eval F ((3:ℤ):ZMod 2) (y:ZMod 2) = 0 := by rw [← cast_eval,hf,Int.cast_zero]
            exact hc _ hz
          · have hc : ∀ z : ZMod 19, eval F (4) z ≠ 0 := by decide +kernel
            have hz : eval F ((4:ℤ):ZMod 19) (y:ZMod 19) = 0 := by rw [← cast_eval,hf,Int.cast_zero]
            exact hc _ hz
          · have hc : ∀ z : ZMod 2, eval F (5) z ≠ 0 := by decide +kernel
            have hz : eval F ((5:ℤ):ZMod 2) (y:ZMod 2) = 0 := by rw [← cast_eval,hf,Int.cast_zero]
            exact hc _ hz
          · have hc : ∀ z : ZMod 3, eval F (6) z ≠ 0 := by decide +kernel
            have hz : eval F ((6:ℤ):ZMod 3) (y:ZMod 3) = 0 := by rw [← cast_eval,hf,Int.cast_zero]
            exact hc _ hz
          · have hc : ∀ z : ZMod 2, eval F (7) z ≠ 0 := by decide +kernel
            have hz : eval F ((7:ℤ):ZMod 2) (y:ZMod 2) = 0 := by rw [← cast_eval,hf,Int.cast_zero]
            exact hc _ hz
          · have hc : ∀ z : ZMod 5, eval F (8) z ≠ 0 := by decide +kernel
            have hz : eval F ((8:ℤ):ZMod 5) (y:ZMod 5) = 0 := by rw [← cast_eval,hf,Int.cast_zero]
            exact hc _ hz
          · have hc : ∀ z : ZMod 2, eval F (9) z ≠ 0 := by decide +kernel
            have hz : eval F ((9:ℤ):ZMod 2) (y:ZMod 2) = 0 := by rw [← cast_eval,hf,Int.cast_zero]
            exact hc _ hz
      · have hlo : -1+1 ≤ y := by omega
        interval_cases y
        · have hc : ∀ z : ZMod 5, eval F z (0) ≠ 0 := by decide +kernel
          have hz : eval F (x:ZMod 5) ((0:ℤ):ZMod 5) = 0 := by rw [← cast_eval,hf,Int.cast_zero]
          exact hc _ hz
        · have hc : ∀ z : ZMod 2, eval F z (1) ≠ 0 := by decide +kernel
          have hz : eval F (x:ZMod 2) ((1:ℤ):ZMod 2) = 0 := by rw [← cast_eval,hf,Int.cast_zero]
          exact hc _ hz
    have hz : eval ([(4, 0, 1), (1, 1, -1), (0, 3, -2), (0, 1, -1), (0, 0, 2)] : Coeffs) x (-y) = 0 := by convert hf using 1 <;> norm_polynomial
    have hh := haux x (-y) hz
    convert hh using 1 <;> norm_polynomial
  convert hs using 1 <;> norm_polynomial

without_editor_info theorem positive1 {x y : ℤ} (hf : equation x y=0) : 0 < (1:ℤ)*(eval H1 x y) := by
  dsimp [equation,F,H1,eval] at hf ⊢
  let F : QuadraticNorm.Coeffs := [(4, 0, 1), (1, 1, 1), (0, 3, 2), (0, 1, 1), (0, 0, 2)]
  let H0 : QuadraticNorm.Coeffs := [(1, 0, 1), (0, 1, -2), (0, 0, -1)]
  have hf : QuadraticNorm.eval F x y = 0 := by convert hf using 1 <;> norm_polynomial
  have hs : 0 < QuadraticNorm.eval H0 x y := by
    have hd : 32 * (2 * x^2 + 4 * x * y + 8 * y^2 + (-4) * y + 6) = ((4 * x + 16 * y + (-4)))^2 + (48 * x^2 + 32 * x + 176) := by ring
    have he : eval H0 x y * (2 * x^2 + 4 * x * y + 8 * y^2 + (-4) * y + 6) = (8 * x^4 + 2 * x^3 + (-2) * x^2 + 6 * x + 10) := by
      linear_combination (norm := norm_polynomial) ((-8)) * hf
    have hpd : (0 : ℤ) < (8 * x^4 + 2 * x^3 + (-2) * x^2 + 6 * x + 10) ∧ (0 : ℤ) < (48 * x^2 + 32 * x + 176) := by
      by_cases hx : x ≤ -1
      · have harg : 0 ≤ ((-1) * x + (-1)) := by omega
        constructor
        · have hz : (8 * x^4 + 2 * x^3 + (-2) * x^2 + 6 * x + 10) = 8 * (((-1) * x + (-1)))^4 + 30 * (((-1) * x + (-1)))^3 + 40 * (((-1) * x + (-1)))^2 + 16 * (((-1) * x + (-1)))^1 + 8 * (((-1) * x + (-1)))^0 := by ring
          rw [hz]; positivity
        · have hz : (48 * x^2 + 32 * x + 176) = 48 * (((-1) * x + (-1)))^2 + 64 * (((-1) * x + (-1)))^1 + 192 * (((-1) * x + (-1)))^0 := by ring
          rw [hz]; positivity
      by_cases hx : 1 ≤ x
      · have harg : 0 ≤ (1 * x + (-1)) := by omega
        constructor
        · have hz : (8 * x^4 + 2 * x^3 + (-2) * x^2 + 6 * x + 10) = 8 * ((1 * x + (-1)))^4 + 34 * ((1 * x + (-1)))^3 + 52 * ((1 * x + (-1)))^2 + 40 * ((1 * x + (-1)))^1 + 24 * ((1 * x + (-1)))^0 := by ring
          rw [hz]; positivity
        · have hz : (48 * x^2 + 32 * x + 176) = 48 * ((1 * x + (-1)))^2 + 128 * ((1 * x + (-1)))^1 + 256 * ((1 * x + (-1)))^0 := by ring
          rw [hz]; positivity
      interval_cases x
      · norm_num
    have ht : 0 < (2 * x^2 + 4 * x * y + 8 * y^2 + (-4) * y + 6) := by
      have hsum := add_pos_of_nonneg_of_pos (sq_nonneg ((4 * x + 16 * y + (-4)))) hpd.2
      rw [← hd] at hsum
      exact (mul_pos_iff_of_pos_left (by norm_num)).mp hsum
    have hprod : 0 < eval H0 x y * (2 * x^2 + 4 * x * y + 8 * y^2 + (-4) * y + 6) := by rw [he]; exact hpd.1
    exact (mul_pos_iff_of_pos_right ht).mp hprod
  convert hs using 1 <;> norm_polynomial

without_editor_info theorem positive2 {x y : ℤ} (hf : equation x y=0) : 0 < (1:ℤ)*(eval H2 x y) := by
  dsimp [equation,F,H2,eval] at hf ⊢
  norm_num [equation, H2, eval]

without_editor_info theorem positive3 {x y : ℤ} (hf : equation x y=0) : 0 < (1:ℤ)*(eval H3 x y) := by
  dsimp [equation,F,H3,eval] at hf ⊢
  let F : Coeffs := [(4,0,1),(1,1,1),(0,3,2),(0,1,1),(0,0,2)]
  let HH : Coeffs := [(2,0,-4),(1,0,2),(0,2,4),(0,1,-2),(0,0,2)]
  let P : Coeffs := [(1,0,2),(0,1,2),(0,0,-1)]
  let Q : Coeffs := [(1,0,-1),(0,1,1)]
  have hf : eval F x y=0 := by convert hf using 1 <;> norm_polynomial
  suffices hpos : 0<eval HH x y by convert hpos using 1 <;> norm_polynomial
  by_contra hn
  have he : (1:ℤ)*eval HH x y=2*eval P x y*eval Q x y+2 := by norm_polynomial
  have hm : eval P x y*eval Q x y<0 := by nlinarith only [he,hn]
  rcases mul_neg_iff.mp hm with ⟨hp,hq⟩ | ⟨hp,hq⟩
  · let u := (1:ℤ)*eval P x y-1
    let v := (-1:ℤ)*eval Q x y-1
    have hu : 0≤u := by dsimp [u]; omega
    have hv : 0≤v := by dsimp [v]; omega
    let G : Coeffs := [(4,0,1),(3,1,8),(3,0,24),(2,2,24),(2,1,48),(2,0,112),(1,3,32),(1,2,288),(1,1,384),(1,0,384),(0,4,16),(0,3,64),(0,2,320),(0,1,256),(0,0,768)]
    have hc : ∀ x y : ℤ, 0≤x → 0≤y → eval G x y≠0 := by
      intro x y hx hy
      have hx0 : 0≤x-0 := by omega
      have hy0 : 0≤y-0 := by omega
      have he : (1:ℤ)*eval G x y = (1:ℤ)*(x-0)^4*(y-0)^0 + (8:ℤ)*(x-0)^3*(y-0)^1 + (24:ℤ)*(x-0)^3*(y-0)^0 + (24:ℤ)*(x-0)^2*(y-0)^2 + (48:ℤ)*(x-0)^2*(y-0)^1 + (112:ℤ)*(x-0)^2*(y-0)^0 + (32:ℤ)*(x-0)^1*(y-0)^3 + (288:ℤ)*(x-0)^1*(y-0)^2 + (384:ℤ)*(x-0)^1*(y-0)^1 + (384:ℤ)*(x-0)^1*(y-0)^0 + (16:ℤ)*(x-0)^0*(y-0)^4 + (64:ℤ)*(x-0)^0*(y-0)^3 + (320:ℤ)*(x-0)^0*(y-0)^2 + (256:ℤ)*(x-0)^0*(y-0)^1 + (768:ℤ)*(x-0)^0*(y-0)^0 := by norm_polynomial
      have hp : 0<(1:ℤ)*eval G x y := by rw [he]; positivity
      intro hz; rw [hz] at hp; norm_num at hp
    apply hc u v hu hv
    have hh : (256:ℤ)*eval F x y=eval G u v := by norm_polynomial
    rw [hf,mul_zero] at hh
    exact hh.symm
  · let u := (-1:ℤ)*eval P x y-1
    let v := (1:ℤ)*eval Q x y-1
    have hu : 0≤u := by dsimp [u]; omega
    have hv : 0≤v := by dsimp [v]; omega
    let G : Coeffs := [(4,0,1),(3,1,8),(2,2,24),(2,1,96),(2,0,88),(1,3,32),(1,1,-96),(1,0,-128),(0,4,16),(0,3,128),(0,2,224),(0,1,256),(0,0,656)]
    have hc : ∀ x y : ℤ, 0≤x → 0≤y → eval G x y≠0 := by
      intro x y hx hy
      by_cases hxn : 1≤x
      · by_cases hyn : 1≤y
        · have hx0 : 0≤x-1 := by omega
          have hy0 : 0≤y-1 := by omega
          have he : (1:ℤ)*eval G x y = (1:ℤ)*(x-1)^4*(y-1)^0 + (8:ℤ)*(x-1)^3*(y-1)^1 + (12:ℤ)*(x-1)^3*(y-1)^0 + (24:ℤ)*(x-1)^2*(y-1)^2 + (168:ℤ)*(x-1)^2*(y-1)^1 + (238:ℤ)*(x-1)^2*(y-1)^0 + (32:ℤ)*(x-1)^1*(y-1)^3 + (144:ℤ)*(x-1)^1*(y-1)^2 + (312:ℤ)*(x-1)^1*(y-1)^1 + (252:ℤ)*(x-1)^1*(y-1)^0 + (16:ℤ)*(x-1)^0*(y-1)^4 + (224:ℤ)*(x-1)^0*(y-1)^3 + (824:ℤ)*(x-1)^0*(y-1)^2 + (1304:ℤ)*(x-1)^0*(y-1)^1 + (1305:ℤ)*(x-1)^0*(y-1)^0 := by norm_polynomial
          have hp : 0<(1:ℤ)*eval G x y := by rw [he]; positivity
          intro hz; rw [hz] at hp; norm_num at hp
        · have hyb : y≤0 := by omega
          interval_cases y
          · have hx0 : 0≤x-1 := by omega
            have he : (1:ℤ)*eval G x (0:ℤ) = (1:ℤ)*(x-1)^4*0^0 + (4:ℤ)*(x-1)^3*0^0 + (94:ℤ)*(x-1)^2*0^0 + (52:ℤ)*(x-1)^1*0^0 + (617:ℤ)*(x-1)^0*0^0 := by norm_polynomial
            have hp : 0<(1:ℤ)*eval G x (0:ℤ) := by rw [he]; positivity
            intro hz; rw [hz] at hp; norm_num at hp
      · have hxb : x≤0 := by omega
        interval_cases x
        · by_cases hyn : 1≤y
          · have hy0 : 0≤y-1 := by omega
            have he : (1:ℤ)*eval G (0:ℤ) y = (16:ℤ)*0^0*(y-1)^4 + (192:ℤ)*0^0*(y-1)^3 + (704:ℤ)*0^0*(y-1)^2 + (1152:ℤ)*0^0*(y-1)^1 + (1280:ℤ)*0^0*(y-1)^0 := by norm_polynomial
            have hp : 0<(1:ℤ)*eval G (0:ℤ) y := by rw [he]; positivity
            intro hz; rw [hz] at hp; norm_num at hp
          · have hyb : y≤0 := by omega
            interval_cases y
            · norm_num [G,eval]
    apply hc u v hu hv
    have hh : (256:ℤ)*eval F x y=eval G u v := by norm_polynomial
    rw [hf,mul_zero] at hh
    exact hh.symm

without_editor_info theorem positive4 {x y : ℤ} (hf : equation x y=0) : 0 < (-1:ℤ)*(eval H4 x y) := by
  dsimp [equation,F,H4,eval] at hf ⊢
  norm_num [equation, H4, eval]

without_editor_info def nodeValues (x y : ℤ) : Fin 5 → ℤ := (fun i => (#[(eval H0 x y),(eval H1 x y),(eval H2 x y),(eval H3 x y),(eval H4 x y)] : Array (ℤ))[i.val]'(by simpa using i.isLt))

without_editor_info theorem nodeValues_nonzero {x y : ℤ} (hf : equation x y=0) : ∀ i : Fin 5, nodeValues x y i≠0 := by
  intro i
  fin_cases i
  · exact nonzero0 hf
  · exact nonzero1 hf
  · exact nonzero2 hf
  · exact nonzero3 hf
  · exact nonzero4 hf

without_editor_info def arguments0 (x y : ℤ) : Arguments := [((eval H0 x y),(eval H1 x y))]

without_editor_info theorem arguments_nonzero0 {x y : ℤ} (hf : equation x y=0) : Nonzero (arguments0 x y) := by
  exact GraphCert.RationalClasses.edgeArguments_nonzero (n:=5) (m:=1) ((fun i => (#[(0,1)] : Array (GraphCert.RationalClasses.Edge 5))[i.val]'(by simpa using i.isLt))) (nodeValues x y) (nodeValues_nonzero hf)

without_editor_info def arguments1 (x y : ℤ) : Arguments := [((eval H3 x y),(eval H4 x y))]

without_editor_info theorem arguments_nonzero1 {x y : ℤ} (hf : equation x y=0) : Nonzero (arguments1 x y) := by
  exact GraphCert.RationalClasses.edgeArguments_nonzero (n:=5) (m:=1) ((fun i => (#[(3,4)] : Array (GraphCert.RationalClasses.Edge 5))[i.val]'(by simpa using i.isLt))) (nodeValues x y) (nodeValues_nonzero hf)

namespace Reflection.Dense

without_editor_info abbrev Poly := List ℤ

without_editor_info def add : Poly → Poly → Poly
  | [],b => b
  | a,[] => a
  | a::as,b::bs => (a+b)::add as bs

without_editor_info def scale (a : ℤ) (b : Poly) : Poly := b.map (a*·)

without_editor_info def neg (a : Poly) : Poly := scale (-1) a

without_editor_info def sub (a b : Poly) : Poly := add a (neg b)

without_editor_info def mul : Poly → Poly → Poly
  | [],_ => []
  | a::as,b => add (scale a b) (0::mul as b)

without_editor_info def pow (a : Poly) : ℕ → Poly
  | 0 => [1]
  | n+1 => mul (pow a n) a

without_editor_info def eval {R : Type*} [CommRing R] (f : ℤ →+* R) : Poly → R → R
  | [],_ => 0
  | a::as,t => f a+t*eval f as t

without_editor_info theorem eval_add {R : Type*} [CommRing R] (f : ℤ →+* R) (a b : Poly) (t : R) :
    eval f (add a b) t=eval f a t+eval f b t := by
  induction a generalizing b with
  | nil => simp [add,eval]
  | cons a as ih =>
    cases b with
    | nil => simp [add,eval]
    | cons b bs => simp only [add,eval,map_add,ih]; ring

without_editor_info theorem eval_scale {R : Type*} [CommRing R] (f : ℤ →+* R) (a : ℤ) (b : Poly) (t : R) :
    eval f (scale a b) t=f a*eval f b t := by
  induction b with
  | nil => simp [scale,eval]
  | cons b bs ih => simp only [scale,List.map_cons,eval,map_mul] at *; rw [ih]; ring

without_editor_info theorem eval_neg {R : Type*} [CommRing R] (f : ℤ →+* R) (a : Poly) (t : R) :
    eval f (neg a) t= -eval f a t := by simp [neg,eval_scale]

without_editor_info theorem eval_sub {R : Type*} [CommRing R] (f : ℤ →+* R) (a b : Poly) (t : R) :
    eval f (sub a b) t=eval f a t-eval f b t := by simp [sub,eval_add,eval_neg,sub_eq_add_neg]

without_editor_info theorem eval_mul {R : Type*} [CommRing R] (f : ℤ →+* R) (a b : Poly) (t : R) :
    eval f (mul a b) t=eval f a t*eval f b t := by
  induction a with
  | nil => simp [mul,eval]
  | cons a as ih => rw [mul,eval_add,eval_scale]; simp only [eval,map_zero,zero_add,ih]; ring

without_editor_info theorem eval_pow {R : Type*} [CommRing R] (f : ℤ →+* R) (a : Poly) (n : ℕ) (t : R) :
    eval f (pow a n) t=(eval f a t)^n := by
  induction n with
  | zero => simp [pow,eval]
  | succ n ih => rw [pow,eval_mul,ih,pow_succ]

without_editor_info def equal (a b : Poly) : Bool := (sub a b).all (· == 0)

without_editor_info theorem eval_of_all_zero {R : Type*} [CommRing R] (f : ℤ →+* R) (a : Poly)
    (ha : a.all (· == 0)=true) (t : R) : eval f a t=0 := by
  induction a with
  | nil => rfl
  | cons a as ih =>
    simp only [List.all_cons,Bool.and_eq_true,beq_iff_eq] at ha
    simp only [eval,ha.1,map_zero,ih ha.2,mul_zero,add_zero]

without_editor_info theorem eval_equal {R : Type*} [CommRing R] (f : ℤ →+* R) (a b : Poly)
    (h : equal a b=true) (t : R) : eval f a t=eval f b t := by
  exact sub_eq_zero.mp ((eval_sub f a b t).symm.trans (eval_of_all_zero f _ h t))

without_editor_info def X : Poly := [0,1]

end Reflection.Dense

namespace Reflection

without_editor_info abbrev Poly := List Dense.Poly

without_editor_info def add : Poly → Poly → Poly
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => Dense.add a b :: add as bs

without_editor_info def scale (a : Dense.Poly) (b : Poly) : Poly := b.map (Dense.mul a)

without_editor_info def neg (a : Poly) : Poly := a.map Dense.neg

without_editor_info def sub (a b : Poly) : Poly := add a (neg b)

without_editor_info def mul : Poly → Poly → Poly
  | [], _ => []
  | a :: as, b => add (scale a b) ([] :: mul as b)

without_editor_info def pow (a : Poly) : ℕ → Poly
  | 0 => [[1]]
  | n+1 => mul (pow a n) a

without_editor_info def eval {R : Type*} [CommRing R] (f : ℤ →+* R) : Poly → R → R → R
  | [], _, _ => 0
  | a :: as, x, y => Dense.eval f a y + x * eval f as x y

without_editor_info theorem eval_add {R : Type*} [CommRing R] (f : ℤ →+* R)
    (a b : Poly) (x y : R) : eval f (add a b) x y = eval f a x y + eval f b x y := by
  induction a generalizing b with
  | nil => simp [add, eval]
  | cons a as ih =>
    cases b with
    | nil => simp [add, eval]
    | cons b bs => simp only [add, eval, Dense.eval_add, ih]; ring

without_editor_info theorem eval_scale {R : Type*} [CommRing R] (f : ℤ →+* R)
    (a : Dense.Poly) (b : Poly) (x y : R) :
    eval f (scale a b) x y = Dense.eval f a y * eval f b x y := by
  induction b with
  | nil => simp [scale, eval]
  | cons b bs ih => simp only [scale, List.map_cons, eval, Dense.eval_mul] at *; rw [ih]; ring

without_editor_info theorem eval_neg {R : Type*} [CommRing R] (f : ℤ →+* R)
    (a : Poly) (x y : R) : eval f (neg a) x y = -eval f a x y := by
  induction a with
  | nil => simp [neg, eval]
  | cons a as ih => simp only [neg, List.map_cons, eval, Dense.eval_neg] at *; rw [ih]; ring

without_editor_info theorem eval_sub {R : Type*} [CommRing R] (f : ℤ →+* R)
    (a b : Poly) (x y : R) : eval f (sub a b) x y = eval f a x y - eval f b x y := by
  simp [sub, eval_add, eval_neg, sub_eq_add_neg]

without_editor_info theorem eval_mul {R : Type*} [CommRing R] (f : ℤ →+* R)
    (a b : Poly) (x y : R) : eval f (mul a b) x y = eval f a x y * eval f b x y := by
  induction a with
  | nil => simp [mul, eval]
  | cons a as ih =>
    rw [mul, eval_add, eval_scale]
    simp only [eval, Dense.eval, zero_add, ih]
    ring

without_editor_info theorem eval_pow {R : Type*} [CommRing R] (f : ℤ →+* R)
    (a : Poly) (k : ℕ) (x y : R) : eval f (pow a k) x y = eval f a x y ^ k := by
  induction k with
  | zero => simp [pow, eval, Dense.eval]
  | succ k ih => rw [pow, eval_mul, ih, pow_succ]

without_editor_info def equal (a b : Poly) : Bool := (sub a b).all (fun row => Dense.equal row [])

without_editor_info theorem eval_zero {R : Type*} [CommRing R] (f : ℤ →+* R)
    (a : Poly) (h : a.all (fun row => Dense.equal row []) = true) (x y : R) :
    eval f a x y = 0 := by
  induction a with
  | nil => rfl
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [eval, Dense.eval_equal f a [] h.1 y, Dense.eval, ih h.2, mul_zero, add_zero]

without_editor_info theorem eval_equal {R : Type*} [CommRing R] (f : ℤ →+* R)
    (a b : Poly) (h : equal a b = true) (x y : R) : eval f a x y = eval f b x y := by
  exact sub_eq_zero.mp ((eval_sub f a b x y).symm.trans (eval_zero f _ h x y))

without_editor_info def constant (c : ℤ) : Poly := [[c]]

without_editor_info theorem eval_constant {R : Type*} [CommRing R] (f : ℤ →+* R)
    (c : ℤ) (x y : R) : eval f (constant c) x y = f c := by
  simp [constant, eval, Dense.eval]

without_editor_info def monomial (i j : ℕ) (a : ℤ) : Poly :=
  List.replicate i [] ++ [List.replicate j 0 ++ [a]]

without_editor_info theorem eval_monomial (i j : ℕ) (a x y : ℤ) :
    eval (RingHom.id ℤ) (monomial i j a) x y = a*x^i*y^j := by
  have hd (k : ℕ) : Dense.eval (RingHom.id ℤ) (List.replicate k 0 ++ [a]) y = a*y^k := by
    induction k with
    | zero => simp [Dense.eval]
    | succ k ih => simp [List.replicate_succ, Dense.eval, ih, pow_succ]; ring
  induction i with
  | zero => simp [monomial, eval, hd]
  | succ i ih =>
    change 0 + x * eval (RingHom.id ℤ) (monomial i j a) x y = _
    rw [ih, pow_succ]
    ring

without_editor_info def ofCoeffs : QuadraticNorm.Coeffs → Poly
  | [] => []
  | (i,j,a)::cs => add (monomial i j a) (ofCoeffs cs)

without_editor_info theorem eval_ofCoeffs (cs : QuadraticNorm.Coeffs) (x y : ℤ) :
    eval (RingHom.id ℤ) (ofCoeffs cs) x y = QuadraticNorm.eval cs x y := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    obtain ⟨i,j,a⟩ := c
    simpa [ofCoeffs, eval_add, eval_monomial, QuadraticNorm.eval] using ih

end Reflection

without_editor_info def star0_0 (x y : ℤ) := (eval H2 x y) * (eval H1 x y)

without_editor_info def W0_0 : Coeffs := [(2,0,-2)]

without_editor_info def A0_0 : Coeffs := [(0,0,-4)]

without_editor_info def B0_0 : Coeffs := [(0,0,-2),(0,1,4),(0,2,-4),(1,0,-2)]

without_editor_info theorem star_identity0_0 (x y : ℤ) :
    (2:ℤ)^2*star0_0 x y-(eval W0_0 x y)^2 =
      equation x y*eval A0_0 x y + (eval H0 x y)*eval B0_0 x y := by simp [equation,F,star0_0,W0_0,A0_0,B0_0,H0,H1,H2,eval] <;> ring

without_editor_info def star0_1 (x y : ℤ) := (eval H2 x y) * (eval H0 x y)

without_editor_info def W0_1 : Coeffs := [(0,0,1),(1,0,-14),(2,0,-7),(3,0,-12)]

without_editor_info def A0_1 : Coeffs := [(0,0,-352),(0,1,72),(1,0,-168),(2,0,-144)]

without_editor_info def B0_1 : Coeffs := [(0,0,265),(0,1,230),(0,2,-388),(0,3,72),(1,0,-99),(1,1,-92),(1,2,-132),(2,0,-205),(2,1,6),(2,2,-144),(3,0,-33),(3,1,-72)]

without_editor_info theorem star_identity0_1 (x y : ℤ) :
    (22:ℤ)^2*star0_1 x y-(eval W0_1 x y)^2 =
      equation x y*eval A0_1 x y + (eval H1 x y)*eval B0_1 x y := by simp [equation,F,star0_1,W0_1,A0_1,B0_1,H0,H1,H2,eval] <;> ring

without_editor_info def bezA0_0 : Coeffs := [(0,0,2)]

without_editor_info def bezB0_0 : Coeffs := [(0,0,-1),(0,1,-2),(0,2,2),(1,0,3),(2,0,-2),(3,0,2)]

without_editor_info def bezC0_0 : Coeffs := [(0,0,4),(1,0,-2),(2,0,2),(3,0,-2)]

without_editor_info theorem separation0_0 (x y : ℤ) :
    equation x y*eval bezA0_0 x y+(eval H0 x y)*eval bezB0_0 x y+
      (eval H1 x y)*eval bezC0_0 x y=(2:ℤ) := by simp [equation,F,H0,H1,bezA0_0,bezB0_0,bezC0_0,eval] <;> ring

without_editor_info theorem ordinary_support0 {x y : ℤ} (hf : equation x y=0) (p : ℕ)
    (hp : p.Prime) (hp2 : p≠2) (hpE : p∉({11}:Finset ℕ)) : value (oddH p) (arguments0 x y)=1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpZ : Prime (p:ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hN : ¬ (p:ℤ) ∣ 22 := by
    intro hd
    have hn : p∣22 := by exact_mod_cast hd
    have hm : p ∈ Nat.primeFactors 22 := Nat.mem_primeFactors.mpr ⟨hp,hn,by decide⟩
    have he : Nat.primeFactors 22 = ({2,11}:Finset ℕ) := by decide +kernel
    rw [he] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact hp2 rfl
    · exact hpE (by simp)
  have supported (a b : ℤ) (he : a*b=(22:ℤ)^1) : ¬(p:ℤ) ∣ a := by
    intro hd
    apply hN
    apply hpZ.dvd_of_dvd_pow
    rw [← he]
    exact dvd_mul_of_dvd_left hd _
  have hc0 : ¬(p:ℤ)∣(eval H2 x y) := by
    apply supported _ (22:ℤ)
    norm_num [H2,eval]
  have hc1 : ¬(p:ℤ)∣(eval H2 x y) := by
    apply supported _ (22:ℤ)
    norm_num [H2,eval]
  have unit_symbol2 : jacobiSym (eval H2 x y) p=1 := by norm_num [H2,eval]
  have sep0 : ¬((p:ℤ)∣(eval H0 x y) ∧ (p:ℤ)∣(eval H1 x y)) :=
    separate_of_identity hf (supported 2 (11) (by norm_num)) (separation0_0 x y)
  have hs0 (hi : (p:ℤ)∣(eval H0 x y)) : jacobiSym (star0_0 x y) p=1 := by
    have hn1 : ¬(p:ℤ)∣(eval H1 x y) := fun hj => sep0 ⟨hi,hj⟩
    have hn : ¬(p:ℤ)∣star0_0 x y := by
      simpa only [star0_0, hpZ.dvd_mul, not_or] using ⟨hc0,hn1⟩
    apply LocalSymbols.jacobi_square_mod _ hn
    exact square_of_identity hf hi (supported 2 (11) (by norm_num)) (star_identity0_0 x y)
  have hs1 (hi : (p:ℤ)∣(eval H1 x y)) : jacobiSym (star0_1 x y) p=1 := by
    have hn0 : ¬(p:ℤ)∣(eval H0 x y) := fun hj => sep0 ⟨hj,hi⟩
    have hn : ¬(p:ℤ)∣star0_1 x y := by
      simpa only [star0_1, hpZ.dvd_mul, not_or] using ⟨hc1,hn0⟩
    apply LocalSymbols.jacobi_square_mod _ hn
    exact square_of_identity hf hi (supported 22 (1) (by norm_num)) (star_identity0_1 x y)
  have expand : value (oddH p) (arguments0 x y) = jacobiSym (star0_0 x y) p ^ padicValInt p (eval H0 x y) * jacobiSym (star0_1 x y) p ^ padicValInt p (eval H1 x y) := by
    simp only [value,arguments0,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    rw [odd_edge (eval H0 x y) (eval H1 x y) sep0]
    simp only [star0_0, star0_1, jacobiSym.mul_left, mul_pow]
    simp only [padicValInt.eq_zero_of_not_dvd hc0, padicValInt.eq_zero_of_not_dvd hc1, unit_symbol2, pow_zero, one_pow, mul_one, one_mul] <;> ring
  rw [expand]
  rw [star_term (eval H0 x y) (star0_0 x y) hs0, star_term (eval H1 x y) (star0_1 x y) hs1] <;> norm_num

without_editor_info theorem ordinary0 {x y : ℤ} (hf : equation x y=0) (p : ℕ)
    (hp : p.Prime) (hp2 : p≠2) (hpE : p∉({11,457}:Finset ℕ)) : value (oddH p) (arguments0 x y)=1 := by
  apply ordinary_support0 hf p hp hp2
  intro h
  apply hpE
  simp_all only [Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty] <;> tauto

without_editor_info def star1_0 (x y : ℤ) := (eval H4 x y)

without_editor_info def W1_0 : Coeffs := [(0,0,-954),(1,0,-306),(2,0,-2230),(3,0,-1048),(4,0,292),(5,0,160),(6,0,-336),(7,0,-128)]

without_editor_info def A1_0 : Coeffs := [(0,0,-1374180),(0,1,1797664),(0,2,-958304),(0,3,3987104),(0,4,-901376),(0,5,2066432),(0,6,-484352),(0,7,131072),(1,0,1346144),(1,1,1824624),(1,2,2976320),(1,3,3806208),(1,4,1056256),(1,5,819200),(1,6,-344064),(2,0,-209360),(2,1,1056640),(2,2,-260352),(2,3,64256),(2,4,-409600),(2,6,-65536),(3,0,-4841280),(3,1,-1652608),(3,2,-1864192),(3,3,-364544),(3,4,-65536),(4,0,-1125584),(4,1,-929536),(4,2,-16384),(4,3,143872),(5,0,-1196544),(5,1,157952),(5,3,172032),(6,0,-64896),(6,1,102400),(6,3,32768),(7,0,182272),(7,1,16384),(8,0,-71936),(9,0,-86016),(10,0,-16384)]

without_editor_info def B1_0 : Coeffs := [(0,0,83726),(0,1,-1026848),(0,2,-1134828),(0,3,-1214904),(0,4,-1835088),(0,5,-62720),(0,6,-928512),(0,7,209408),(0,8,-65536),(1,0,-1721794),(1,1,-2505552),(1,2,-2714600),(1,3,-2649952),(1,4,-2163200),(1,5,-673536),(1,6,-323584),(1,7,172032),(2,0,-75632),(2,1,-1248808),(2,2,-1832880),(2,3,-328000),(2,4,-751488),(2,5,389632),(2,6,-49152),(2,7,32768),(3,0,-208848),(3,1,206784),(3,2,-809664),(3,3,72960),(3,4,-14336),(3,5,204800),(4,0,-658312),(4,1,-348576),(4,2,-101440),(4,3,-204800),(5,0,-1330960),(5,1,-478016),(5,2,-436352),(6,0,14336),(6,1,-204800)]

without_editor_info def dense_W1_0 : Reflection.Poly := [[(-954)],[(-306)],[(-2230)],[(-1048)],[292],[160],[(-336)],[(-128)]]

without_editor_info theorem link_W1_0 (x y : ℤ) : Reflection.eval (RingHom.id ℤ) dense_W1_0 x y = eval W1_0 x y := by
  exact (Reflection.eval_equal (RingHom.id ℤ) dense_W1_0 (Reflection.ofCoeffs W1_0) (by decide +kernel) x y).trans (Reflection.eval_ofCoeffs W1_0 x y)

without_editor_info def dense_A1_0 : Reflection.Poly := [[(-1374180),1797664,(-958304),3987104,(-901376),2066432,(-484352),131072],[1346144,1824624,2976320,3806208,1056256,819200,(-344064)],[(-209360),1056640,(-260352),64256,(-409600),0,(-65536)],[(-4841280),(-1652608),(-1864192),(-364544),(-65536)],[(-1125584),(-929536),(-16384),143872],[(-1196544),157952,0,172032],[(-64896),102400,0,32768],[182272,16384],[(-71936)],[(-86016)],[(-16384)]]

without_editor_info theorem link_A1_0 (x y : ℤ) : Reflection.eval (RingHom.id ℤ) dense_A1_0 x y = eval A1_0 x y := by
  exact (Reflection.eval_equal (RingHom.id ℤ) dense_A1_0 (Reflection.ofCoeffs A1_0) (by decide +kernel) x y).trans (Reflection.eval_ofCoeffs A1_0 x y)

without_editor_info def dense_B1_0 : Reflection.Poly := [[83726,(-1026848),(-1134828),(-1214904),(-1835088),(-62720),(-928512),209408,(-65536)],[(-1721794),(-2505552),(-2714600),(-2649952),(-2163200),(-673536),(-323584),172032],[(-75632),(-1248808),(-1832880),(-328000),(-751488),389632,(-49152),32768],[(-208848),206784,(-809664),72960,(-14336),204800],[(-658312),(-348576),(-101440),(-204800)],[(-1330960),(-478016),(-436352)],[14336,(-204800)]]

without_editor_info theorem link_B1_0 (x y : ℤ) : Reflection.eval (RingHom.id ℤ) dense_B1_0 x y = eval B1_0 x y := by
  exact (Reflection.eval_equal (RingHom.id ℤ) dense_B1_0 (Reflection.ofCoeffs B1_0) (by decide +kernel) x y).trans (Reflection.eval_ofCoeffs B1_0 x y)

without_editor_info def dense_F : Reflection.Poly := [[2,1,0,2],[0,1],[],[],[1]]

without_editor_info theorem link_F (x y : ℤ) : Reflection.eval (RingHom.id ℤ) dense_F x y = eval F x y := by
  exact (Reflection.eval_equal (RingHom.id ℤ) dense_F (Reflection.ofCoeffs F) (by decide +kernel) x y).trans (Reflection.eval_ofCoeffs F x y)

without_editor_info def dense_H3 : Reflection.Poly := [[2,(-2),4],[2],[(-4)]]

without_editor_info theorem link_H3 (x y : ℤ) : Reflection.eval (RingHom.id ℤ) dense_H3 x y = eval H3 x y := by
  exact (Reflection.eval_equal (RingHom.id ℤ) dense_H3 (Reflection.ofCoeffs H3) (by decide +kernel) x y).trans (Reflection.eval_ofCoeffs H3 x y)

without_editor_info def dense_H4 : Reflection.Poly := [[(-2)]]

without_editor_info theorem link_H4 (x y : ℤ) : Reflection.eval (RingHom.id ℤ) dense_H4 x y = eval H4 x y := by
  exact (Reflection.eval_equal (RingHom.id ℤ) dense_H4 (Reflection.ofCoeffs H4) (by decide +kernel) x y).trans (Reflection.eval_ofCoeffs H4 x y)

without_editor_info theorem star_identity1_0 (x y : ℤ) : (914:ℤ)^2*star1_0 x y-(eval W1_0 x y)^2 = equation x y*eval A1_0 x y + (eval H3 x y)*eval B1_0 x y := by
  have h := Reflection.eval_equal (RingHom.id ℤ) (Reflection.sub (Reflection.mul (Reflection.constant ((914:ℤ)^2)) (dense_H4)) (Reflection.pow dense_W1_0 2)) (Reflection.add (Reflection.mul dense_F dense_A1_0) (Reflection.mul dense_H3 dense_B1_0)) (by decide +kernel) x y
  simpa only [Reflection.eval_add, Reflection.eval_sub, Reflection.eval_mul, Reflection.eval_pow, Reflection.eval_constant, RingHom.id_apply, link_F, link_H3, link_H4, link_W1_0, link_A1_0, link_B1_0, equation, star1_0] using h

without_editor_info theorem ordinary_support1 {x y : ℤ} (hf : equation x y=0) (p : ℕ)
    (hp : p.Prime) (hp2 : p≠2) (hpE : p∉({457}:Finset ℕ)) : value (oddH p) (arguments1 x y)=1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpZ : Prime (p:ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hN : ¬ (p:ℤ) ∣ 914 := by
    intro hd
    have hn : p∣914 := by exact_mod_cast hd
    have hm : p ∈ Nat.primeFactors 914 := Nat.mem_primeFactors.mpr ⟨hp,hn,by decide⟩
    have he : Nat.primeFactors 914 = ({2,457}:Finset ℕ) := by decide +kernel
    rw [he] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact hp2 rfl
    · exact hpE (by simp)
  have supported (a b : ℤ) (he : a*b=(914:ℤ)^1) : ¬(p:ℤ) ∣ a := by
    intro hd
    apply hN
    apply hpZ.dvd_of_dvd_pow
    rw [← he]
    exact dvd_mul_of_dvd_left hd _
  have hc0 : ¬(p:ℤ)∣(eval H4 x y) := by
    apply supported _ (-457:ℤ)
    norm_num [H4,eval]
  have hs0 (hi : (p:ℤ)∣(eval H3 x y)) : jacobiSym (star1_0 x y) p=1 := by
    have hn : ¬(p:ℤ)∣star1_0 x y := by
      simpa only [star1_0, hpZ.dvd_mul, not_or] using hc0
    apply LocalSymbols.jacobi_square_mod _ hn
    exact square_of_identity hf hi (supported 914 (1) (by norm_num)) (star_identity1_0 x y)
  have expand : value (oddH p) (arguments1 x y) = jacobiSym (star1_0 x y) p ^ padicValInt p (eval H3 x y) := by
    simp only [value,arguments1,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    rw [odd_edge (eval H3 x y) (eval H4 x y) (fun h => hc0 h.2)]
    simp only [star1_0, jacobiSym.mul_left, mul_pow]
    simp only [padicValInt.eq_zero_of_not_dvd hc0, pow_zero, one_pow, mul_one, one_mul] <;> ring
  rw [expand]
  rw [star_term (eval H3 x y) (star1_0 x y) hs0] <;> norm_num

without_editor_info theorem ordinary1 {x y : ℤ} (hf : equation x y=0) (p : ℕ)
    (hp : p.Prime) (hp2 : p≠2) (hpE : p∉({11,457}:Finset ℕ)) : value (oddH p) (arguments1 x y)=1 := by
  apply ordinary_support1 hf p hp hp2
  intro h
  apply hpE
  simp_all only [Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty] <;> tauto

namespace FiniteTable

open GraphCert.RationalClasses

without_editor_info def table {α : Type*} {m : ℕ} (xs : List α) (h : xs.length=m)
    (i : Fin m) : α := xs.get (Fin.cast h.symm i)

without_editor_info theorem table_ofFn {α : Type*} {m : ℕ} (xs : List α) (h : xs.length=m) :
    List.ofFn (table xs h)=xs := by
  subst m
  exact List.ofFn_get xs

without_editor_info theorem table_all {α : Type*} {m : ℕ} (xs : List α) (h : xs.length=m)
    (P : α → Prop) [DecidablePred P]
    (hc : xs.all (fun a => decide (P a))=true) : ∀ i, P (table xs h i) := by
  intro i
  exact of_decide_eq_true ((List.all_eq_true.mp hc) _ (List.get_mem _ _))

without_editor_info theorem zip_all {α β : Type*} {n : ℕ}
    (xs : Array α) (ys : Array β) (hx : xs.size = n) (hy : ys.size = n)
    (P : α → β → Prop) [DecidableRel P]
    (hc : (xs.toList.zip ys.toList).all (fun z => decide (P z.1 z.2)) = true) :
    ∀ i : Fin n, P (xs[i.val]'(hx.symm ▸ i.isLt)) (ys[i.val]'(hy.symm ▸ i.isLt)) := by
  intro i
  have hi : i.val < (xs.toList.zip ys.toList).length := by
    simp only [List.length_zip, Array.length_toList, hx, hy, min_self]
    exact i.isLt
  have h := of_decide_eq_true ((List.all_eq_true.mp hc) _ (List.getElem_mem hi))
  simpa only [List.getElem_zip, Array.getElem_toList] using h

without_editor_info theorem table_sum {α A : Type*} {m : ℕ} [AddCommMonoid A]
    (xs : List α) (h : xs.length=m) (f : α → A) :
    (∑ i, f (table xs h i))=(xs.map f).sum := by
  rw [←List.sum_ofFn]
  change (List.ofFn (f ∘ table xs h)).sum=(xs.map f).sum
  rw [←List.map_ofFn,table_ofFn]

without_editor_info theorem graphForm_table {n m : ℕ} (p : ℕ) (es : List (Edge n))
    (h : es.length=m) (H : Fin n → Vector) :
    graphForm p (table es h) H (fun _ => 0)=
      (es.map (fun e => pairing p (H e.1) (H e.2))).sum := by
  unfold graphForm
  rw [table_sum es h (fun e => pairing p (H e.1) (H e.2))]
  simp

without_editor_info theorem neighbors_table {n m : ℕ} (es : List (Edge n)) (h : es.length=m)
    (i : Fin n) : neighbors (table es h) i = es.flatMap (fun e =>
      (if e.1=i then [e.2] else []) ++ (if e.2=i then [e.1] else [])) := by
  have ht := table_ofFn es h
  rw [List.ofFn_eq_map] at ht
  conv_rhs => rw [←ht, List.flatMap_map]
  rfl

end FiniteTable

without_editor_info theorem equation_congr {m x y a b : ℤ} (hx : m∣x-a) (hy : m∣y-b) :
    m∣equation x y-equation a b := GraphCert.RationalClasses.eval_congr F hx hy

namespace RationalAt2

open GraphCert.RationalClasses

without_editor_info instance : Fact (Nat.Prime 2) := ⟨by decide⟩

without_editor_info def polysData : Array Coeffs := #[H0,H1,H2,H3,H4]

without_editor_info def polys (i : Fin 5) : Coeffs := polysData[i.val]'i.isLt

without_editor_info def values (x y : ℤ) (i : Fin 5) : ℤ := eval (polys i) x y

without_editor_info theorem all_nonzero {x y : ℤ} (hf : equation x y=0) : ∀ i : Fin 5, values x y i≠0 := by
  intro i
  fin_cases i
  · exact nonzero0 hf
  · exact nonzero1 hf
  · exact nonzero2 hf
  · exact nonzero3 hf
  · exact nonzero4 hf

without_editor_info def edgeList0 : List (GraphCert.RationalClasses.Edge 5) := [(0,1)]

without_editor_info def edges0 : Fin 1 → GraphCert.RationalClasses.Edge 5 := FiniteTable.table (m := 1) edgeList0 (by decide)

without_editor_info def adjacentData0 : Array (List (Fin 5)) := #[[1],[0],[],[],[]]

without_editor_info def adjacent0 (i : Fin 5) : List (Fin 5) := adjacentData0[i.val]'i.isLt

without_editor_info theorem adjacent_checked0 : ∀ i : Fin 5, neighbors edges0 i=adjacent0 i := by
  simp only [edges0,FiniteTable.neighbors_table]
  decide +kernel

without_editor_info theorem star_sparse0 (H : Fin 5 → Vector) (i : Fin 5) : star 2 edges0 H (fun _ => 0) i=((adjacent0 i).map H).sum := by
  rw [star_neighbors,adjacent_checked0,zero_add]

without_editor_info def localSum0 (x y : ℤ) : ZMod 2 := graphForm 2 edges0 (fun i => localClass 2 (values x y i)) (fun _ => 0)

without_editor_info theorem value_phase0 {x y : ℤ} (hf : equation x y=0) :
    value (twoH) (arguments0 x y)=sign (localSum0 x y) := by
  exact edge_value 2 edges0 (values x y) (all_nonzero hf)

without_editor_info theorem noLoops0 : ∀ e : Fin 1, (edges0 e).1 ≠ (edges0 e).2 := FiniteTable.table_all (m := 1) edgeList0 (by decide) (fun e => e.1 ≠ e.2) (by decide +kernel)

without_editor_info def edgeList1 : List (GraphCert.RationalClasses.Edge 5) := [(3,4)]

without_editor_info def edges1 : Fin 1 → GraphCert.RationalClasses.Edge 5 := FiniteTable.table (m := 1) edgeList1 (by decide)

without_editor_info def adjacentData1 : Array (List (Fin 5)) := #[[],[],[],[4],[3]]

without_editor_info def adjacent1 (i : Fin 5) : List (Fin 5) := adjacentData1[i.val]'i.isLt

without_editor_info theorem adjacent_checked1 : ∀ i : Fin 5, neighbors edges1 i=adjacent1 i := by
  simp only [edges1,FiniteTable.neighbors_table]
  decide +kernel

without_editor_info theorem star_sparse1 (H : Fin 5 → Vector) (i : Fin 5) : star 2 edges1 H (fun _ => 0) i=((adjacent1 i).map H).sum := by
  rw [star_neighbors,adjacent_checked1,zero_add]

without_editor_info def localSum1 (x y : ℤ) : ZMod 2 := graphForm 2 edges1 (fun i => localClass 2 (values x y i)) (fun _ => 0)

without_editor_info theorem value_phase1 {x y : ℤ} (hf : equation x y=0) :
    value (twoH) (arguments1 x y)=sign (localSum1 x y) := by
  exact edge_value 2 edges1 (values x y) (all_nonzero hf)

without_editor_info theorem noLoops1 : ∀ e : Fin 1, (edges1 e).1 ≠ (edges1 e).2 := FiniteTable.table_all (m := 1) edgeList1 (by decide) (fun e => e.1 ≠ e.2) (by decide +kernel)

without_editor_info def envData0 : Array Envelope := #[⟨![1,0,1],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![1,0,1],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![1,1,0],![![0,0,0],![0,0,0],![0,0,0]]⟩]

without_editor_info def env0 (i : Fin 5) : Envelope := envData0[i.val]'i.isLt

without_editor_info theorem checked0 : ∀ i : Fin 5, (env0 i).check 2 4 (values 14 2 i) := by
  exact FiniteTable.zip_all envData0 polysData (by decide) (by decide)
    (fun e h => e.check 2 4 (eval h 14 2)) (by decide +kernel)

without_editor_info theorem fixedDirections0 : ∀ i : Fin 5, (env0 i).directions=0 := by decide +kernel

without_editor_info theorem linear0_0 : ∀ i : Fin 5, ∀ k : Fin 3, pairing 2 ((env0 i).directions k) (star 2 edges0 (fun i => (env0 i).base) (fun _ => 0) i)=0 := by
  intro i k; rw [fixedDirections0]; simp

without_editor_info theorem cross0_0 : ∀ e : Fin 1, ∀ k l : Fin 3, pairing 2 ((env0 (edges0 e).1).directions k) ((env0 (edges0 e).2).directions l)=0 := by
  intro e k l; rw [fixedDirections0]; simp

without_editor_info theorem base0_0 : graphForm 2 edges0 (fun i => (env0 i).base) (fun _ => 0)=0 := by
  unfold edges0
  rw [FiniteTable.graphForm_table]
  decide +kernel

without_editor_info theorem cell0_0 {x y : ℤ} (hx : (2:ℤ)^4∣x-14) (hy : (2:ℤ)^4∣y-2) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 2 edges0 _ (fun _ => 0) env0 ?_ linear0_0 cross0_0,base0_0]
  intro i
  exact Envelope.check_sound (env0 i) 2 4 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked0 i)

without_editor_info theorem linear1_0 : ∀ i : Fin 5, ∀ k : Fin 3, pairing 2 ((env0 i).directions k) (star 2 edges1 (fun i => (env0 i).base) (fun _ => 0) i)=0 := by
  intro i k; rw [fixedDirections0]; simp

without_editor_info theorem cross1_0 : ∀ e : Fin 1, ∀ k l : Fin 3, pairing 2 ((env0 (edges1 e).1).directions k) ((env0 (edges1 e).2).directions l)=0 := by
  intro e k l; rw [fixedDirections0]; simp

without_editor_info theorem base1_0 : graphForm 2 edges1 (fun i => (env0 i).base) (fun _ => 0)=1 := by
  unfold edges1
  rw [FiniteTable.graphForm_table]
  decide +kernel

without_editor_info theorem cell1_0 {x y : ℤ} (hx : (2:ℤ)^4∣x-14) (hy : (2:ℤ)^4∣y-2) : localSum1 x y=1 := by
  rw [localSum1,graphForm_envelopes 2 edges1 _ (fun _ => 0) env0 ?_ linear1_0 cross1_0,base1_0]
  intro i
  exact Envelope.check_sound (env0 i) 2 4 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked0 i)

without_editor_info theorem checked1 : ∀ i : Fin 5, (env0 i).check 2 4 (values 6 2 i) := by
  exact FiniteTable.zip_all envData0 polysData (by decide) (by decide)
    (fun e h => e.check 2 4 (eval h 6 2)) (by decide +kernel)

without_editor_info theorem cell0_1 {x y : ℤ} (hx : (2:ℤ)^4∣x-6) (hy : (2:ℤ)^4∣y-2) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 2 edges0 _ (fun _ => 0) env0 ?_ linear0_0 cross0_0,base0_0]
  intro i
  exact Envelope.check_sound (env0 i) 2 4 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked1 i)

without_editor_info theorem cell1_1 {x y : ℤ} (hx : (2:ℤ)^4∣x-6) (hy : (2:ℤ)^4∣y-2) : localSum1 x y=1 := by
  rw [localSum1,graphForm_envelopes 2 edges1 _ (fun _ => 0) env0 ?_ linear1_0 cross1_0,base1_0]
  intro i
  exact Envelope.check_sound (env0 i) 2 4 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked1 i)

without_editor_info def envData2 : Array Envelope := #[⟨![1,0,1],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,1],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![1,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![1,1,0],![![0,0,0],![0,0,0],![0,0,0]]⟩]

without_editor_info def env2 (i : Fin 5) : Envelope := envData2[i.val]'i.isLt

without_editor_info theorem checked2 : ∀ i : Fin 5, (env2 i).check 2 4 (values 10 10 i) := by
  exact FiniteTable.zip_all envData2 polysData (by decide) (by decide)
    (fun e h => e.check 2 4 (eval h 10 10)) (by decide +kernel)

without_editor_info theorem fixedDirections2 : ∀ i : Fin 5, (env2 i).directions=0 := by decide +kernel

without_editor_info theorem linear0_2 : ∀ i : Fin 5, ∀ k : Fin 3, pairing 2 ((env2 i).directions k) (star 2 edges0 (fun i => (env2 i).base) (fun _ => 0) i)=0 := by
  intro i k; rw [fixedDirections2]; simp

without_editor_info theorem cross0_2 : ∀ e : Fin 1, ∀ k l : Fin 3, pairing 2 ((env2 (edges0 e).1).directions k) ((env2 (edges0 e).2).directions l)=0 := by
  intro e k l; rw [fixedDirections2]; simp

without_editor_info theorem base0_2 : graphForm 2 edges0 (fun i => (env2 i).base) (fun _ => 0)=1 := by
  unfold edges0
  rw [FiniteTable.graphForm_table]
  decide +kernel

without_editor_info theorem cell0_2 {x y : ℤ} (hx : (2:ℤ)^4∣x-10) (hy : (2:ℤ)^4∣y-10) : localSum0 x y=1 := by
  rw [localSum0,graphForm_envelopes 2 edges0 _ (fun _ => 0) env2 ?_ linear0_2 cross0_2,base0_2]
  intro i
  exact Envelope.check_sound (env2 i) 2 4 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked2 i)

without_editor_info theorem linear1_2 : ∀ i : Fin 5, ∀ k : Fin 3, pairing 2 ((env2 i).directions k) (star 2 edges1 (fun i => (env2 i).base) (fun _ => 0) i)=0 := by
  intro i k; rw [fixedDirections2]; simp

without_editor_info theorem cross1_2 : ∀ e : Fin 1, ∀ k l : Fin 3, pairing 2 ((env2 (edges1 e).1).directions k) ((env2 (edges1 e).2).directions l)=0 := by
  intro e k l; rw [fixedDirections2]; simp

without_editor_info theorem base1_2 : graphForm 2 edges1 (fun i => (env2 i).base) (fun _ => 0)=0 := by
  unfold edges1
  rw [FiniteTable.graphForm_table]
  decide +kernel

without_editor_info theorem cell1_2 {x y : ℤ} (hx : (2:ℤ)^4∣x-10) (hy : (2:ℤ)^4∣y-10) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 2 edges1 _ (fun _ => 0) env2 ?_ linear1_2 cross1_2,base1_2]
  intro i
  exact Envelope.check_sound (env2 i) 2 4 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked2 i)

without_editor_info theorem checked3 : ∀ i : Fin 5, (env2 i).check 2 4 (values 2 10 i) := by
  exact FiniteTable.zip_all envData2 polysData (by decide) (by decide)
    (fun e h => e.check 2 4 (eval h 2 10)) (by decide +kernel)

without_editor_info theorem cell0_3 {x y : ℤ} (hx : (2:ℤ)^4∣x-2) (hy : (2:ℤ)^4∣y-10) : localSum0 x y=1 := by
  rw [localSum0,graphForm_envelopes 2 edges0 _ (fun _ => 0) env2 ?_ linear0_2 cross0_2,base0_2]
  intro i
  exact Envelope.check_sound (env2 i) 2 4 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked3 i)

without_editor_info theorem cell1_3 {x y : ℤ} (hx : (2:ℤ)^4∣x-2) (hy : (2:ℤ)^4∣y-10) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 2 edges1 _ (fun _ => 0) env2 ?_ linear1_2 cross1_2,base1_2]
  intro i
  exact Envelope.check_sound (env2 i) 2 4 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked3 i)

without_editor_info def envData4 : Array Envelope := #[⟨![1,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,1,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![1,1,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![1,1,0],![![0,0,0],![0,0,0],![0,0,0]]⟩]

without_editor_info def env4 (i : Fin 5) : Envelope := envData4[i.val]'i.isLt

without_editor_info theorem checked4 : ∀ i : Fin 5, (env4 i).check 2 4 (values 12 6 i) := by
  exact FiniteTable.zip_all envData4 polysData (by decide) (by decide)
    (fun e h => e.check 2 4 (eval h 12 6)) (by decide +kernel)

without_editor_info theorem fixedDirections4 : ∀ i : Fin 5, (env4 i).directions=0 := by decide +kernel

without_editor_info theorem linear0_4 : ∀ i : Fin 5, ∀ k : Fin 3, pairing 2 ((env4 i).directions k) (star 2 edges0 (fun i => (env4 i).base) (fun _ => 0) i)=0 := by
  intro i k; rw [fixedDirections4]; simp

without_editor_info theorem cross0_4 : ∀ e : Fin 1, ∀ k l : Fin 3, pairing 2 ((env4 (edges0 e).1).directions k) ((env4 (edges0 e).2).directions l)=0 := by
  intro e k l; rw [fixedDirections4]; simp

without_editor_info theorem base0_4 : graphForm 2 edges0 (fun i => (env4 i).base) (fun _ => 0)=0 := by
  unfold edges0
  rw [FiniteTable.graphForm_table]
  decide +kernel

without_editor_info theorem cell0_4 {x y : ℤ} (hx : (2:ℤ)^4∣x-12) (hy : (2:ℤ)^4∣y-6) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 2 edges0 _ (fun _ => 0) env4 ?_ linear0_4 cross0_4,base0_4]
  intro i
  exact Envelope.check_sound (env4 i) 2 4 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked4 i)

without_editor_info theorem linear1_4 : ∀ i : Fin 5, ∀ k : Fin 3, pairing 2 ((env4 i).directions k) (star 2 edges1 (fun i => (env4 i).base) (fun _ => 0) i)=0 := by
  intro i k; rw [fixedDirections4]; simp

without_editor_info theorem cross1_4 : ∀ e : Fin 1, ∀ k l : Fin 3, pairing 2 ((env4 (edges1 e).1).directions k) ((env4 (edges1 e).2).directions l)=0 := by
  intro e k l; rw [fixedDirections4]; simp

without_editor_info theorem base1_4 : graphForm 2 edges1 (fun i => (env4 i).base) (fun _ => 0)=1 := by
  unfold edges1
  rw [FiniteTable.graphForm_table]
  decide +kernel

without_editor_info theorem cell1_4 {x y : ℤ} (hx : (2:ℤ)^4∣x-12) (hy : (2:ℤ)^4∣y-6) : localSum1 x y=1 := by
  rw [localSum1,graphForm_envelopes 2 edges1 _ (fun _ => 0) env4 ?_ linear1_4 cross1_4,base1_4]
  intro i
  exact Envelope.check_sound (env4 i) 2 4 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked4 i)

without_editor_info theorem checked5 : ∀ i : Fin 5, (env4 i).check 2 4 (values 4 6 i) := by
  exact FiniteTable.zip_all envData4 polysData (by decide) (by decide)
    (fun e h => e.check 2 4 (eval h 4 6)) (by decide +kernel)

without_editor_info theorem cell0_5 {x y : ℤ} (hx : (2:ℤ)^4∣x-4) (hy : (2:ℤ)^4∣y-6) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 2 edges0 _ (fun _ => 0) env4 ?_ linear0_4 cross0_4,base0_4]
  intro i
  exact Envelope.check_sound (env4 i) 2 4 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked5 i)

without_editor_info theorem cell1_5 {x y : ℤ} (hx : (2:ℤ)^4∣x-4) (hy : (2:ℤ)^4∣y-6) : localSum1 x y=1 := by
  rw [localSum1,graphForm_envelopes 2 edges1 _ (fun _ => 0) env4 ?_ linear1_4 cross1_4,base1_4]
  intro i
  exact Envelope.check_sound (env4 i) 2 4 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked5 i)

without_editor_info def envData6 : Array Envelope := #[⟨![1,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,1,1],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![1,1,1],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![1,1,0],![![0,0,0],![0,0,0],![0,0,0]]⟩]

without_editor_info def env6 (i : Fin 5) : Envelope := envData6[i.val]'i.isLt

without_editor_info theorem checked6 : ∀ i : Fin 5, (env6 i).check 2 4 (values 8 14 i) := by
  exact FiniteTable.zip_all envData6 polysData (by decide) (by decide)
    (fun e h => e.check 2 4 (eval h 8 14)) (by decide +kernel)

without_editor_info theorem fixedDirections6 : ∀ i : Fin 5, (env6 i).directions=0 := by decide +kernel

without_editor_info theorem linear0_6 : ∀ i : Fin 5, ∀ k : Fin 3, pairing 2 ((env6 i).directions k) (star 2 edges0 (fun i => (env6 i).base) (fun _ => 0) i)=0 := by
  intro i k; rw [fixedDirections6]; simp

without_editor_info theorem cross0_6 : ∀ e : Fin 1, ∀ k l : Fin 3, pairing 2 ((env6 (edges0 e).1).directions k) ((env6 (edges0 e).2).directions l)=0 := by
  intro e k l; rw [fixedDirections6]; simp

without_editor_info theorem base0_6 : graphForm 2 edges0 (fun i => (env6 i).base) (fun _ => 0)=1 := by
  unfold edges0
  rw [FiniteTable.graphForm_table]
  decide +kernel

without_editor_info theorem cell0_6 {x y : ℤ} (hx : (2:ℤ)^4∣x-8) (hy : (2:ℤ)^4∣y-14) : localSum0 x y=1 := by
  rw [localSum0,graphForm_envelopes 2 edges0 _ (fun _ => 0) env6 ?_ linear0_6 cross0_6,base0_6]
  intro i
  exact Envelope.check_sound (env6 i) 2 4 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked6 i)

without_editor_info theorem linear1_6 : ∀ i : Fin 5, ∀ k : Fin 3, pairing 2 ((env6 i).directions k) (star 2 edges1 (fun i => (env6 i).base) (fun _ => 0) i)=0 := by
  intro i k; rw [fixedDirections6]; simp

without_editor_info theorem cross1_6 : ∀ e : Fin 1, ∀ k l : Fin 3, pairing 2 ((env6 (edges1 e).1).directions k) ((env6 (edges1 e).2).directions l)=0 := by
  intro e k l; rw [fixedDirections6]; simp

without_editor_info theorem base1_6 : graphForm 2 edges1 (fun i => (env6 i).base) (fun _ => 0)=0 := by
  unfold edges1
  rw [FiniteTable.graphForm_table]
  decide +kernel

without_editor_info theorem cell1_6 {x y : ℤ} (hx : (2:ℤ)^4∣x-8) (hy : (2:ℤ)^4∣y-14) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 2 edges1 _ (fun _ => 0) env6 ?_ linear1_6 cross1_6,base1_6]
  intro i
  exact Envelope.check_sound (env6 i) 2 4 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked6 i)

without_editor_info theorem checked7 : ∀ i : Fin 5, (env6 i).check 2 4 (values 0 14 i) := by
  exact FiniteTable.zip_all envData6 polysData (by decide) (by decide)
    (fun e h => e.check 2 4 (eval h 0 14)) (by decide +kernel)

without_editor_info theorem cell0_7 {x y : ℤ} (hx : (2:ℤ)^4∣x-0) (hy : (2:ℤ)^4∣y-14) : localSum0 x y=1 := by
  rw [localSum0,graphForm_envelopes 2 edges0 _ (fun _ => 0) env6 ?_ linear0_6 cross0_6,base0_6]
  intro i
  exact Envelope.check_sound (env6 i) 2 4 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked7 i)

without_editor_info theorem cell1_7 {x y : ℤ} (hx : (2:ℤ)^4∣x-0) (hy : (2:ℤ)^4∣y-14) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 2 edges1 _ (fun _ => 0) env6 ?_ linear1_6 cross1_6,base1_6]
  intro i
  exact Envelope.check_sound (env6 i) 2 4 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked7 i)

without_editor_info def residues : Fin 8 → ℤ × ℤ × ℕ := (fun i => (#[(14,2,4),(6,2,4),(10,10,4),(2,10,4),(12,6,4),(4,6,4),(8,14,4),(0,14,4)] : Array (ℤ × ℤ × ℕ))[i.val]'(by simpa using i.isLt))

without_editor_info def targets0 : Fin 8 → ZMod 2 := (fun i => (#[0,0,1,1,0,0,1,1] : Array (ZMod 2))[i.val]'(by simpa using i.isLt))

without_editor_info theorem cell_value0 (i : Fin 8) {x y : ℤ}
    (hx : (2:ℤ)^(residues i).2.2∣x-(residues i).1)
    (hy : (2:ℤ)^(residues i).2.2∣y-(residues i).2.1) : localSum0 x y=targets0 i := by
  fin_cases i
  · exact cell0_0 hx hy
  · exact cell0_1 hx hy
  · exact cell0_2 hx hy
  · exact cell0_3 hx hy
  · exact cell0_4 hx hy
  · exact cell0_5 hx hy
  · exact cell0_6 hx hy
  · exact cell0_7 hx hy

without_editor_info def targets1 : Fin 8 → ZMod 2 := (fun i => (#[1,1,0,0,1,1,0,0] : Array (ZMod 2))[i.val]'(by simpa using i.isLt))

without_editor_info theorem cell_value1 (i : Fin 8) {x y : ℤ}
    (hx : (2:ℤ)^(residues i).2.2∣x-(residues i).1)
    (hy : (2:ℤ)^(residues i).2.2∣y-(residues i).2.1) : localSum1 x y=targets1 i := by
  fin_cases i
  · exact cell1_0 hx hy
  · exact cell1_1 hx hy
  · exact cell1_2 hx hy
  · exact cell1_3 hx hy
  · exact cell1_4 hx hy
  · exact cell1_5 hx hy
  · exact cell1_6 hx hy
  · exact cell1_7 hx hy

without_editor_info theorem covered0 {x y : ℤ} (_hf : equation x y=0) (hx : (2:ℤ)^4∣x-14) (hy : (2:ℤ)^4∣y-2) : ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨0,hx,hy⟩

without_editor_info theorem covered1 {x y : ℤ} (_hf : equation x y=0) (hx : (2:ℤ)^4∣x-6) (hy : (2:ℤ)^4∣y-2) : ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨1,hx,hy⟩

without_editor_info theorem covered2 {x y : ℤ} (_hf : equation x y=0) (hx : (2:ℤ)^4∣x-10) (hy : (2:ℤ)^4∣y-10) : ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨2,hx,hy⟩

without_editor_info theorem covered3 {x y : ℤ} (_hf : equation x y=0) (hx : (2:ℤ)^4∣x-2) (hy : (2:ℤ)^4∣y-10) : ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨3,hx,hy⟩

without_editor_info theorem covered4 {x y : ℤ} (_hf : equation x y=0) (hx : (2:ℤ)^4∣x-12) (hy : (2:ℤ)^4∣y-6) : ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨4,hx,hy⟩

without_editor_info theorem covered5 {x y : ℤ} (_hf : equation x y=0) (hx : (2:ℤ)^4∣x-4) (hy : (2:ℤ)^4∣y-6) : ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨5,hx,hy⟩

without_editor_info theorem covered6 {x y : ℤ} (_hf : equation x y=0) (hx : (2:ℤ)^4∣x-8) (hy : (2:ℤ)^4∣y-14) : ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨6,hx,hy⟩

without_editor_info theorem covered7 {x y : ℤ} (_hf : equation x y=0) (hx : (2:ℤ)^4∣x-0) (hy : (2:ℤ)^4∣y-14) : ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨7,hx,hy⟩

without_editor_info theorem branch0 {x y : ℤ} (hf : equation x y=0) (hx : (2:ℤ)^3∣x-0) (hy : (2:ℤ)^3∣y-6) : ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1) 2 (by decide) 8 0 6 [(0,14),(8,14)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl
  · intro X Y hF hX hY
    apply covered7 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered6 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch1 {x y : ℤ} (hf : equation x y=0) (hx : (2:ℤ)^3∣x-4) (hy : (2:ℤ)^3∣y-6) : ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1) 2 (by decide) 8 4 6 [(4,6),(12,6)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl
  · intro X Y hF hX hY
    apply covered5 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered4 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch2 {x y : ℤ} (hf : equation x y=0) (hx : (2:ℤ)^2∣x-0) (hy : (2:ℤ)^2∣y-2) : ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1) 2 (by decide) 4 0 2 [(0,6),(4,6)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl
  · intro X Y hF hX hY
    apply branch0 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply branch1 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch3 {x y : ℤ} (hf : equation x y=0) (hx : (2:ℤ)^3∣x-2) (hy : (2:ℤ)^3∣y-2) : ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1) 2 (by decide) 8 2 2 [(2,10),(10,10)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl
  · intro X Y hF hX hY
    apply covered3 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered2 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch4 {x y : ℤ} (hf : equation x y=0) (hx : (2:ℤ)^3∣x-6) (hy : (2:ℤ)^3∣y-2) : ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1) 2 (by decide) 8 6 2 [(6,2),(14,2)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl
  · intro X Y hF hX hY
    apply covered1 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered0 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch5 {x y : ℤ} (hf : equation x y=0) (hx : (2:ℤ)^2∣x-2) (hy : (2:ℤ)^2∣y-2) : ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1) 2 (by decide) 4 2 2 [(2,2),(6,2)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl
  · intro X Y hF hX hY
    apply branch3 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply branch4 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch6 {x y : ℤ} (hf : equation x y=0) (hx : (2:ℤ)^1∣x-0) (hy : (2:ℤ)^1∣y-0) : ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1) 2 (by decide) 2 0 0 [(0,2),(2,2)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl
  · intro X Y hF hX hY
    apply branch2 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply branch5 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch7 {x y : ℤ} (hf : equation x y=0) (hx : (2:ℤ)^0∣x-0) (hy : (2:ℤ)^0∣y-0) : ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1) 2 (by decide) 1 0 0 [(0,0)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl
  · intro X Y hF hX hY
    apply branch6 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem local_cover {x y : ℤ} (hf : equation x y=0) : ∃ i : Fin 8, (2:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (2:ℤ)^(residues i).2.2∣y-(residues i).2.1 := branch7 hf (by simp) (by simp)

without_editor_info theorem local_values {x y : ℤ} (hf : equation x y=0) : (value (twoH) (arguments0 x y),value (twoH) (arguments1 x y)) ∈ ([(-1,1),(1,-1)]:List (ℤ × ℤ)) := by
  obtain ⟨i,hx,hy⟩ := local_cover hf
  have ht : ∀ i : Fin 8, (sign (targets0 i),sign (targets1 i)) ∈ ([(-1,1),(1,-1)]:List (ℤ × ℤ)) := by decide +kernel
  simpa only [value_phase0 hf,cell_value0 i hx hy,value_phase1 hf,cell_value1 i hx hy] using ht i

end RationalAt2

without_editor_info theorem local2 {x y : ℤ} (hf : equation x y=0) : (value (twoH) (arguments0 x y),value (twoH) (arguments1 x y)) ∈ ([(-1,1),(1,-1)]:List (ℤ × ℤ)) := RationalAt2.local_values hf

namespace RationalAt11

open GraphCert.RationalClasses

without_editor_info instance : Fact (Nat.Prime 11) := ⟨by decide⟩

without_editor_info def polysData : Array Coeffs := #[H0,H1,H2,H3,H4]

without_editor_info def polys (i : Fin 5) : Coeffs := polysData[i.val]'i.isLt

without_editor_info def values (x y : ℤ) (i : Fin 5) : ℤ := eval (polys i) x y

without_editor_info theorem all_nonzero {x y : ℤ} (hf : equation x y=0) : ∀ i : Fin 5, values x y i≠0 := by
  intro i
  fin_cases i
  · exact nonzero0 hf
  · exact nonzero1 hf
  · exact nonzero2 hf
  · exact nonzero3 hf
  · exact nonzero4 hf

without_editor_info def edgeList0 : List (GraphCert.RationalClasses.Edge 5) := [(0,1)]

without_editor_info def edges0 : Fin 1 → GraphCert.RationalClasses.Edge 5 := FiniteTable.table (m := 1) edgeList0 (by decide)

without_editor_info def adjacentData0 : Array (List (Fin 5)) := #[[1],[0],[],[],[]]

without_editor_info def adjacent0 (i : Fin 5) : List (Fin 5) := adjacentData0[i.val]'i.isLt

without_editor_info theorem adjacent_checked0 : ∀ i : Fin 5, neighbors edges0 i=adjacent0 i := by
  simp only [edges0,FiniteTable.neighbors_table]
  decide +kernel

without_editor_info theorem star_sparse0 (H : Fin 5 → Vector) (i : Fin 5) : star 11 edges0 H (fun _ => 0) i=((adjacent0 i).map H).sum := by
  rw [star_neighbors,adjacent_checked0,zero_add]

without_editor_info def localSum0 (x y : ℤ) : ZMod 2 := graphForm 11 edges0 (fun i => localClass 11 (values x y i)) (fun _ => 0)

without_editor_info theorem value_phase0 {x y : ℤ} (hf : equation x y=0) :
    value (oddH 11) (arguments0 x y)=sign (localSum0 x y) := by
  exact edge_value 11 edges0 (values x y) (all_nonzero hf)

without_editor_info theorem noLoops0 : ∀ e : Fin 1, (edges0 e).1 ≠ (edges0 e).2 := FiniteTable.table_all (m := 1) edgeList0 (by decide) (fun e => e.1 ≠ e.2) (by decide +kernel)

without_editor_info def edgeList1 : List (GraphCert.RationalClasses.Edge 5) := [(3,4)]

without_editor_info def edges1 : Fin 1 → GraphCert.RationalClasses.Edge 5 := FiniteTable.table (m := 1) edgeList1 (by decide)

without_editor_info def adjacentData1 : Array (List (Fin 5)) := #[[],[],[],[4],[3]]

without_editor_info def adjacent1 (i : Fin 5) : List (Fin 5) := adjacentData1[i.val]'i.isLt

without_editor_info theorem adjacent_checked1 : ∀ i : Fin 5, neighbors edges1 i=adjacent1 i := by
  simp only [edges1,FiniteTable.neighbors_table]
  decide +kernel

without_editor_info theorem star_sparse1 (H : Fin 5 → Vector) (i : Fin 5) : star 11 edges1 H (fun _ => 0) i=((adjacent1 i).map H).sum := by
  rw [star_neighbors,adjacent_checked1,zero_add]

without_editor_info def localSum1 (x y : ℤ) : ZMod 2 := graphForm 11 edges1 (fun i => localClass 11 (values x y i)) (fun _ => 0)

without_editor_info theorem value_phase1 {x y : ℤ} (hf : equation x y=0) :
    value (oddH 11) (arguments1 x y)=sign (localSum1 x y) := by
  exact edge_value 11 edges1 (values x y) (all_nonzero hf)

without_editor_info theorem noLoops1 : ∀ e : Fin 1, (edges1 e).1 ≠ (edges1 e).2 := FiniteTable.table_all (m := 1) edgeList1 (by decide) (fun e => e.1 ≠ e.2) (by decide +kernel)

without_editor_info def envData0 : Array Envelope := #[⟨![0,1,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,1,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩]

without_editor_info def env0 (i : Fin 5) : Envelope := envData0[i.val]'i.isLt

without_editor_info theorem checked0 : ∀ i : Fin 5, (env0 i).check 11 1 (values 10 5 i) := by
  exact FiniteTable.zip_all envData0 polysData (by decide) (by decide)
    (fun e h => e.check 11 1 (eval h 10 5)) (by decide +kernel)

without_editor_info theorem fixedDirections0 : ∀ i : Fin 5, (env0 i).directions=0 := by decide +kernel

without_editor_info theorem linear0_0 : ∀ i : Fin 5, ∀ k : Fin 3, pairing 11 ((env0 i).directions k) (star 11 edges0 (fun i => (env0 i).base) (fun _ => 0) i)=0 := by
  intro i k; rw [fixedDirections0]; simp

without_editor_info theorem cross0_0 : ∀ e : Fin 1, ∀ k l : Fin 3, pairing 11 ((env0 (edges0 e).1).directions k) ((env0 (edges0 e).2).directions l)=0 := by
  intro e k l; rw [fixedDirections0]; simp

without_editor_info theorem base0_0 : graphForm 11 edges0 (fun i => (env0 i).base) (fun _ => 0)=0 := by
  unfold edges0
  rw [FiniteTable.graphForm_table]
  decide +kernel

without_editor_info theorem cell0_0 {x y : ℤ} (hx : (11:ℤ)^1∣x-10) (hy : (11:ℤ)^1∣y-5) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env0 ?_ linear0_0 cross0_0,base0_0]
  intro i
  exact Envelope.check_sound (env0 i) 11 1 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked0 i)

without_editor_info theorem linear1_0 : ∀ i : Fin 5, ∀ k : Fin 3, pairing 11 ((env0 i).directions k) (star 11 edges1 (fun i => (env0 i).base) (fun _ => 0) i)=0 := by
  intro i k; rw [fixedDirections0]; simp

without_editor_info theorem cross1_0 : ∀ e : Fin 1, ∀ k l : Fin 3, pairing 11 ((env0 (edges1 e).1).directions k) ((env0 (edges1 e).2).directions l)=0 := by
  intro e k l; rw [fixedDirections0]; simp

without_editor_info theorem base1_0 : graphForm 11 edges1 (fun i => (env0 i).base) (fun _ => 0)=0 := by
  unfold edges1
  rw [FiniteTable.graphForm_table]
  decide +kernel

without_editor_info theorem cell1_0 {x y : ℤ} (hx : (11:ℤ)^1∣x-10) (hy : (11:ℤ)^1∣y-5) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env0 ?_ linear1_0 cross1_0,base1_0]
  intro i
  exact Envelope.check_sound (env0 i) 11 1 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked0 i)

without_editor_info def envData1 : Array Envelope := #[⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,1,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩]

without_editor_info def env1 (i : Fin 5) : Envelope := envData1[i.val]'i.isLt

without_editor_info theorem checked1 : ∀ i : Fin 5, (env1 i).check 11 1 (values 9 8 i) := by
  exact FiniteTable.zip_all envData1 polysData (by decide) (by decide)
    (fun e h => e.check 11 1 (eval h 9 8)) (by decide +kernel)

without_editor_info theorem fixedDirections1 : ∀ i : Fin 5, (env1 i).directions=0 := by decide +kernel

without_editor_info theorem linear0_1 : ∀ i : Fin 5, ∀ k : Fin 3, pairing 11 ((env1 i).directions k) (star 11 edges0 (fun i => (env1 i).base) (fun _ => 0) i)=0 := by
  intro i k; rw [fixedDirections1]; simp

without_editor_info theorem cross0_1 : ∀ e : Fin 1, ∀ k l : Fin 3, pairing 11 ((env1 (edges0 e).1).directions k) ((env1 (edges0 e).2).directions l)=0 := by
  intro e k l; rw [fixedDirections1]; simp

without_editor_info theorem base0_1 : graphForm 11 edges0 (fun i => (env1 i).base) (fun _ => 0)=0 := by
  unfold edges0
  rw [FiniteTable.graphForm_table]
  decide +kernel

without_editor_info theorem cell0_1 {x y : ℤ} (hx : (11:ℤ)^1∣x-9) (hy : (11:ℤ)^1∣y-8) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env1 ?_ linear0_1 cross0_1,base0_1]
  intro i
  exact Envelope.check_sound (env1 i) 11 1 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked1 i)

without_editor_info theorem linear1_1 : ∀ i : Fin 5, ∀ k : Fin 3, pairing 11 ((env1 i).directions k) (star 11 edges1 (fun i => (env1 i).base) (fun _ => 0) i)=0 := by
  intro i k; rw [fixedDirections1]; simp

without_editor_info theorem cross1_1 : ∀ e : Fin 1, ∀ k l : Fin 3, pairing 11 ((env1 (edges1 e).1).directions k) ((env1 (edges1 e).2).directions l)=0 := by
  intro e k l; rw [fixedDirections1]; simp

without_editor_info theorem base1_1 : graphForm 11 edges1 (fun i => (env1 i).base) (fun _ => 0)=0 := by
  unfold edges1
  rw [FiniteTable.graphForm_table]
  decide +kernel

without_editor_info theorem cell1_1 {x y : ℤ} (hx : (11:ℤ)^1∣x-9) (hy : (11:ℤ)^1∣y-8) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env1 ?_ linear1_1 cross1_1,base1_1]
  intro i
  exact Envelope.check_sound (env1 i) 11 1 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked1 i)

without_editor_info theorem checked2 : ∀ i : Fin 5, (env1 i).check 11 1 (values 7 4 i) := by
  exact FiniteTable.zip_all envData1 polysData (by decide) (by decide)
    (fun e h => e.check 11 1 (eval h 7 4)) (by decide +kernel)

without_editor_info theorem cell0_2 {x y : ℤ} (hx : (11:ℤ)^1∣x-7) (hy : (11:ℤ)^1∣y-4) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env1 ?_ linear0_1 cross0_1,base0_1]
  intro i
  exact Envelope.check_sound (env1 i) 11 1 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked2 i)

without_editor_info theorem cell1_2 {x y : ℤ} (hx : (11:ℤ)^1∣x-7) (hy : (11:ℤ)^1∣y-4) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env1 ?_ linear1_1 cross1_1,base1_1]
  intro i
  exact Envelope.check_sound (env1 i) 11 1 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked2 i)

without_editor_info theorem checked3 : ∀ i : Fin 5, (env1 i).check 11 1 (values 6 0 i) := by
  exact FiniteTable.zip_all envData1 polysData (by decide) (by decide)
    (fun e h => e.check 11 1 (eval h 6 0)) (by decide +kernel)

without_editor_info theorem cell0_3 {x y : ℤ} (hx : (11:ℤ)^1∣x-6) (hy : (11:ℤ)^1∣y-0) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env1 ?_ linear0_1 cross0_1,base0_1]
  intro i
  exact Envelope.check_sound (env1 i) 11 1 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked3 i)

without_editor_info theorem cell1_3 {x y : ℤ} (hx : (11:ℤ)^1∣x-6) (hy : (11:ℤ)^1∣y-0) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env1 ?_ linear1_1 cross1_1,base1_1]
  intro i
  exact Envelope.check_sound (env1 i) 11 1 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked3 i)

without_editor_info def envData4 : Array Envelope := #[⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![1,0,0],![0,1,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩]

without_editor_info def env4 (i : Fin 5) : Envelope := envData4[i.val]'i.isLt

without_editor_info theorem checked4 : ∀ i : Fin 5, (env4 i).check 11 1 (values 5 0 i) := by
  exact FiniteTable.zip_all envData4 polysData (by decide) (by decide)
    (fun e h => e.check 11 1 (eval h 5 0)) (by decide +kernel)

without_editor_info theorem fixedDirections4 : ∀ i : Fin 5, i=3 ∨ (env4 i).directions=0 := by decide +kernel

without_editor_info theorem linear0_4 : ∀ i : Fin 5, ∀ k : Fin 3, pairing 11 ((env4 i).directions k) (star 11 edges0 (fun i => (env4 i).base) (fun _ => 0) i)=0 := by
  have h : ∀ k : Fin 3, pairing 11 ((env4 3).directions k) (star 11 edges0 (fun i => (env4 i).base) (fun _ => 0) 3)=0 := by
    simp only [star_sparse0]
    decide +kernel
  intro i k; rcases fixedDirections4 i with rfl | hz
  · exact h k
  · rw [hz]; simp

without_editor_info theorem cross0_4 : ∀ e : Fin 1, ∀ k l : Fin 3, pairing 11 ((env4 (edges0 e).1).directions k) ((env4 (edges0 e).2).directions l)=0 := by
  intro e k l; rcases fixedDirections4 (edges0 e).1 with hs | hz
  · rcases fixedDirections4 (edges0 e).2 with ht | hz
    · exact False.elim (noLoops0 e (hs.trans ht.symm))
    · rw [hz]; simp
  · rw [hz]; simp

without_editor_info theorem base0_4 : graphForm 11 edges0 (fun i => (env4 i).base) (fun _ => 0)=0 := by
  unfold edges0
  rw [FiniteTable.graphForm_table]
  decide +kernel

without_editor_info theorem cell0_4 {x y : ℤ} (hx : (11:ℤ)^1∣x-5) (hy : (11:ℤ)^1∣y-0) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env4 ?_ linear0_4 cross0_4,base0_4]
  intro i
  exact Envelope.check_sound (env4 i) 11 1 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked4 i)

without_editor_info theorem linear1_4 : ∀ i : Fin 5, ∀ k : Fin 3, pairing 11 ((env4 i).directions k) (star 11 edges1 (fun i => (env4 i).base) (fun _ => 0) i)=0 := by
  have h : ∀ k : Fin 3, pairing 11 ((env4 3).directions k) (star 11 edges1 (fun i => (env4 i).base) (fun _ => 0) 3)=0 := by
    simp only [star_sparse1]
    decide +kernel
  intro i k; rcases fixedDirections4 i with rfl | hz
  · exact h k
  · rw [hz]; simp

without_editor_info theorem cross1_4 : ∀ e : Fin 1, ∀ k l : Fin 3, pairing 11 ((env4 (edges1 e).1).directions k) ((env4 (edges1 e).2).directions l)=0 := by
  intro e k l; rcases fixedDirections4 (edges1 e).1 with hs | hz
  · rcases fixedDirections4 (edges1 e).2 with ht | hz
    · exact False.elim (noLoops1 e (hs.trans ht.symm))
    · rw [hz]; simp
  · rw [hz]; simp

without_editor_info theorem base1_4 : graphForm 11 edges1 (fun i => (env4 i).base) (fun _ => 0)=0 := by
  unfold edges1
  rw [FiniteTable.graphForm_table]
  decide +kernel

without_editor_info theorem cell1_4 {x y : ℤ} (hx : (11:ℤ)^1∣x-5) (hy : (11:ℤ)^1∣y-0) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env4 ?_ linear1_4 cross1_4,base1_4]
  intro i
  exact Envelope.check_sound (env4 i) 11 1 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked4 i)

without_editor_info def envData5 : Array Envelope := #[⟨![0,1,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,1,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,1,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩]

without_editor_info def env5 (i : Fin 5) : Envelope := envData5[i.val]'i.isLt

without_editor_info theorem checked5 : ∀ i : Fin 5, (env5 i).check 11 3 (values 1324 843 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1324 843)) (by decide +kernel)

without_editor_info theorem fixedDirections5 : ∀ i : Fin 5, (env5 i).directions=0 := by decide +kernel

without_editor_info theorem linear0_5 : ∀ i : Fin 5, ∀ k : Fin 3, pairing 11 ((env5 i).directions k) (star 11 edges0 (fun i => (env5 i).base) (fun _ => 0) i)=0 := by
  intro i k; rw [fixedDirections5]; simp

without_editor_info theorem cross0_5 : ∀ e : Fin 1, ∀ k l : Fin 3, pairing 11 ((env5 (edges0 e).1).directions k) ((env5 (edges0 e).2).directions l)=0 := by
  intro e k l; rw [fixedDirections5]; simp

without_editor_info theorem base0_5 : graphForm 11 edges0 (fun i => (env5 i).base) (fun _ => 0)=0 := by
  unfold edges0
  rw [FiniteTable.graphForm_table]
  decide +kernel

without_editor_info theorem cell0_5 {x y : ℤ} (hx : (11:ℤ)^3∣x-1324) (hy : (11:ℤ)^3∣y-843) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked5 i)

without_editor_info theorem linear1_5 : ∀ i : Fin 5, ∀ k : Fin 3, pairing 11 ((env5 i).directions k) (star 11 edges1 (fun i => (env5 i).base) (fun _ => 0) i)=0 := by
  intro i k; rw [fixedDirections5]; simp

without_editor_info theorem cross1_5 : ∀ e : Fin 1, ∀ k l : Fin 3, pairing 11 ((env5 (edges1 e).1).directions k) ((env5 (edges1 e).2).directions l)=0 := by
  intro e k l; rw [fixedDirections5]; simp

without_editor_info theorem base1_5 : graphForm 11 edges1 (fun i => (env5 i).base) (fun _ => 0)=0 := by
  unfold edges1
  rw [FiniteTable.graphForm_table]
  decide +kernel

without_editor_info theorem cell1_5 {x y : ℤ} (hx : (11:ℤ)^3∣x-1324) (hy : (11:ℤ)^3∣y-843) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked5 i)

without_editor_info theorem checked6 : ∀ i : Fin 5, (env5 i).check 11 3 (values 1203 117 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1203 117)) (by decide +kernel)

without_editor_info theorem cell0_6 {x y : ℤ} (hx : (11:ℤ)^3∣x-1203) (hy : (11:ℤ)^3∣y-117) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked6 i)

without_editor_info theorem cell1_6 {x y : ℤ} (hx : (11:ℤ)^3∣x-1203) (hy : (11:ℤ)^3∣y-117) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked6 i)

without_editor_info theorem checked7 : ∀ i : Fin 5, (env5 i).check 11 3 (values 1082 722 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1082 722)) (by decide +kernel)

without_editor_info theorem cell0_7 {x y : ℤ} (hx : (11:ℤ)^3∣x-1082) (hy : (11:ℤ)^3∣y-722) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked7 i)

without_editor_info theorem cell1_7 {x y : ℤ} (hx : (11:ℤ)^3∣x-1082) (hy : (11:ℤ)^3∣y-722) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked7 i)

without_editor_info theorem checked8 : ∀ i : Fin 5, (env5 i).check 11 3 (values 961 1327 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 961 1327)) (by decide +kernel)

without_editor_info theorem cell0_8 {x y : ℤ} (hx : (11:ℤ)^3∣x-961) (hy : (11:ℤ)^3∣y-1327) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked8 i)

without_editor_info theorem cell1_8 {x y : ℤ} (hx : (11:ℤ)^3∣x-961) (hy : (11:ℤ)^3∣y-1327) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked8 i)

without_editor_info theorem checked9 : ∀ i : Fin 5, (env5 i).check 11 3 (values 840 601 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 840 601)) (by decide +kernel)

without_editor_info theorem cell0_9 {x y : ℤ} (hx : (11:ℤ)^3∣x-840) (hy : (11:ℤ)^3∣y-601) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked9 i)

without_editor_info theorem cell1_9 {x y : ℤ} (hx : (11:ℤ)^3∣x-840) (hy : (11:ℤ)^3∣y-601) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked9 i)

without_editor_info theorem checked10 : ∀ i : Fin 5, (env5 i).check 11 3 (values 719 1206 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 719 1206)) (by decide +kernel)

without_editor_info theorem cell0_10 {x y : ℤ} (hx : (11:ℤ)^3∣x-719) (hy : (11:ℤ)^3∣y-1206) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked10 i)

without_editor_info theorem cell1_10 {x y : ℤ} (hx : (11:ℤ)^3∣x-719) (hy : (11:ℤ)^3∣y-1206) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked10 i)

without_editor_info theorem checked11 : ∀ i : Fin 5, (env5 i).check 11 3 (values 598 480 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 598 480)) (by decide +kernel)

without_editor_info theorem cell0_11 {x y : ℤ} (hx : (11:ℤ)^3∣x-598) (hy : (11:ℤ)^3∣y-480) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked11 i)

without_editor_info theorem cell1_11 {x y : ℤ} (hx : (11:ℤ)^3∣x-598) (hy : (11:ℤ)^3∣y-480) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked11 i)

without_editor_info theorem checked12 : ∀ i : Fin 5, (env5 i).check 11 3 (values 477 1085 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 477 1085)) (by decide +kernel)

without_editor_info theorem cell0_12 {x y : ℤ} (hx : (11:ℤ)^3∣x-477) (hy : (11:ℤ)^3∣y-1085) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked12 i)

without_editor_info theorem cell1_12 {x y : ℤ} (hx : (11:ℤ)^3∣x-477) (hy : (11:ℤ)^3∣y-1085) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked12 i)

without_editor_info theorem checked13 : ∀ i : Fin 5, (env5 i).check 11 3 (values 356 359 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 356 359)) (by decide +kernel)

without_editor_info theorem cell0_13 {x y : ℤ} (hx : (11:ℤ)^3∣x-356) (hy : (11:ℤ)^3∣y-359) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked13 i)

without_editor_info theorem cell1_13 {x y : ℤ} (hx : (11:ℤ)^3∣x-356) (hy : (11:ℤ)^3∣y-359) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked13 i)

without_editor_info theorem checked14 : ∀ i : Fin 5, (env5 i).check 11 3 (values 235 964 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 235 964)) (by decide +kernel)

without_editor_info theorem cell0_14 {x y : ℤ} (hx : (11:ℤ)^3∣x-235) (hy : (11:ℤ)^3∣y-964) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked14 i)

without_editor_info theorem cell1_14 {x y : ℤ} (hx : (11:ℤ)^3∣x-235) (hy : (11:ℤ)^3∣y-964) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked14 i)

without_editor_info theorem checked15 : ∀ i : Fin 5, (env5 i).check 11 3 (values 114 238 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 114 238)) (by decide +kernel)

without_editor_info theorem cell0_15 {x y : ℤ} (hx : (11:ℤ)^3∣x-114) (hy : (11:ℤ)^3∣y-238) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked15 i)

without_editor_info theorem cell1_15 {x y : ℤ} (hx : (11:ℤ)^3∣x-114) (hy : (11:ℤ)^3∣y-238) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked15 i)

without_editor_info def envData16 : Array Envelope := #[⟨![0,1,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,1,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩]

without_editor_info def env16 (i : Fin 5) : Envelope := envData16[i.val]'i.isLt

without_editor_info theorem checked16 : ∀ i : Fin 5, (env16 i).check 11 3 (values 1313 1019 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1313 1019)) (by decide +kernel)

without_editor_info theorem fixedDirections16 : ∀ i : Fin 5, (env16 i).directions=0 := by decide +kernel

without_editor_info theorem linear0_16 : ∀ i : Fin 5, ∀ k : Fin 3, pairing 11 ((env16 i).directions k) (star 11 edges0 (fun i => (env16 i).base) (fun _ => 0) i)=0 := by
  intro i k; rw [fixedDirections16]; simp

without_editor_info theorem cross0_16 : ∀ e : Fin 1, ∀ k l : Fin 3, pairing 11 ((env16 (edges0 e).1).directions k) ((env16 (edges0 e).2).directions l)=0 := by
  intro e k l; rw [fixedDirections16]; simp

without_editor_info theorem base0_16 : graphForm 11 edges0 (fun i => (env16 i).base) (fun _ => 0)=0 := by
  unfold edges0
  rw [FiniteTable.graphForm_table]
  decide +kernel

without_editor_info theorem cell0_16 {x y : ℤ} (hx : (11:ℤ)^3∣x-1313) (hy : (11:ℤ)^3∣y-1019) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked16 i)

without_editor_info theorem linear1_16 : ∀ i : Fin 5, ∀ k : Fin 3, pairing 11 ((env16 i).directions k) (star 11 edges1 (fun i => (env16 i).base) (fun _ => 0) i)=0 := by
  intro i k; rw [fixedDirections16]; simp

without_editor_info theorem cross1_16 : ∀ e : Fin 1, ∀ k l : Fin 3, pairing 11 ((env16 (edges1 e).1).directions k) ((env16 (edges1 e).2).directions l)=0 := by
  intro e k l; rw [fixedDirections16]; simp

without_editor_info theorem base1_16 : graphForm 11 edges1 (fun i => (env16 i).base) (fun _ => 0)=0 := by
  unfold edges1
  rw [FiniteTable.graphForm_table]
  decide +kernel

without_editor_info theorem cell1_16 {x y : ℤ} (hx : (11:ℤ)^3∣x-1313) (hy : (11:ℤ)^3∣y-1019) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked16 i)

without_editor_info theorem checked17 : ∀ i : Fin 5, (env16 i).check 11 3 (values 1192 293 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1192 293)) (by decide +kernel)

without_editor_info theorem cell0_17 {x y : ℤ} (hx : (11:ℤ)^3∣x-1192) (hy : (11:ℤ)^3∣y-293) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked17 i)

without_editor_info theorem cell1_17 {x y : ℤ} (hx : (11:ℤ)^3∣x-1192) (hy : (11:ℤ)^3∣y-293) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked17 i)

without_editor_info theorem checked18 : ∀ i : Fin 5, (env16 i).check 11 3 (values 1071 898 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1071 898)) (by decide +kernel)

without_editor_info theorem cell0_18 {x y : ℤ} (hx : (11:ℤ)^3∣x-1071) (hy : (11:ℤ)^3∣y-898) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked18 i)

without_editor_info theorem cell1_18 {x y : ℤ} (hx : (11:ℤ)^3∣x-1071) (hy : (11:ℤ)^3∣y-898) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked18 i)

without_editor_info theorem checked19 : ∀ i : Fin 5, (env16 i).check 11 3 (values 950 172 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 950 172)) (by decide +kernel)

without_editor_info theorem cell0_19 {x y : ℤ} (hx : (11:ℤ)^3∣x-950) (hy : (11:ℤ)^3∣y-172) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked19 i)

without_editor_info theorem cell1_19 {x y : ℤ} (hx : (11:ℤ)^3∣x-950) (hy : (11:ℤ)^3∣y-172) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked19 i)

without_editor_info theorem checked20 : ∀ i : Fin 5, (env16 i).check 11 3 (values 829 777 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 829 777)) (by decide +kernel)

without_editor_info theorem cell0_20 {x y : ℤ} (hx : (11:ℤ)^3∣x-829) (hy : (11:ℤ)^3∣y-777) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked20 i)

without_editor_info theorem cell1_20 {x y : ℤ} (hx : (11:ℤ)^3∣x-829) (hy : (11:ℤ)^3∣y-777) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked20 i)

without_editor_info theorem checked21 : ∀ i : Fin 5, (env16 i).check 11 3 (values 708 51 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 708 51)) (by decide +kernel)

without_editor_info theorem cell0_21 {x y : ℤ} (hx : (11:ℤ)^3∣x-708) (hy : (11:ℤ)^3∣y-51) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked21 i)

without_editor_info theorem cell1_21 {x y : ℤ} (hx : (11:ℤ)^3∣x-708) (hy : (11:ℤ)^3∣y-51) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked21 i)

without_editor_info theorem checked22 : ∀ i : Fin 5, (env16 i).check 11 3 (values 587 656 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 587 656)) (by decide +kernel)

without_editor_info theorem cell0_22 {x y : ℤ} (hx : (11:ℤ)^3∣x-587) (hy : (11:ℤ)^3∣y-656) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked22 i)

without_editor_info theorem cell1_22 {x y : ℤ} (hx : (11:ℤ)^3∣x-587) (hy : (11:ℤ)^3∣y-656) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked22 i)

without_editor_info theorem checked23 : ∀ i : Fin 5, (env16 i).check 11 3 (values 466 1261 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 466 1261)) (by decide +kernel)

without_editor_info theorem cell0_23 {x y : ℤ} (hx : (11:ℤ)^3∣x-466) (hy : (11:ℤ)^3∣y-1261) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked23 i)

without_editor_info theorem cell1_23 {x y : ℤ} (hx : (11:ℤ)^3∣x-466) (hy : (11:ℤ)^3∣y-1261) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked23 i)

without_editor_info theorem checked24 : ∀ i : Fin 5, (env16 i).check 11 3 (values 345 535 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 345 535)) (by decide +kernel)

without_editor_info theorem cell0_24 {x y : ℤ} (hx : (11:ℤ)^3∣x-345) (hy : (11:ℤ)^3∣y-535) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked24 i)

without_editor_info theorem cell1_24 {x y : ℤ} (hx : (11:ℤ)^3∣x-345) (hy : (11:ℤ)^3∣y-535) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked24 i)

without_editor_info theorem checked25 : ∀ i : Fin 5, (env16 i).check 11 3 (values 224 1140 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 224 1140)) (by decide +kernel)

without_editor_info theorem cell0_25 {x y : ℤ} (hx : (11:ℤ)^3∣x-224) (hy : (11:ℤ)^3∣y-1140) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked25 i)

without_editor_info theorem cell1_25 {x y : ℤ} (hx : (11:ℤ)^3∣x-224) (hy : (11:ℤ)^3∣y-1140) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked25 i)

without_editor_info theorem checked26 : ∀ i : Fin 5, (env16 i).check 11 3 (values 103 414 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 103 414)) (by decide +kernel)

without_editor_info theorem cell0_26 {x y : ℤ} (hx : (11:ℤ)^3∣x-103) (hy : (11:ℤ)^3∣y-414) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked26 i)

without_editor_info theorem cell1_26 {x y : ℤ} (hx : (11:ℤ)^3∣x-103) (hy : (11:ℤ)^3∣y-414) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked26 i)

without_editor_info theorem checked27 : ∀ i : Fin 5, (env5 i).check 11 3 (values 1302 227 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1302 227)) (by decide +kernel)

without_editor_info theorem cell0_27 {x y : ℤ} (hx : (11:ℤ)^3∣x-1302) (hy : (11:ℤ)^3∣y-227) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked27 i)

without_editor_info theorem cell1_27 {x y : ℤ} (hx : (11:ℤ)^3∣x-1302) (hy : (11:ℤ)^3∣y-227) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked27 i)

without_editor_info theorem checked28 : ∀ i : Fin 5, (env5 i).check 11 3 (values 1181 832 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1181 832)) (by decide +kernel)

without_editor_info theorem cell0_28 {x y : ℤ} (hx : (11:ℤ)^3∣x-1181) (hy : (11:ℤ)^3∣y-832) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked28 i)

without_editor_info theorem cell1_28 {x y : ℤ} (hx : (11:ℤ)^3∣x-1181) (hy : (11:ℤ)^3∣y-832) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked28 i)

without_editor_info theorem checked29 : ∀ i : Fin 5, (env5 i).check 11 3 (values 1060 106 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1060 106)) (by decide +kernel)

without_editor_info theorem cell0_29 {x y : ℤ} (hx : (11:ℤ)^3∣x-1060) (hy : (11:ℤ)^3∣y-106) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked29 i)

without_editor_info theorem cell1_29 {x y : ℤ} (hx : (11:ℤ)^3∣x-1060) (hy : (11:ℤ)^3∣y-106) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked29 i)

without_editor_info theorem checked30 : ∀ i : Fin 5, (env5 i).check 11 3 (values 939 711 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 939 711)) (by decide +kernel)

without_editor_info theorem cell0_30 {x y : ℤ} (hx : (11:ℤ)^3∣x-939) (hy : (11:ℤ)^3∣y-711) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked30 i)

without_editor_info theorem cell1_30 {x y : ℤ} (hx : (11:ℤ)^3∣x-939) (hy : (11:ℤ)^3∣y-711) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked30 i)

without_editor_info theorem checked31 : ∀ i : Fin 5, (env5 i).check 11 3 (values 818 1316 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 818 1316)) (by decide +kernel)

without_editor_info theorem cell0_31 {x y : ℤ} (hx : (11:ℤ)^3∣x-818) (hy : (11:ℤ)^3∣y-1316) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked31 i)

without_editor_info theorem cell1_31 {x y : ℤ} (hx : (11:ℤ)^3∣x-818) (hy : (11:ℤ)^3∣y-1316) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked31 i)

without_editor_info theorem checked32 : ∀ i : Fin 5, (env5 i).check 11 3 (values 697 590 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 697 590)) (by decide +kernel)

without_editor_info theorem cell0_32 {x y : ℤ} (hx : (11:ℤ)^3∣x-697) (hy : (11:ℤ)^3∣y-590) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked32 i)

without_editor_info theorem cell1_32 {x y : ℤ} (hx : (11:ℤ)^3∣x-697) (hy : (11:ℤ)^3∣y-590) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked32 i)

without_editor_info theorem checked33 : ∀ i : Fin 5, (env5 i).check 11 3 (values 576 1195 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 576 1195)) (by decide +kernel)

without_editor_info theorem cell0_33 {x y : ℤ} (hx : (11:ℤ)^3∣x-576) (hy : (11:ℤ)^3∣y-1195) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked33 i)

without_editor_info theorem cell1_33 {x y : ℤ} (hx : (11:ℤ)^3∣x-576) (hy : (11:ℤ)^3∣y-1195) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked33 i)

without_editor_info theorem checked34 : ∀ i : Fin 5, (env5 i).check 11 3 (values 455 469 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 455 469)) (by decide +kernel)

without_editor_info theorem cell0_34 {x y : ℤ} (hx : (11:ℤ)^3∣x-455) (hy : (11:ℤ)^3∣y-469) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked34 i)

without_editor_info theorem cell1_34 {x y : ℤ} (hx : (11:ℤ)^3∣x-455) (hy : (11:ℤ)^3∣y-469) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked34 i)

without_editor_info theorem checked35 : ∀ i : Fin 5, (env5 i).check 11 3 (values 334 1074 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 334 1074)) (by decide +kernel)

without_editor_info theorem cell0_35 {x y : ℤ} (hx : (11:ℤ)^3∣x-334) (hy : (11:ℤ)^3∣y-1074) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked35 i)

without_editor_info theorem cell1_35 {x y : ℤ} (hx : (11:ℤ)^3∣x-334) (hy : (11:ℤ)^3∣y-1074) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked35 i)

without_editor_info theorem checked36 : ∀ i : Fin 5, (env5 i).check 11 3 (values 213 348 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 213 348)) (by decide +kernel)

without_editor_info theorem cell0_36 {x y : ℤ} (hx : (11:ℤ)^3∣x-213) (hy : (11:ℤ)^3∣y-348) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked36 i)

without_editor_info theorem cell1_36 {x y : ℤ} (hx : (11:ℤ)^3∣x-213) (hy : (11:ℤ)^3∣y-348) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked36 i)

without_editor_info theorem checked37 : ∀ i : Fin 5, (env5 i).check 11 3 (values 92 953 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 92 953)) (by decide +kernel)

without_editor_info theorem cell0_37 {x y : ℤ} (hx : (11:ℤ)^3∣x-92) (hy : (11:ℤ)^3∣y-953) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked37 i)

without_editor_info theorem cell1_37 {x y : ℤ} (hx : (11:ℤ)^3∣x-92) (hy : (11:ℤ)^3∣y-953) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked37 i)

without_editor_info theorem checked38 : ∀ i : Fin 5, (env16 i).check 11 3 (values 1291 1129 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1291 1129)) (by decide +kernel)

without_editor_info theorem cell0_38 {x y : ℤ} (hx : (11:ℤ)^3∣x-1291) (hy : (11:ℤ)^3∣y-1129) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked38 i)

without_editor_info theorem cell1_38 {x y : ℤ} (hx : (11:ℤ)^3∣x-1291) (hy : (11:ℤ)^3∣y-1129) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked38 i)

without_editor_info theorem checked39 : ∀ i : Fin 5, (env16 i).check 11 3 (values 1170 403 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1170 403)) (by decide +kernel)

without_editor_info theorem cell0_39 {x y : ℤ} (hx : (11:ℤ)^3∣x-1170) (hy : (11:ℤ)^3∣y-403) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked39 i)

without_editor_info theorem cell1_39 {x y : ℤ} (hx : (11:ℤ)^3∣x-1170) (hy : (11:ℤ)^3∣y-403) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked39 i)

without_editor_info theorem checked40 : ∀ i : Fin 5, (env16 i).check 11 3 (values 1049 1008 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1049 1008)) (by decide +kernel)

without_editor_info theorem cell0_40 {x y : ℤ} (hx : (11:ℤ)^3∣x-1049) (hy : (11:ℤ)^3∣y-1008) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked40 i)

without_editor_info theorem cell1_40 {x y : ℤ} (hx : (11:ℤ)^3∣x-1049) (hy : (11:ℤ)^3∣y-1008) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked40 i)

without_editor_info theorem checked41 : ∀ i : Fin 5, (env16 i).check 11 3 (values 928 282 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 928 282)) (by decide +kernel)

without_editor_info theorem cell0_41 {x y : ℤ} (hx : (11:ℤ)^3∣x-928) (hy : (11:ℤ)^3∣y-282) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked41 i)

without_editor_info theorem cell1_41 {x y : ℤ} (hx : (11:ℤ)^3∣x-928) (hy : (11:ℤ)^3∣y-282) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked41 i)

without_editor_info theorem checked42 : ∀ i : Fin 5, (env16 i).check 11 3 (values 807 887 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 807 887)) (by decide +kernel)

without_editor_info theorem cell0_42 {x y : ℤ} (hx : (11:ℤ)^3∣x-807) (hy : (11:ℤ)^3∣y-887) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked42 i)

without_editor_info theorem cell1_42 {x y : ℤ} (hx : (11:ℤ)^3∣x-807) (hy : (11:ℤ)^3∣y-887) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked42 i)

without_editor_info theorem checked43 : ∀ i : Fin 5, (env16 i).check 11 3 (values 686 161 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 686 161)) (by decide +kernel)

without_editor_info theorem cell0_43 {x y : ℤ} (hx : (11:ℤ)^3∣x-686) (hy : (11:ℤ)^3∣y-161) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked43 i)

without_editor_info theorem cell1_43 {x y : ℤ} (hx : (11:ℤ)^3∣x-686) (hy : (11:ℤ)^3∣y-161) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked43 i)

without_editor_info theorem checked44 : ∀ i : Fin 5, (env16 i).check 11 3 (values 565 766 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 565 766)) (by decide +kernel)

without_editor_info theorem cell0_44 {x y : ℤ} (hx : (11:ℤ)^3∣x-565) (hy : (11:ℤ)^3∣y-766) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked44 i)

without_editor_info theorem cell1_44 {x y : ℤ} (hx : (11:ℤ)^3∣x-565) (hy : (11:ℤ)^3∣y-766) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked44 i)

without_editor_info theorem checked45 : ∀ i : Fin 5, (env16 i).check 11 3 (values 444 40 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 444 40)) (by decide +kernel)

without_editor_info theorem cell0_45 {x y : ℤ} (hx : (11:ℤ)^3∣x-444) (hy : (11:ℤ)^3∣y-40) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked45 i)

without_editor_info theorem cell1_45 {x y : ℤ} (hx : (11:ℤ)^3∣x-444) (hy : (11:ℤ)^3∣y-40) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked45 i)

without_editor_info theorem checked46 : ∀ i : Fin 5, (env16 i).check 11 3 (values 323 645 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 323 645)) (by decide +kernel)

without_editor_info theorem cell0_46 {x y : ℤ} (hx : (11:ℤ)^3∣x-323) (hy : (11:ℤ)^3∣y-645) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked46 i)

without_editor_info theorem cell1_46 {x y : ℤ} (hx : (11:ℤ)^3∣x-323) (hy : (11:ℤ)^3∣y-645) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked46 i)

without_editor_info theorem checked47 : ∀ i : Fin 5, (env16 i).check 11 3 (values 202 1250 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 202 1250)) (by decide +kernel)

without_editor_info theorem cell0_47 {x y : ℤ} (hx : (11:ℤ)^3∣x-202) (hy : (11:ℤ)^3∣y-1250) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked47 i)

without_editor_info theorem cell1_47 {x y : ℤ} (hx : (11:ℤ)^3∣x-202) (hy : (11:ℤ)^3∣y-1250) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked47 i)

without_editor_info theorem checked48 : ∀ i : Fin 5, (env16 i).check 11 3 (values 81 524 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 81 524)) (by decide +kernel)

without_editor_info theorem cell0_48 {x y : ℤ} (hx : (11:ℤ)^3∣x-81) (hy : (11:ℤ)^3∣y-524) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked48 i)

without_editor_info theorem cell1_48 {x y : ℤ} (hx : (11:ℤ)^3∣x-81) (hy : (11:ℤ)^3∣y-524) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked48 i)

without_editor_info theorem checked49 : ∀ i : Fin 5, (env16 i).check 11 3 (values 1280 1063 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1280 1063)) (by decide +kernel)

without_editor_info theorem cell0_49 {x y : ℤ} (hx : (11:ℤ)^3∣x-1280) (hy : (11:ℤ)^3∣y-1063) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked49 i)

without_editor_info theorem cell1_49 {x y : ℤ} (hx : (11:ℤ)^3∣x-1280) (hy : (11:ℤ)^3∣y-1063) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked49 i)

without_editor_info theorem checked50 : ∀ i : Fin 5, (env16 i).check 11 3 (values 1159 337 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1159 337)) (by decide +kernel)

without_editor_info theorem cell0_50 {x y : ℤ} (hx : (11:ℤ)^3∣x-1159) (hy : (11:ℤ)^3∣y-337) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked50 i)

without_editor_info theorem cell1_50 {x y : ℤ} (hx : (11:ℤ)^3∣x-1159) (hy : (11:ℤ)^3∣y-337) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked50 i)

without_editor_info theorem checked51 : ∀ i : Fin 5, (env16 i).check 11 3 (values 1038 942 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1038 942)) (by decide +kernel)

without_editor_info theorem cell0_51 {x y : ℤ} (hx : (11:ℤ)^3∣x-1038) (hy : (11:ℤ)^3∣y-942) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked51 i)

without_editor_info theorem cell1_51 {x y : ℤ} (hx : (11:ℤ)^3∣x-1038) (hy : (11:ℤ)^3∣y-942) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked51 i)

without_editor_info theorem checked52 : ∀ i : Fin 5, (env16 i).check 11 3 (values 917 216 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 917 216)) (by decide +kernel)

without_editor_info theorem cell0_52 {x y : ℤ} (hx : (11:ℤ)^3∣x-917) (hy : (11:ℤ)^3∣y-216) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked52 i)

without_editor_info theorem cell1_52 {x y : ℤ} (hx : (11:ℤ)^3∣x-917) (hy : (11:ℤ)^3∣y-216) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked52 i)

without_editor_info theorem checked53 : ∀ i : Fin 5, (env16 i).check 11 3 (values 796 821 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 796 821)) (by decide +kernel)

without_editor_info theorem cell0_53 {x y : ℤ} (hx : (11:ℤ)^3∣x-796) (hy : (11:ℤ)^3∣y-821) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked53 i)

without_editor_info theorem cell1_53 {x y : ℤ} (hx : (11:ℤ)^3∣x-796) (hy : (11:ℤ)^3∣y-821) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked53 i)

without_editor_info theorem checked54 : ∀ i : Fin 5, (env16 i).check 11 3 (values 675 95 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 675 95)) (by decide +kernel)

without_editor_info theorem cell0_54 {x y : ℤ} (hx : (11:ℤ)^3∣x-675) (hy : (11:ℤ)^3∣y-95) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked54 i)

without_editor_info theorem cell1_54 {x y : ℤ} (hx : (11:ℤ)^3∣x-675) (hy : (11:ℤ)^3∣y-95) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked54 i)

without_editor_info theorem checked55 : ∀ i : Fin 5, (env16 i).check 11 3 (values 554 700 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 554 700)) (by decide +kernel)

without_editor_info theorem cell0_55 {x y : ℤ} (hx : (11:ℤ)^3∣x-554) (hy : (11:ℤ)^3∣y-700) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked55 i)

without_editor_info theorem cell1_55 {x y : ℤ} (hx : (11:ℤ)^3∣x-554) (hy : (11:ℤ)^3∣y-700) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked55 i)

without_editor_info theorem checked56 : ∀ i : Fin 5, (env16 i).check 11 3 (values 433 1305 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 433 1305)) (by decide +kernel)

without_editor_info theorem cell0_56 {x y : ℤ} (hx : (11:ℤ)^3∣x-433) (hy : (11:ℤ)^3∣y-1305) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked56 i)

without_editor_info theorem cell1_56 {x y : ℤ} (hx : (11:ℤ)^3∣x-433) (hy : (11:ℤ)^3∣y-1305) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked56 i)

without_editor_info theorem checked57 : ∀ i : Fin 5, (env16 i).check 11 3 (values 312 579 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 312 579)) (by decide +kernel)

without_editor_info theorem cell0_57 {x y : ℤ} (hx : (11:ℤ)^3∣x-312) (hy : (11:ℤ)^3∣y-579) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked57 i)

without_editor_info theorem cell1_57 {x y : ℤ} (hx : (11:ℤ)^3∣x-312) (hy : (11:ℤ)^3∣y-579) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked57 i)

without_editor_info theorem checked58 : ∀ i : Fin 5, (env16 i).check 11 3 (values 191 1184 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 191 1184)) (by decide +kernel)

without_editor_info theorem cell0_58 {x y : ℤ} (hx : (11:ℤ)^3∣x-191) (hy : (11:ℤ)^3∣y-1184) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked58 i)

without_editor_info theorem cell1_58 {x y : ℤ} (hx : (11:ℤ)^3∣x-191) (hy : (11:ℤ)^3∣y-1184) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked58 i)

without_editor_info theorem checked59 : ∀ i : Fin 5, (env16 i).check 11 3 (values 70 458 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 70 458)) (by decide +kernel)

without_editor_info theorem cell0_59 {x y : ℤ} (hx : (11:ℤ)^3∣x-70) (hy : (11:ℤ)^3∣y-458) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked59 i)

without_editor_info theorem cell1_59 {x y : ℤ} (hx : (11:ℤ)^3∣x-70) (hy : (11:ℤ)^3∣y-458) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked59 i)

without_editor_info theorem checked60 : ∀ i : Fin 5, (env5 i).check 11 3 (values 1269 29 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1269 29)) (by decide +kernel)

without_editor_info theorem cell0_60 {x y : ℤ} (hx : (11:ℤ)^3∣x-1269) (hy : (11:ℤ)^3∣y-29) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked60 i)

without_editor_info theorem cell1_60 {x y : ℤ} (hx : (11:ℤ)^3∣x-1269) (hy : (11:ℤ)^3∣y-29) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked60 i)

without_editor_info theorem checked61 : ∀ i : Fin 5, (env5 i).check 11 3 (values 1148 634 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1148 634)) (by decide +kernel)

without_editor_info theorem cell0_61 {x y : ℤ} (hx : (11:ℤ)^3∣x-1148) (hy : (11:ℤ)^3∣y-634) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked61 i)

without_editor_info theorem cell1_61 {x y : ℤ} (hx : (11:ℤ)^3∣x-1148) (hy : (11:ℤ)^3∣y-634) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked61 i)

without_editor_info theorem checked62 : ∀ i : Fin 5, (env5 i).check 11 3 (values 1027 1239 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1027 1239)) (by decide +kernel)

without_editor_info theorem cell0_62 {x y : ℤ} (hx : (11:ℤ)^3∣x-1027) (hy : (11:ℤ)^3∣y-1239) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked62 i)

without_editor_info theorem cell1_62 {x y : ℤ} (hx : (11:ℤ)^3∣x-1027) (hy : (11:ℤ)^3∣y-1239) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked62 i)

without_editor_info theorem checked63 : ∀ i : Fin 5, (env5 i).check 11 3 (values 906 513 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 906 513)) (by decide +kernel)

without_editor_info theorem cell0_63 {x y : ℤ} (hx : (11:ℤ)^3∣x-906) (hy : (11:ℤ)^3∣y-513) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked63 i)

without_editor_info theorem cell1_63 {x y : ℤ} (hx : (11:ℤ)^3∣x-906) (hy : (11:ℤ)^3∣y-513) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked63 i)

without_editor_info theorem checked64 : ∀ i : Fin 5, (env5 i).check 11 3 (values 785 1118 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 785 1118)) (by decide +kernel)

without_editor_info theorem cell0_64 {x y : ℤ} (hx : (11:ℤ)^3∣x-785) (hy : (11:ℤ)^3∣y-1118) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked64 i)

without_editor_info theorem cell1_64 {x y : ℤ} (hx : (11:ℤ)^3∣x-785) (hy : (11:ℤ)^3∣y-1118) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked64 i)

without_editor_info theorem checked65 : ∀ i : Fin 5, (env5 i).check 11 3 (values 664 392 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 664 392)) (by decide +kernel)

without_editor_info theorem cell0_65 {x y : ℤ} (hx : (11:ℤ)^3∣x-664) (hy : (11:ℤ)^3∣y-392) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked65 i)

without_editor_info theorem cell1_65 {x y : ℤ} (hx : (11:ℤ)^3∣x-664) (hy : (11:ℤ)^3∣y-392) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked65 i)

without_editor_info theorem checked66 : ∀ i : Fin 5, (env5 i).check 11 3 (values 543 997 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 543 997)) (by decide +kernel)

without_editor_info theorem cell0_66 {x y : ℤ} (hx : (11:ℤ)^3∣x-543) (hy : (11:ℤ)^3∣y-997) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked66 i)

without_editor_info theorem cell1_66 {x y : ℤ} (hx : (11:ℤ)^3∣x-543) (hy : (11:ℤ)^3∣y-997) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked66 i)

without_editor_info theorem checked67 : ∀ i : Fin 5, (env5 i).check 11 3 (values 422 271 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 422 271)) (by decide +kernel)

without_editor_info theorem cell0_67 {x y : ℤ} (hx : (11:ℤ)^3∣x-422) (hy : (11:ℤ)^3∣y-271) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked67 i)

without_editor_info theorem cell1_67 {x y : ℤ} (hx : (11:ℤ)^3∣x-422) (hy : (11:ℤ)^3∣y-271) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked67 i)

without_editor_info theorem checked68 : ∀ i : Fin 5, (env5 i).check 11 3 (values 301 876 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 301 876)) (by decide +kernel)

without_editor_info theorem cell0_68 {x y : ℤ} (hx : (11:ℤ)^3∣x-301) (hy : (11:ℤ)^3∣y-876) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked68 i)

without_editor_info theorem cell1_68 {x y : ℤ} (hx : (11:ℤ)^3∣x-301) (hy : (11:ℤ)^3∣y-876) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked68 i)

without_editor_info theorem checked69 : ∀ i : Fin 5, (env5 i).check 11 3 (values 180 150 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 180 150)) (by decide +kernel)

without_editor_info theorem cell0_69 {x y : ℤ} (hx : (11:ℤ)^3∣x-180) (hy : (11:ℤ)^3∣y-150) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked69 i)

without_editor_info theorem cell1_69 {x y : ℤ} (hx : (11:ℤ)^3∣x-180) (hy : (11:ℤ)^3∣y-150) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked69 i)

without_editor_info theorem checked70 : ∀ i : Fin 5, (env5 i).check 11 3 (values 59 755 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 59 755)) (by decide +kernel)

without_editor_info theorem cell0_70 {x y : ℤ} (hx : (11:ℤ)^3∣x-59) (hy : (11:ℤ)^3∣y-755) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked70 i)

without_editor_info theorem cell1_70 {x y : ℤ} (hx : (11:ℤ)^3∣x-59) (hy : (11:ℤ)^3∣y-755) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked70 i)

without_editor_info theorem checked71 : ∀ i : Fin 5, (env5 i).check 11 3 (values 1258 689 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1258 689)) (by decide +kernel)

without_editor_info theorem cell0_71 {x y : ℤ} (hx : (11:ℤ)^3∣x-1258) (hy : (11:ℤ)^3∣y-689) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked71 i)

without_editor_info theorem cell1_71 {x y : ℤ} (hx : (11:ℤ)^3∣x-1258) (hy : (11:ℤ)^3∣y-689) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked71 i)

without_editor_info theorem checked72 : ∀ i : Fin 5, (env5 i).check 11 3 (values 1137 1294 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1137 1294)) (by decide +kernel)

without_editor_info theorem cell0_72 {x y : ℤ} (hx : (11:ℤ)^3∣x-1137) (hy : (11:ℤ)^3∣y-1294) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked72 i)

without_editor_info theorem cell1_72 {x y : ℤ} (hx : (11:ℤ)^3∣x-1137) (hy : (11:ℤ)^3∣y-1294) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked72 i)

without_editor_info theorem checked73 : ∀ i : Fin 5, (env5 i).check 11 3 (values 1016 568 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1016 568)) (by decide +kernel)

without_editor_info theorem cell0_73 {x y : ℤ} (hx : (11:ℤ)^3∣x-1016) (hy : (11:ℤ)^3∣y-568) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked73 i)

without_editor_info theorem cell1_73 {x y : ℤ} (hx : (11:ℤ)^3∣x-1016) (hy : (11:ℤ)^3∣y-568) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked73 i)

without_editor_info theorem checked74 : ∀ i : Fin 5, (env5 i).check 11 3 (values 895 1173 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 895 1173)) (by decide +kernel)

without_editor_info theorem cell0_74 {x y : ℤ} (hx : (11:ℤ)^3∣x-895) (hy : (11:ℤ)^3∣y-1173) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked74 i)

without_editor_info theorem cell1_74 {x y : ℤ} (hx : (11:ℤ)^3∣x-895) (hy : (11:ℤ)^3∣y-1173) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked74 i)

without_editor_info theorem checked75 : ∀ i : Fin 5, (env5 i).check 11 3 (values 774 447 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 774 447)) (by decide +kernel)

without_editor_info theorem cell0_75 {x y : ℤ} (hx : (11:ℤ)^3∣x-774) (hy : (11:ℤ)^3∣y-447) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked75 i)

without_editor_info theorem cell1_75 {x y : ℤ} (hx : (11:ℤ)^3∣x-774) (hy : (11:ℤ)^3∣y-447) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked75 i)

without_editor_info theorem checked76 : ∀ i : Fin 5, (env5 i).check 11 3 (values 653 1052 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 653 1052)) (by decide +kernel)

without_editor_info theorem cell0_76 {x y : ℤ} (hx : (11:ℤ)^3∣x-653) (hy : (11:ℤ)^3∣y-1052) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked76 i)

without_editor_info theorem cell1_76 {x y : ℤ} (hx : (11:ℤ)^3∣x-653) (hy : (11:ℤ)^3∣y-1052) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked76 i)

without_editor_info theorem checked77 : ∀ i : Fin 5, (env5 i).check 11 3 (values 532 326 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 532 326)) (by decide +kernel)

without_editor_info theorem cell0_77 {x y : ℤ} (hx : (11:ℤ)^3∣x-532) (hy : (11:ℤ)^3∣y-326) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked77 i)

without_editor_info theorem cell1_77 {x y : ℤ} (hx : (11:ℤ)^3∣x-532) (hy : (11:ℤ)^3∣y-326) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked77 i)

without_editor_info theorem checked78 : ∀ i : Fin 5, (env5 i).check 11 3 (values 411 931 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 411 931)) (by decide +kernel)

without_editor_info theorem cell0_78 {x y : ℤ} (hx : (11:ℤ)^3∣x-411) (hy : (11:ℤ)^3∣y-931) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked78 i)

without_editor_info theorem cell1_78 {x y : ℤ} (hx : (11:ℤ)^3∣x-411) (hy : (11:ℤ)^3∣y-931) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked78 i)

without_editor_info theorem checked79 : ∀ i : Fin 5, (env5 i).check 11 3 (values 290 205 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 290 205)) (by decide +kernel)

without_editor_info theorem cell0_79 {x y : ℤ} (hx : (11:ℤ)^3∣x-290) (hy : (11:ℤ)^3∣y-205) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked79 i)

without_editor_info theorem cell1_79 {x y : ℤ} (hx : (11:ℤ)^3∣x-290) (hy : (11:ℤ)^3∣y-205) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked79 i)

without_editor_info theorem checked80 : ∀ i : Fin 5, (env5 i).check 11 3 (values 169 810 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 169 810)) (by decide +kernel)

without_editor_info theorem cell0_80 {x y : ℤ} (hx : (11:ℤ)^3∣x-169) (hy : (11:ℤ)^3∣y-810) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked80 i)

without_editor_info theorem cell1_80 {x y : ℤ} (hx : (11:ℤ)^3∣x-169) (hy : (11:ℤ)^3∣y-810) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked80 i)

without_editor_info theorem checked81 : ∀ i : Fin 5, (env5 i).check 11 3 (values 48 84 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 48 84)) (by decide +kernel)

without_editor_info theorem cell0_81 {x y : ℤ} (hx : (11:ℤ)^3∣x-48) (hy : (11:ℤ)^3∣y-84) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked81 i)

without_editor_info theorem cell1_81 {x y : ℤ} (hx : (11:ℤ)^3∣x-48) (hy : (11:ℤ)^3∣y-84) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked81 i)

without_editor_info theorem checked82 : ∀ i : Fin 5, (env16 i).check 11 3 (values 1247 381 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1247 381)) (by decide +kernel)

without_editor_info theorem cell0_82 {x y : ℤ} (hx : (11:ℤ)^3∣x-1247) (hy : (11:ℤ)^3∣y-381) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked82 i)

without_editor_info theorem cell1_82 {x y : ℤ} (hx : (11:ℤ)^3∣x-1247) (hy : (11:ℤ)^3∣y-381) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked82 i)

without_editor_info theorem checked83 : ∀ i : Fin 5, (env16 i).check 11 3 (values 1126 986 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1126 986)) (by decide +kernel)

without_editor_info theorem cell0_83 {x y : ℤ} (hx : (11:ℤ)^3∣x-1126) (hy : (11:ℤ)^3∣y-986) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked83 i)

without_editor_info theorem cell1_83 {x y : ℤ} (hx : (11:ℤ)^3∣x-1126) (hy : (11:ℤ)^3∣y-986) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked83 i)

without_editor_info theorem checked84 : ∀ i : Fin 5, (env16 i).check 11 3 (values 1005 260 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1005 260)) (by decide +kernel)

without_editor_info theorem cell0_84 {x y : ℤ} (hx : (11:ℤ)^3∣x-1005) (hy : (11:ℤ)^3∣y-260) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked84 i)

without_editor_info theorem cell1_84 {x y : ℤ} (hx : (11:ℤ)^3∣x-1005) (hy : (11:ℤ)^3∣y-260) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked84 i)

without_editor_info theorem checked85 : ∀ i : Fin 5, (env16 i).check 11 3 (values 884 865 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 884 865)) (by decide +kernel)

without_editor_info theorem cell0_85 {x y : ℤ} (hx : (11:ℤ)^3∣x-884) (hy : (11:ℤ)^3∣y-865) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked85 i)

without_editor_info theorem cell1_85 {x y : ℤ} (hx : (11:ℤ)^3∣x-884) (hy : (11:ℤ)^3∣y-865) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked85 i)

without_editor_info theorem checked86 : ∀ i : Fin 5, (env16 i).check 11 3 (values 763 139 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 763 139)) (by decide +kernel)

without_editor_info theorem cell0_86 {x y : ℤ} (hx : (11:ℤ)^3∣x-763) (hy : (11:ℤ)^3∣y-139) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked86 i)

without_editor_info theorem cell1_86 {x y : ℤ} (hx : (11:ℤ)^3∣x-763) (hy : (11:ℤ)^3∣y-139) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked86 i)

without_editor_info theorem checked87 : ∀ i : Fin 5, (env16 i).check 11 3 (values 642 744 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 642 744)) (by decide +kernel)

without_editor_info theorem cell0_87 {x y : ℤ} (hx : (11:ℤ)^3∣x-642) (hy : (11:ℤ)^3∣y-744) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked87 i)

without_editor_info theorem cell1_87 {x y : ℤ} (hx : (11:ℤ)^3∣x-642) (hy : (11:ℤ)^3∣y-744) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked87 i)

without_editor_info theorem checked88 : ∀ i : Fin 5, (env16 i).check 11 3 (values 521 18 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 521 18)) (by decide +kernel)

without_editor_info theorem cell0_88 {x y : ℤ} (hx : (11:ℤ)^3∣x-521) (hy : (11:ℤ)^3∣y-18) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked88 i)

without_editor_info theorem cell1_88 {x y : ℤ} (hx : (11:ℤ)^3∣x-521) (hy : (11:ℤ)^3∣y-18) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked88 i)

without_editor_info theorem checked89 : ∀ i : Fin 5, (env16 i).check 11 3 (values 400 623 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 400 623)) (by decide +kernel)

without_editor_info theorem cell0_89 {x y : ℤ} (hx : (11:ℤ)^3∣x-400) (hy : (11:ℤ)^3∣y-623) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked89 i)

without_editor_info theorem cell1_89 {x y : ℤ} (hx : (11:ℤ)^3∣x-400) (hy : (11:ℤ)^3∣y-623) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked89 i)

without_editor_info theorem checked90 : ∀ i : Fin 5, (env16 i).check 11 3 (values 279 1228 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 279 1228)) (by decide +kernel)

without_editor_info theorem cell0_90 {x y : ℤ} (hx : (11:ℤ)^3∣x-279) (hy : (11:ℤ)^3∣y-1228) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked90 i)

without_editor_info theorem cell1_90 {x y : ℤ} (hx : (11:ℤ)^3∣x-279) (hy : (11:ℤ)^3∣y-1228) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked90 i)

without_editor_info theorem checked91 : ∀ i : Fin 5, (env16 i).check 11 3 (values 158 502 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 158 502)) (by decide +kernel)

without_editor_info theorem cell0_91 {x y : ℤ} (hx : (11:ℤ)^3∣x-158) (hy : (11:ℤ)^3∣y-502) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked91 i)

without_editor_info theorem cell1_91 {x y : ℤ} (hx : (11:ℤ)^3∣x-158) (hy : (11:ℤ)^3∣y-502) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked91 i)

without_editor_info theorem checked92 : ∀ i : Fin 5, (env16 i).check 11 3 (values 37 1107 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 37 1107)) (by decide +kernel)

without_editor_info theorem cell0_92 {x y : ℤ} (hx : (11:ℤ)^3∣x-37) (hy : (11:ℤ)^3∣y-1107) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked92 i)

without_editor_info theorem cell1_92 {x y : ℤ} (hx : (11:ℤ)^3∣x-37) (hy : (11:ℤ)^3∣y-1107) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked92 i)

without_editor_info theorem checked93 : ∀ i : Fin 5, (env16 i).check 11 3 (values 1236 436 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1236 436)) (by decide +kernel)

without_editor_info theorem cell0_93 {x y : ℤ} (hx : (11:ℤ)^3∣x-1236) (hy : (11:ℤ)^3∣y-436) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked93 i)

without_editor_info theorem cell1_93 {x y : ℤ} (hx : (11:ℤ)^3∣x-1236) (hy : (11:ℤ)^3∣y-436) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked93 i)

without_editor_info theorem checked94 : ∀ i : Fin 5, (env16 i).check 11 3 (values 1115 1041 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1115 1041)) (by decide +kernel)

without_editor_info theorem cell0_94 {x y : ℤ} (hx : (11:ℤ)^3∣x-1115) (hy : (11:ℤ)^3∣y-1041) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked94 i)

without_editor_info theorem cell1_94 {x y : ℤ} (hx : (11:ℤ)^3∣x-1115) (hy : (11:ℤ)^3∣y-1041) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked94 i)

without_editor_info theorem checked95 : ∀ i : Fin 5, (env16 i).check 11 3 (values 994 315 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 994 315)) (by decide +kernel)

without_editor_info theorem cell0_95 {x y : ℤ} (hx : (11:ℤ)^3∣x-994) (hy : (11:ℤ)^3∣y-315) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked95 i)

without_editor_info theorem cell1_95 {x y : ℤ} (hx : (11:ℤ)^3∣x-994) (hy : (11:ℤ)^3∣y-315) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked95 i)

without_editor_info theorem checked96 : ∀ i : Fin 5, (env16 i).check 11 3 (values 873 920 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 873 920)) (by decide +kernel)

without_editor_info theorem cell0_96 {x y : ℤ} (hx : (11:ℤ)^3∣x-873) (hy : (11:ℤ)^3∣y-920) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked96 i)

without_editor_info theorem cell1_96 {x y : ℤ} (hx : (11:ℤ)^3∣x-873) (hy : (11:ℤ)^3∣y-920) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked96 i)

without_editor_info theorem checked97 : ∀ i : Fin 5, (env16 i).check 11 3 (values 752 194 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 752 194)) (by decide +kernel)

without_editor_info theorem cell0_97 {x y : ℤ} (hx : (11:ℤ)^3∣x-752) (hy : (11:ℤ)^3∣y-194) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked97 i)

without_editor_info theorem cell1_97 {x y : ℤ} (hx : (11:ℤ)^3∣x-752) (hy : (11:ℤ)^3∣y-194) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked97 i)

without_editor_info theorem checked98 : ∀ i : Fin 5, (env16 i).check 11 3 (values 631 799 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 631 799)) (by decide +kernel)

without_editor_info theorem cell0_98 {x y : ℤ} (hx : (11:ℤ)^3∣x-631) (hy : (11:ℤ)^3∣y-799) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked98 i)

without_editor_info theorem cell1_98 {x y : ℤ} (hx : (11:ℤ)^3∣x-631) (hy : (11:ℤ)^3∣y-799) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked98 i)

without_editor_info theorem checked99 : ∀ i : Fin 5, (env16 i).check 11 3 (values 510 73 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 510 73)) (by decide +kernel)

without_editor_info theorem cell0_99 {x y : ℤ} (hx : (11:ℤ)^3∣x-510) (hy : (11:ℤ)^3∣y-73) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked99 i)

without_editor_info theorem cell1_99 {x y : ℤ} (hx : (11:ℤ)^3∣x-510) (hy : (11:ℤ)^3∣y-73) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked99 i)

without_editor_info theorem checked100 : ∀ i : Fin 5, (env16 i).check 11 3 (values 389 678 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 389 678)) (by decide +kernel)

without_editor_info theorem cell0_100 {x y : ℤ} (hx : (11:ℤ)^3∣x-389) (hy : (11:ℤ)^3∣y-678) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked100 i)

without_editor_info theorem cell1_100 {x y : ℤ} (hx : (11:ℤ)^3∣x-389) (hy : (11:ℤ)^3∣y-678) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked100 i)

without_editor_info theorem checked101 : ∀ i : Fin 5, (env16 i).check 11 3 (values 268 1283 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 268 1283)) (by decide +kernel)

without_editor_info theorem cell0_101 {x y : ℤ} (hx : (11:ℤ)^3∣x-268) (hy : (11:ℤ)^3∣y-1283) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked101 i)

without_editor_info theorem cell1_101 {x y : ℤ} (hx : (11:ℤ)^3∣x-268) (hy : (11:ℤ)^3∣y-1283) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked101 i)

without_editor_info theorem checked102 : ∀ i : Fin 5, (env16 i).check 11 3 (values 147 557 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 147 557)) (by decide +kernel)

without_editor_info theorem cell0_102 {x y : ℤ} (hx : (11:ℤ)^3∣x-147) (hy : (11:ℤ)^3∣y-557) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked102 i)

without_editor_info theorem cell1_102 {x y : ℤ} (hx : (11:ℤ)^3∣x-147) (hy : (11:ℤ)^3∣y-557) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked102 i)

without_editor_info theorem checked103 : ∀ i : Fin 5, (env16 i).check 11 3 (values 26 1162 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 26 1162)) (by decide +kernel)

without_editor_info theorem cell0_103 {x y : ℤ} (hx : (11:ℤ)^3∣x-26) (hy : (11:ℤ)^3∣y-1162) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked103 i)

without_editor_info theorem cell1_103 {x y : ℤ} (hx : (11:ℤ)^3∣x-26) (hy : (11:ℤ)^3∣y-1162) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked103 i)

without_editor_info theorem checked104 : ∀ i : Fin 5, (env5 i).check 11 3 (values 1225 854 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1225 854)) (by decide +kernel)

without_editor_info theorem cell0_104 {x y : ℤ} (hx : (11:ℤ)^3∣x-1225) (hy : (11:ℤ)^3∣y-854) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked104 i)

without_editor_info theorem cell1_104 {x y : ℤ} (hx : (11:ℤ)^3∣x-1225) (hy : (11:ℤ)^3∣y-854) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked104 i)

without_editor_info theorem checked105 : ∀ i : Fin 5, (env5 i).check 11 3 (values 1104 128 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1104 128)) (by decide +kernel)

without_editor_info theorem cell0_105 {x y : ℤ} (hx : (11:ℤ)^3∣x-1104) (hy : (11:ℤ)^3∣y-128) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked105 i)

without_editor_info theorem cell1_105 {x y : ℤ} (hx : (11:ℤ)^3∣x-1104) (hy : (11:ℤ)^3∣y-128) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked105 i)

without_editor_info theorem checked106 : ∀ i : Fin 5, (env5 i).check 11 3 (values 983 733 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 983 733)) (by decide +kernel)

without_editor_info theorem cell0_106 {x y : ℤ} (hx : (11:ℤ)^3∣x-983) (hy : (11:ℤ)^3∣y-733) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked106 i)

without_editor_info theorem cell1_106 {x y : ℤ} (hx : (11:ℤ)^3∣x-983) (hy : (11:ℤ)^3∣y-733) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked106 i)

without_editor_info theorem checked107 : ∀ i : Fin 5, (env5 i).check 11 3 (values 862 7 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 862 7)) (by decide +kernel)

without_editor_info theorem cell0_107 {x y : ℤ} (hx : (11:ℤ)^3∣x-862) (hy : (11:ℤ)^3∣y-7) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked107 i)

without_editor_info theorem cell1_107 {x y : ℤ} (hx : (11:ℤ)^3∣x-862) (hy : (11:ℤ)^3∣y-7) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked107 i)

without_editor_info theorem checked108 : ∀ i : Fin 5, (env5 i).check 11 3 (values 741 612 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 741 612)) (by decide +kernel)

without_editor_info theorem cell0_108 {x y : ℤ} (hx : (11:ℤ)^3∣x-741) (hy : (11:ℤ)^3∣y-612) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked108 i)

without_editor_info theorem cell1_108 {x y : ℤ} (hx : (11:ℤ)^3∣x-741) (hy : (11:ℤ)^3∣y-612) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked108 i)

without_editor_info theorem checked109 : ∀ i : Fin 5, (env5 i).check 11 3 (values 620 1217 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 620 1217)) (by decide +kernel)

without_editor_info theorem cell0_109 {x y : ℤ} (hx : (11:ℤ)^3∣x-620) (hy : (11:ℤ)^3∣y-1217) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked109 i)

without_editor_info theorem cell1_109 {x y : ℤ} (hx : (11:ℤ)^3∣x-620) (hy : (11:ℤ)^3∣y-1217) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked109 i)

without_editor_info theorem checked110 : ∀ i : Fin 5, (env5 i).check 11 3 (values 499 491 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 499 491)) (by decide +kernel)

without_editor_info theorem cell0_110 {x y : ℤ} (hx : (11:ℤ)^3∣x-499) (hy : (11:ℤ)^3∣y-491) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked110 i)

without_editor_info theorem cell1_110 {x y : ℤ} (hx : (11:ℤ)^3∣x-499) (hy : (11:ℤ)^3∣y-491) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked110 i)

without_editor_info theorem checked111 : ∀ i : Fin 5, (env5 i).check 11 3 (values 378 1096 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 378 1096)) (by decide +kernel)

without_editor_info theorem cell0_111 {x y : ℤ} (hx : (11:ℤ)^3∣x-378) (hy : (11:ℤ)^3∣y-1096) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked111 i)

without_editor_info theorem cell1_111 {x y : ℤ} (hx : (11:ℤ)^3∣x-378) (hy : (11:ℤ)^3∣y-1096) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked111 i)

without_editor_info theorem checked112 : ∀ i : Fin 5, (env5 i).check 11 3 (values 257 370 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 257 370)) (by decide +kernel)

without_editor_info theorem cell0_112 {x y : ℤ} (hx : (11:ℤ)^3∣x-257) (hy : (11:ℤ)^3∣y-370) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked112 i)

without_editor_info theorem cell1_112 {x y : ℤ} (hx : (11:ℤ)^3∣x-257) (hy : (11:ℤ)^3∣y-370) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked112 i)

without_editor_info theorem checked113 : ∀ i : Fin 5, (env5 i).check 11 3 (values 136 975 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 136 975)) (by decide +kernel)

without_editor_info theorem cell0_113 {x y : ℤ} (hx : (11:ℤ)^3∣x-136) (hy : (11:ℤ)^3∣y-975) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked113 i)

without_editor_info theorem cell1_113 {x y : ℤ} (hx : (11:ℤ)^3∣x-136) (hy : (11:ℤ)^3∣y-975) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked113 i)

without_editor_info theorem checked114 : ∀ i : Fin 5, (env5 i).check 11 3 (values 15 249 i) := by
  exact FiniteTable.zip_all envData5 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 15 249)) (by decide +kernel)

without_editor_info theorem cell0_114 {x y : ℤ} (hx : (11:ℤ)^3∣x-15) (hy : (11:ℤ)^3∣y-249) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env5 ?_ linear0_5 cross0_5,base0_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked114 i)

without_editor_info theorem cell1_114 {x y : ℤ} (hx : (11:ℤ)^3∣x-15) (hy : (11:ℤ)^3∣y-249) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env5 ?_ linear1_5 cross1_5,base1_5]
  intro i
  exact Envelope.check_sound (env5 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked114 i)

without_editor_info theorem checked115 : ∀ i : Fin 5, (env16 i).check 11 3 (values 1214 304 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1214 304)) (by decide +kernel)

without_editor_info theorem cell0_115 {x y : ℤ} (hx : (11:ℤ)^3∣x-1214) (hy : (11:ℤ)^3∣y-304) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked115 i)

without_editor_info theorem cell1_115 {x y : ℤ} (hx : (11:ℤ)^3∣x-1214) (hy : (11:ℤ)^3∣y-304) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked115 i)

without_editor_info theorem checked116 : ∀ i : Fin 5, (env16 i).check 11 3 (values 1093 909 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 1093 909)) (by decide +kernel)

without_editor_info theorem cell0_116 {x y : ℤ} (hx : (11:ℤ)^3∣x-1093) (hy : (11:ℤ)^3∣y-909) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked116 i)

without_editor_info theorem cell1_116 {x y : ℤ} (hx : (11:ℤ)^3∣x-1093) (hy : (11:ℤ)^3∣y-909) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked116 i)

without_editor_info theorem checked117 : ∀ i : Fin 5, (env16 i).check 11 3 (values 972 183 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 972 183)) (by decide +kernel)

without_editor_info theorem cell0_117 {x y : ℤ} (hx : (11:ℤ)^3∣x-972) (hy : (11:ℤ)^3∣y-183) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked117 i)

without_editor_info theorem cell1_117 {x y : ℤ} (hx : (11:ℤ)^3∣x-972) (hy : (11:ℤ)^3∣y-183) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked117 i)

without_editor_info theorem checked118 : ∀ i : Fin 5, (env16 i).check 11 3 (values 851 788 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 851 788)) (by decide +kernel)

without_editor_info theorem cell0_118 {x y : ℤ} (hx : (11:ℤ)^3∣x-851) (hy : (11:ℤ)^3∣y-788) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked118 i)

without_editor_info theorem cell1_118 {x y : ℤ} (hx : (11:ℤ)^3∣x-851) (hy : (11:ℤ)^3∣y-788) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked118 i)

without_editor_info theorem checked119 : ∀ i : Fin 5, (env16 i).check 11 3 (values 730 62 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 730 62)) (by decide +kernel)

without_editor_info theorem cell0_119 {x y : ℤ} (hx : (11:ℤ)^3∣x-730) (hy : (11:ℤ)^3∣y-62) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked119 i)

without_editor_info theorem cell1_119 {x y : ℤ} (hx : (11:ℤ)^3∣x-730) (hy : (11:ℤ)^3∣y-62) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked119 i)

without_editor_info theorem checked120 : ∀ i : Fin 5, (env16 i).check 11 3 (values 609 667 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 609 667)) (by decide +kernel)

without_editor_info theorem cell0_120 {x y : ℤ} (hx : (11:ℤ)^3∣x-609) (hy : (11:ℤ)^3∣y-667) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked120 i)

without_editor_info theorem cell1_120 {x y : ℤ} (hx : (11:ℤ)^3∣x-609) (hy : (11:ℤ)^3∣y-667) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked120 i)

without_editor_info theorem checked121 : ∀ i : Fin 5, (env16 i).check 11 3 (values 488 1272 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 488 1272)) (by decide +kernel)

without_editor_info theorem cell0_121 {x y : ℤ} (hx : (11:ℤ)^3∣x-488) (hy : (11:ℤ)^3∣y-1272) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked121 i)

without_editor_info theorem cell1_121 {x y : ℤ} (hx : (11:ℤ)^3∣x-488) (hy : (11:ℤ)^3∣y-1272) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked121 i)

without_editor_info theorem checked122 : ∀ i : Fin 5, (env16 i).check 11 3 (values 367 546 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 367 546)) (by decide +kernel)

without_editor_info theorem cell0_122 {x y : ℤ} (hx : (11:ℤ)^3∣x-367) (hy : (11:ℤ)^3∣y-546) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked122 i)

without_editor_info theorem cell1_122 {x y : ℤ} (hx : (11:ℤ)^3∣x-367) (hy : (11:ℤ)^3∣y-546) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked122 i)

without_editor_info theorem checked123 : ∀ i : Fin 5, (env16 i).check 11 3 (values 246 1151 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 246 1151)) (by decide +kernel)

without_editor_info theorem cell0_123 {x y : ℤ} (hx : (11:ℤ)^3∣x-246) (hy : (11:ℤ)^3∣y-1151) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked123 i)

without_editor_info theorem cell1_123 {x y : ℤ} (hx : (11:ℤ)^3∣x-246) (hy : (11:ℤ)^3∣y-1151) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked123 i)

without_editor_info theorem checked124 : ∀ i : Fin 5, (env16 i).check 11 3 (values 125 425 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 125 425)) (by decide +kernel)

without_editor_info theorem cell0_124 {x y : ℤ} (hx : (11:ℤ)^3∣x-125) (hy : (11:ℤ)^3∣y-425) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked124 i)

without_editor_info theorem cell1_124 {x y : ℤ} (hx : (11:ℤ)^3∣x-125) (hy : (11:ℤ)^3∣y-425) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked124 i)

without_editor_info theorem checked125 : ∀ i : Fin 5, (env16 i).check 11 3 (values 4 1030 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 3 (eval h 4 1030)) (by decide +kernel)

without_editor_info theorem cell0_125 {x y : ℤ} (hx : (11:ℤ)^3∣x-4) (hy : (11:ℤ)^3∣y-1030) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked125 i)

without_editor_info theorem cell1_125 {x y : ℤ} (hx : (11:ℤ)^3∣x-4) (hy : (11:ℤ)^3∣y-1030) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 3 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked125 i)

without_editor_info def envData126 : Array Envelope := #[⟨![0,0,0],![![1,0,0],![0,1,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![1,0,0],![0,1,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩]

without_editor_info def env126 (i : Fin 5) : Envelope := envData126[i.val]'i.isLt

without_editor_info theorem checked126 : ∀ i : Fin 5, (env126 i).check 11 1 (values 3 10 i) := by
  exact FiniteTable.zip_all envData126 polysData (by decide) (by decide)
    (fun e h => e.check 11 1 (eval h 3 10)) (by decide +kernel)

without_editor_info theorem linear0_126 : ∀ i : Fin 5, ∀ k : Fin 3, pairing 11 ((env126 i).directions k) (star 11 edges0 (fun i => (env126 i).base) (fun _ => 0) i)=0 := by
  have h : ∀ i : Fin 5, ∀ k : Fin 3, (env126 i).directions k=0 ∨ pairing 11 ((env126 i).directions k) (star 11 edges0 (fun i => (env126 i).base) (fun _ => 0) i)=0 := by
    simp only [star_sparse0]
    decide +kernel
  intro i k
  rcases h i k with hz | hz
  · rw [hz]; simp
  · exact hz

without_editor_info theorem cross0_126 : ∀ e : Fin 1, ∀ k l : Fin 3, pairing 11 ((env126 (edges0 e).1).directions k) ((env126 (edges0 e).2).directions l)=0 := by
  have h : ∀ e : Fin 1, (env126 (edges0 e).1).directions=0 ∨ (env126 (edges0 e).2).directions=0 ∨
      (∀ k l : Fin 3, pairing 11 ((env126 (edges0 e).1).directions k) ((env126 (edges0 e).2).directions l)=0) := by
    exact FiniteTable.table_all (m := 1) edgeList0 (by decide)
      (fun e => (env126 e.1).directions=0 ∨ (env126 e.2).directions=0 ∨
        (∀ k l : Fin 3, pairing 11 ((env126 e.1).directions k) ((env126 e.2).directions l)=0)) (by decide +kernel)
  intro e k l
  rcases h e with hz | hz | hz
  · rw [hz]; simp
  · rw [hz]; simp
  · exact hz k l

without_editor_info theorem base0_126 : graphForm 11 edges0 (fun i => (env126 i).base) (fun _ => 0)=0 := by
  unfold edges0
  rw [FiniteTable.graphForm_table]
  decide +kernel

without_editor_info theorem cell0_126 {x y : ℤ} (hx : (11:ℤ)^1∣x-3) (hy : (11:ℤ)^1∣y-10) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env126 ?_ linear0_126 cross0_126,base0_126]
  intro i
  exact Envelope.check_sound (env126 i) 11 1 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked126 i)

without_editor_info theorem linear1_126 : ∀ i : Fin 5, ∀ k : Fin 3, pairing 11 ((env126 i).directions k) (star 11 edges1 (fun i => (env126 i).base) (fun _ => 0) i)=0 := by
  have h : ∀ i : Fin 5, ∀ k : Fin 3, (env126 i).directions k=0 ∨ pairing 11 ((env126 i).directions k) (star 11 edges1 (fun i => (env126 i).base) (fun _ => 0) i)=0 := by
    simp only [star_sparse1]
    decide +kernel
  intro i k
  rcases h i k with hz | hz
  · rw [hz]; simp
  · exact hz

without_editor_info theorem cross1_126 : ∀ e : Fin 1, ∀ k l : Fin 3, pairing 11 ((env126 (edges1 e).1).directions k) ((env126 (edges1 e).2).directions l)=0 := by
  have h : ∀ e : Fin 1, (env126 (edges1 e).1).directions=0 ∨ (env126 (edges1 e).2).directions=0 ∨
      (∀ k l : Fin 3, pairing 11 ((env126 (edges1 e).1).directions k) ((env126 (edges1 e).2).directions l)=0) := by
    exact FiniteTable.table_all (m := 1) edgeList1 (by decide)
      (fun e => (env126 e.1).directions=0 ∨ (env126 e.2).directions=0 ∨
        (∀ k l : Fin 3, pairing 11 ((env126 e.1).directions k) ((env126 e.2).directions l)=0)) (by decide +kernel)
  intro e k l
  rcases h e with hz | hz | hz
  · rw [hz]; simp
  · rw [hz]; simp
  · exact hz k l

without_editor_info theorem base1_126 : graphForm 11 edges1 (fun i => (env126 i).base) (fun _ => 0)=0 := by
  unfold edges1
  rw [FiniteTable.graphForm_table]
  decide +kernel

without_editor_info theorem cell1_126 {x y : ℤ} (hx : (11:ℤ)^1∣x-3) (hy : (11:ℤ)^1∣y-10) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env126 ?_ linear1_126 cross1_126,base1_126]
  intro i
  exact Envelope.check_sound (env126 i) 11 1 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked126 i)

without_editor_info def envData127 : Array Envelope := #[⟨![0,1,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩,⟨![0,0,0],![![0,0,0],![0,0,0],![0,0,0]]⟩]

without_editor_info def env127 (i : Fin 5) : Envelope := envData127[i.val]'i.isLt

without_editor_info theorem checked127 : ∀ i : Fin 5, (env127 i).check 11 1 (values 3 6 i) := by
  exact FiniteTable.zip_all envData127 polysData (by decide) (by decide)
    (fun e h => e.check 11 1 (eval h 3 6)) (by decide +kernel)

without_editor_info theorem fixedDirections127 : ∀ i : Fin 5, (env127 i).directions=0 := by decide +kernel

without_editor_info theorem linear0_127 : ∀ i : Fin 5, ∀ k : Fin 3, pairing 11 ((env127 i).directions k) (star 11 edges0 (fun i => (env127 i).base) (fun _ => 0) i)=0 := by
  intro i k; rw [fixedDirections127]; simp

without_editor_info theorem cross0_127 : ∀ e : Fin 1, ∀ k l : Fin 3, pairing 11 ((env127 (edges0 e).1).directions k) ((env127 (edges0 e).2).directions l)=0 := by
  intro e k l; rw [fixedDirections127]; simp

without_editor_info theorem base0_127 : graphForm 11 edges0 (fun i => (env127 i).base) (fun _ => 0)=0 := by
  unfold edges0
  rw [FiniteTable.graphForm_table]
  decide +kernel

without_editor_info theorem cell0_127 {x y : ℤ} (hx : (11:ℤ)^1∣x-3) (hy : (11:ℤ)^1∣y-6) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env127 ?_ linear0_127 cross0_127,base0_127]
  intro i
  exact Envelope.check_sound (env127 i) 11 1 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked127 i)

without_editor_info theorem linear1_127 : ∀ i : Fin 5, ∀ k : Fin 3, pairing 11 ((env127 i).directions k) (star 11 edges1 (fun i => (env127 i).base) (fun _ => 0) i)=0 := by
  intro i k; rw [fixedDirections127]; simp

without_editor_info theorem cross1_127 : ∀ e : Fin 1, ∀ k l : Fin 3, pairing 11 ((env127 (edges1 e).1).directions k) ((env127 (edges1 e).2).directions l)=0 := by
  intro e k l; rw [fixedDirections127]; simp

without_editor_info theorem base1_127 : graphForm 11 edges1 (fun i => (env127 i).base) (fun _ => 0)=0 := by
  unfold edges1
  rw [FiniteTable.graphForm_table]
  decide +kernel

without_editor_info theorem cell1_127 {x y : ℤ} (hx : (11:ℤ)^1∣x-3) (hy : (11:ℤ)^1∣y-6) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env127 ?_ linear1_127 cross1_127,base1_127]
  intro i
  exact Envelope.check_sound (env127 i) 11 1 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked127 i)

without_editor_info theorem checked128 : ∀ i : Fin 5, (env4 i).check 11 1 (values 0 8 i) := by
  exact FiniteTable.zip_all envData4 polysData (by decide) (by decide)
    (fun e h => e.check 11 1 (eval h 0 8)) (by decide +kernel)

without_editor_info theorem cell0_128 {x y : ℤ} (hx : (11:ℤ)^1∣x-0) (hy : (11:ℤ)^1∣y-8) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env4 ?_ linear0_4 cross0_4,base0_4]
  intro i
  exact Envelope.check_sound (env4 i) 11 1 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked128 i)

without_editor_info theorem cell1_128 {x y : ℤ} (hx : (11:ℤ)^1∣x-0) (hy : (11:ℤ)^1∣y-8) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env4 ?_ linear1_4 cross1_4,base1_4]
  intro i
  exact Envelope.check_sound (env4 i) 11 1 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked128 i)

without_editor_info theorem checked129 : ∀ i : Fin 5, (env16 i).check 11 1 (values 0 6 i) := by
  exact FiniteTable.zip_all envData16 polysData (by decide) (by decide)
    (fun e h => e.check 11 1 (eval h 0 6)) (by decide +kernel)

without_editor_info theorem cell0_129 {x y : ℤ} (hx : (11:ℤ)^1∣x-0) (hy : (11:ℤ)^1∣y-6) : localSum0 x y=0 := by
  rw [localSum0,graphForm_envelopes 11 edges0 _ (fun _ => 0) env16 ?_ linear0_16 cross0_16,base0_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 1 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked129 i)

without_editor_info theorem cell1_129 {x y : ℤ} (hx : (11:ℤ)^1∣x-0) (hy : (11:ℤ)^1∣y-6) : localSum1 x y=0 := by
  rw [localSum1,graphForm_envelopes 11 edges1 _ (fun _ => 0) env16 ?_ linear1_16 cross1_16,base1_16]
  intro i
  exact Envelope.check_sound (env16 i) 11 1 (GraphCert.RationalClasses.eval_congr (polys i) hx hy) (checked129 i)

structure ProofCell where
  point : ℤ × ℤ × ℕ
  checked0 : ∀ {x y : ℤ},
    (11:ℤ)^point.2.2∣x-point.1 →
    (11:ℤ)^point.2.2∣y-point.2.1 → localSum0 x y=0
  checked1 : ∀ {x y : ℤ},
    (11:ℤ)^point.2.2∣x-point.1 →
    (11:ℤ)^point.2.2∣y-point.2.1 → localSum1 x y=0

without_editor_info def proofCell0 : ProofCell := {point := (10,5,1), checked0 := @cell0_0, checked1 := @cell1_0}

without_editor_info def proofCell1 : ProofCell := {point := (9,8,1), checked0 := @cell0_1, checked1 := @cell1_1}

without_editor_info def proofCell2 : ProofCell := {point := (7,4,1), checked0 := @cell0_2, checked1 := @cell1_2}

without_editor_info def proofCell3 : ProofCell := {point := (6,0,1), checked0 := @cell0_3, checked1 := @cell1_3}

without_editor_info def proofCell4 : ProofCell := {point := (5,0,1), checked0 := @cell0_4, checked1 := @cell1_4}

without_editor_info def proofCell5 : ProofCell := {point := (1324,843,3), checked0 := @cell0_5, checked1 := @cell1_5}

without_editor_info def proofCell6 : ProofCell := {point := (1203,117,3), checked0 := @cell0_6, checked1 := @cell1_6}

without_editor_info def proofCell7 : ProofCell := {point := (1082,722,3), checked0 := @cell0_7, checked1 := @cell1_7}

without_editor_info def proofCell8 : ProofCell := {point := (961,1327,3), checked0 := @cell0_8, checked1 := @cell1_8}

without_editor_info def proofCell9 : ProofCell := {point := (840,601,3), checked0 := @cell0_9, checked1 := @cell1_9}

without_editor_info def proofCell10 : ProofCell := {point := (719,1206,3), checked0 := @cell0_10, checked1 := @cell1_10}

without_editor_info def proofCell11 : ProofCell := {point := (598,480,3), checked0 := @cell0_11, checked1 := @cell1_11}

without_editor_info def proofCell12 : ProofCell := {point := (477,1085,3), checked0 := @cell0_12, checked1 := @cell1_12}

without_editor_info def proofCell13 : ProofCell := {point := (356,359,3), checked0 := @cell0_13, checked1 := @cell1_13}

without_editor_info def proofCell14 : ProofCell := {point := (235,964,3), checked0 := @cell0_14, checked1 := @cell1_14}

without_editor_info def proofCell15 : ProofCell := {point := (114,238,3), checked0 := @cell0_15, checked1 := @cell1_15}

without_editor_info def proofCell16 : ProofCell := {point := (1313,1019,3), checked0 := @cell0_16, checked1 := @cell1_16}

without_editor_info def proofCell17 : ProofCell := {point := (1192,293,3), checked0 := @cell0_17, checked1 := @cell1_17}

without_editor_info def proofCell18 : ProofCell := {point := (1071,898,3), checked0 := @cell0_18, checked1 := @cell1_18}

without_editor_info def proofCell19 : ProofCell := {point := (950,172,3), checked0 := @cell0_19, checked1 := @cell1_19}

without_editor_info def proofCell20 : ProofCell := {point := (829,777,3), checked0 := @cell0_20, checked1 := @cell1_20}

without_editor_info def proofCell21 : ProofCell := {point := (708,51,3), checked0 := @cell0_21, checked1 := @cell1_21}

without_editor_info def proofCell22 : ProofCell := {point := (587,656,3), checked0 := @cell0_22, checked1 := @cell1_22}

without_editor_info def proofCell23 : ProofCell := {point := (466,1261,3), checked0 := @cell0_23, checked1 := @cell1_23}

without_editor_info def proofCell24 : ProofCell := {point := (345,535,3), checked0 := @cell0_24, checked1 := @cell1_24}

without_editor_info def proofCell25 : ProofCell := {point := (224,1140,3), checked0 := @cell0_25, checked1 := @cell1_25}

without_editor_info def proofCell26 : ProofCell := {point := (103,414,3), checked0 := @cell0_26, checked1 := @cell1_26}

without_editor_info def proofCell27 : ProofCell := {point := (1302,227,3), checked0 := @cell0_27, checked1 := @cell1_27}

without_editor_info def proofCell28 : ProofCell := {point := (1181,832,3), checked0 := @cell0_28, checked1 := @cell1_28}

without_editor_info def proofCell29 : ProofCell := {point := (1060,106,3), checked0 := @cell0_29, checked1 := @cell1_29}

without_editor_info def proofCell30 : ProofCell := {point := (939,711,3), checked0 := @cell0_30, checked1 := @cell1_30}

without_editor_info def proofCell31 : ProofCell := {point := (818,1316,3), checked0 := @cell0_31, checked1 := @cell1_31}

without_editor_info def proofCell32 : ProofCell := {point := (697,590,3), checked0 := @cell0_32, checked1 := @cell1_32}

without_editor_info def proofCell33 : ProofCell := {point := (576,1195,3), checked0 := @cell0_33, checked1 := @cell1_33}

without_editor_info def proofCell34 : ProofCell := {point := (455,469,3), checked0 := @cell0_34, checked1 := @cell1_34}

without_editor_info def proofCell35 : ProofCell := {point := (334,1074,3), checked0 := @cell0_35, checked1 := @cell1_35}

without_editor_info def proofCell36 : ProofCell := {point := (213,348,3), checked0 := @cell0_36, checked1 := @cell1_36}

without_editor_info def proofCell37 : ProofCell := {point := (92,953,3), checked0 := @cell0_37, checked1 := @cell1_37}

without_editor_info def proofCell38 : ProofCell := {point := (1291,1129,3), checked0 := @cell0_38, checked1 := @cell1_38}

without_editor_info def proofCell39 : ProofCell := {point := (1170,403,3), checked0 := @cell0_39, checked1 := @cell1_39}

without_editor_info def proofCell40 : ProofCell := {point := (1049,1008,3), checked0 := @cell0_40, checked1 := @cell1_40}

without_editor_info def proofCell41 : ProofCell := {point := (928,282,3), checked0 := @cell0_41, checked1 := @cell1_41}

without_editor_info def proofCell42 : ProofCell := {point := (807,887,3), checked0 := @cell0_42, checked1 := @cell1_42}

without_editor_info def proofCell43 : ProofCell := {point := (686,161,3), checked0 := @cell0_43, checked1 := @cell1_43}

without_editor_info def proofCell44 : ProofCell := {point := (565,766,3), checked0 := @cell0_44, checked1 := @cell1_44}

without_editor_info def proofCell45 : ProofCell := {point := (444,40,3), checked0 := @cell0_45, checked1 := @cell1_45}

without_editor_info def proofCell46 : ProofCell := {point := (323,645,3), checked0 := @cell0_46, checked1 := @cell1_46}

without_editor_info def proofCell47 : ProofCell := {point := (202,1250,3), checked0 := @cell0_47, checked1 := @cell1_47}

without_editor_info def proofCell48 : ProofCell := {point := (81,524,3), checked0 := @cell0_48, checked1 := @cell1_48}

without_editor_info def proofCell49 : ProofCell := {point := (1280,1063,3), checked0 := @cell0_49, checked1 := @cell1_49}

without_editor_info def proofCell50 : ProofCell := {point := (1159,337,3), checked0 := @cell0_50, checked1 := @cell1_50}

without_editor_info def proofCell51 : ProofCell := {point := (1038,942,3), checked0 := @cell0_51, checked1 := @cell1_51}

without_editor_info def proofCell52 : ProofCell := {point := (917,216,3), checked0 := @cell0_52, checked1 := @cell1_52}

without_editor_info def proofCell53 : ProofCell := {point := (796,821,3), checked0 := @cell0_53, checked1 := @cell1_53}

without_editor_info def proofCell54 : ProofCell := {point := (675,95,3), checked0 := @cell0_54, checked1 := @cell1_54}

without_editor_info def proofCell55 : ProofCell := {point := (554,700,3), checked0 := @cell0_55, checked1 := @cell1_55}

without_editor_info def proofCell56 : ProofCell := {point := (433,1305,3), checked0 := @cell0_56, checked1 := @cell1_56}

without_editor_info def proofCell57 : ProofCell := {point := (312,579,3), checked0 := @cell0_57, checked1 := @cell1_57}

without_editor_info def proofCell58 : ProofCell := {point := (191,1184,3), checked0 := @cell0_58, checked1 := @cell1_58}

without_editor_info def proofCell59 : ProofCell := {point := (70,458,3), checked0 := @cell0_59, checked1 := @cell1_59}

without_editor_info def proofCell60 : ProofCell := {point := (1269,29,3), checked0 := @cell0_60, checked1 := @cell1_60}

without_editor_info def proofCell61 : ProofCell := {point := (1148,634,3), checked0 := @cell0_61, checked1 := @cell1_61}

without_editor_info def proofCell62 : ProofCell := {point := (1027,1239,3), checked0 := @cell0_62, checked1 := @cell1_62}

without_editor_info def proofCell63 : ProofCell := {point := (906,513,3), checked0 := @cell0_63, checked1 := @cell1_63}

without_editor_info def proofCell64 : ProofCell := {point := (785,1118,3), checked0 := @cell0_64, checked1 := @cell1_64}

without_editor_info def proofCell65 : ProofCell := {point := (664,392,3), checked0 := @cell0_65, checked1 := @cell1_65}

without_editor_info def proofCell66 : ProofCell := {point := (543,997,3), checked0 := @cell0_66, checked1 := @cell1_66}

without_editor_info def proofCell67 : ProofCell := {point := (422,271,3), checked0 := @cell0_67, checked1 := @cell1_67}

without_editor_info def proofCell68 : ProofCell := {point := (301,876,3), checked0 := @cell0_68, checked1 := @cell1_68}

without_editor_info def proofCell69 : ProofCell := {point := (180,150,3), checked0 := @cell0_69, checked1 := @cell1_69}

without_editor_info def proofCell70 : ProofCell := {point := (59,755,3), checked0 := @cell0_70, checked1 := @cell1_70}

without_editor_info def proofCell71 : ProofCell := {point := (1258,689,3), checked0 := @cell0_71, checked1 := @cell1_71}

without_editor_info def proofCell72 : ProofCell := {point := (1137,1294,3), checked0 := @cell0_72, checked1 := @cell1_72}

without_editor_info def proofCell73 : ProofCell := {point := (1016,568,3), checked0 := @cell0_73, checked1 := @cell1_73}

without_editor_info def proofCell74 : ProofCell := {point := (895,1173,3), checked0 := @cell0_74, checked1 := @cell1_74}

without_editor_info def proofCell75 : ProofCell := {point := (774,447,3), checked0 := @cell0_75, checked1 := @cell1_75}

without_editor_info def proofCell76 : ProofCell := {point := (653,1052,3), checked0 := @cell0_76, checked1 := @cell1_76}

without_editor_info def proofCell77 : ProofCell := {point := (532,326,3), checked0 := @cell0_77, checked1 := @cell1_77}

without_editor_info def proofCell78 : ProofCell := {point := (411,931,3), checked0 := @cell0_78, checked1 := @cell1_78}

without_editor_info def proofCell79 : ProofCell := {point := (290,205,3), checked0 := @cell0_79, checked1 := @cell1_79}

without_editor_info def proofCell80 : ProofCell := {point := (169,810,3), checked0 := @cell0_80, checked1 := @cell1_80}

without_editor_info def proofCell81 : ProofCell := {point := (48,84,3), checked0 := @cell0_81, checked1 := @cell1_81}

without_editor_info def proofCell82 : ProofCell := {point := (1247,381,3), checked0 := @cell0_82, checked1 := @cell1_82}

without_editor_info def proofCell83 : ProofCell := {point := (1126,986,3), checked0 := @cell0_83, checked1 := @cell1_83}

without_editor_info def proofCell84 : ProofCell := {point := (1005,260,3), checked0 := @cell0_84, checked1 := @cell1_84}

without_editor_info def proofCell85 : ProofCell := {point := (884,865,3), checked0 := @cell0_85, checked1 := @cell1_85}

without_editor_info def proofCell86 : ProofCell := {point := (763,139,3), checked0 := @cell0_86, checked1 := @cell1_86}

without_editor_info def proofCell87 : ProofCell := {point := (642,744,3), checked0 := @cell0_87, checked1 := @cell1_87}

without_editor_info def proofCell88 : ProofCell := {point := (521,18,3), checked0 := @cell0_88, checked1 := @cell1_88}

without_editor_info def proofCell89 : ProofCell := {point := (400,623,3), checked0 := @cell0_89, checked1 := @cell1_89}

without_editor_info def proofCell90 : ProofCell := {point := (279,1228,3), checked0 := @cell0_90, checked1 := @cell1_90}

without_editor_info def proofCell91 : ProofCell := {point := (158,502,3), checked0 := @cell0_91, checked1 := @cell1_91}

without_editor_info def proofCell92 : ProofCell := {point := (37,1107,3), checked0 := @cell0_92, checked1 := @cell1_92}

without_editor_info def proofCell93 : ProofCell := {point := (1236,436,3), checked0 := @cell0_93, checked1 := @cell1_93}

without_editor_info def proofCell94 : ProofCell := {point := (1115,1041,3), checked0 := @cell0_94, checked1 := @cell1_94}

without_editor_info def proofCell95 : ProofCell := {point := (994,315,3), checked0 := @cell0_95, checked1 := @cell1_95}

without_editor_info def proofCell96 : ProofCell := {point := (873,920,3), checked0 := @cell0_96, checked1 := @cell1_96}

without_editor_info def proofCell97 : ProofCell := {point := (752,194,3), checked0 := @cell0_97, checked1 := @cell1_97}

without_editor_info def proofCell98 : ProofCell := {point := (631,799,3), checked0 := @cell0_98, checked1 := @cell1_98}

without_editor_info def proofCell99 : ProofCell := {point := (510,73,3), checked0 := @cell0_99, checked1 := @cell1_99}

without_editor_info def proofCell100 : ProofCell := {point := (389,678,3), checked0 := @cell0_100, checked1 := @cell1_100}

without_editor_info def proofCell101 : ProofCell := {point := (268,1283,3), checked0 := @cell0_101, checked1 := @cell1_101}

without_editor_info def proofCell102 : ProofCell := {point := (147,557,3), checked0 := @cell0_102, checked1 := @cell1_102}

without_editor_info def proofCell103 : ProofCell := {point := (26,1162,3), checked0 := @cell0_103, checked1 := @cell1_103}

without_editor_info def proofCell104 : ProofCell := {point := (1225,854,3), checked0 := @cell0_104, checked1 := @cell1_104}

without_editor_info def proofCell105 : ProofCell := {point := (1104,128,3), checked0 := @cell0_105, checked1 := @cell1_105}

without_editor_info def proofCell106 : ProofCell := {point := (983,733,3), checked0 := @cell0_106, checked1 := @cell1_106}

without_editor_info def proofCell107 : ProofCell := {point := (862,7,3), checked0 := @cell0_107, checked1 := @cell1_107}

without_editor_info def proofCell108 : ProofCell := {point := (741,612,3), checked0 := @cell0_108, checked1 := @cell1_108}

without_editor_info def proofCell109 : ProofCell := {point := (620,1217,3), checked0 := @cell0_109, checked1 := @cell1_109}

without_editor_info def proofCell110 : ProofCell := {point := (499,491,3), checked0 := @cell0_110, checked1 := @cell1_110}

without_editor_info def proofCell111 : ProofCell := {point := (378,1096,3), checked0 := @cell0_111, checked1 := @cell1_111}

without_editor_info def proofCell112 : ProofCell := {point := (257,370,3), checked0 := @cell0_112, checked1 := @cell1_112}

without_editor_info def proofCell113 : ProofCell := {point := (136,975,3), checked0 := @cell0_113, checked1 := @cell1_113}

without_editor_info def proofCell114 : ProofCell := {point := (15,249,3), checked0 := @cell0_114, checked1 := @cell1_114}

without_editor_info def proofCell115 : ProofCell := {point := (1214,304,3), checked0 := @cell0_115, checked1 := @cell1_115}

without_editor_info def proofCell116 : ProofCell := {point := (1093,909,3), checked0 := @cell0_116, checked1 := @cell1_116}

without_editor_info def proofCell117 : ProofCell := {point := (972,183,3), checked0 := @cell0_117, checked1 := @cell1_117}

without_editor_info def proofCell118 : ProofCell := {point := (851,788,3), checked0 := @cell0_118, checked1 := @cell1_118}

without_editor_info def proofCell119 : ProofCell := {point := (730,62,3), checked0 := @cell0_119, checked1 := @cell1_119}

without_editor_info def proofCell120 : ProofCell := {point := (609,667,3), checked0 := @cell0_120, checked1 := @cell1_120}

without_editor_info def proofCell121 : ProofCell := {point := (488,1272,3), checked0 := @cell0_121, checked1 := @cell1_121}

without_editor_info def proofCell122 : ProofCell := {point := (367,546,3), checked0 := @cell0_122, checked1 := @cell1_122}

without_editor_info def proofCell123 : ProofCell := {point := (246,1151,3), checked0 := @cell0_123, checked1 := @cell1_123}

without_editor_info def proofCell124 : ProofCell := {point := (125,425,3), checked0 := @cell0_124, checked1 := @cell1_124}

without_editor_info def proofCell125 : ProofCell := {point := (4,1030,3), checked0 := @cell0_125, checked1 := @cell1_125}

without_editor_info def proofCell126 : ProofCell := {point := (3,10,1), checked0 := @cell0_126, checked1 := @cell1_126}

without_editor_info def proofCell127 : ProofCell := {point := (3,6,1), checked0 := @cell0_127, checked1 := @cell1_127}

without_editor_info def proofCell128 : ProofCell := {point := (0,8,1), checked0 := @cell0_128, checked1 := @cell1_128}

without_editor_info def proofCell129 : ProofCell := {point := (0,6,1), checked0 := @cell0_129, checked1 := @cell1_129}

without_editor_info def proofCells : Fin 130 → ProofCell := (fun i => (#[proofCell0,proofCell1,proofCell2,proofCell3,proofCell4,proofCell5,proofCell6,proofCell7,proofCell8,proofCell9,proofCell10,proofCell11,proofCell12,proofCell13,proofCell14,proofCell15,proofCell16,proofCell17,proofCell18,proofCell19,proofCell20,proofCell21,proofCell22,proofCell23,proofCell24,proofCell25,proofCell26,proofCell27,proofCell28,proofCell29,proofCell30,proofCell31,proofCell32,proofCell33,proofCell34,proofCell35,proofCell36,proofCell37,proofCell38,proofCell39,proofCell40,proofCell41,proofCell42,proofCell43,proofCell44,proofCell45,proofCell46,proofCell47,proofCell48,proofCell49,proofCell50,proofCell51,proofCell52,proofCell53,proofCell54,proofCell55,proofCell56,proofCell57,proofCell58,proofCell59,proofCell60,proofCell61,proofCell62,proofCell63,proofCell64,proofCell65,proofCell66,proofCell67,proofCell68,proofCell69,proofCell70,proofCell71,proofCell72,proofCell73,proofCell74,proofCell75,proofCell76,proofCell77,proofCell78,proofCell79,proofCell80,proofCell81,proofCell82,proofCell83,proofCell84,proofCell85,proofCell86,proofCell87,proofCell88,proofCell89,proofCell90,proofCell91,proofCell92,proofCell93,proofCell94,proofCell95,proofCell96,proofCell97,proofCell98,proofCell99,proofCell100,proofCell101,proofCell102,proofCell103,proofCell104,proofCell105,proofCell106,proofCell107,proofCell108,proofCell109,proofCell110,proofCell111,proofCell112,proofCell113,proofCell114,proofCell115,proofCell116,proofCell117,proofCell118,proofCell119,proofCell120,proofCell121,proofCell122,proofCell123,proofCell124,proofCell125,proofCell126,proofCell127,proofCell128,proofCell129] : Array ProofCell)[i.val]'i.isLt)

without_editor_info def residues (i : Fin 130) : ℤ × ℤ × ℕ := (proofCells i).point

without_editor_info def targets0 (i : Fin 130) : ZMod 2 := 0

without_editor_info theorem cell_value0 (i : Fin 130) {x y : ℤ}
    (hx : (11:ℤ)^(residues i).2.2∣x-(residues i).1)
    (hy : (11:ℤ)^(residues i).2.2∣y-(residues i).2.1) : localSum0 x y=targets0 i :=
  (proofCells i).checked0 hx hy

without_editor_info def targets1 (i : Fin 130) : ZMod 2 := 0

without_editor_info theorem cell_value1 (i : Fin 130) {x y : ℤ}
    (hx : (11:ℤ)^(residues i).2.2∣x-(residues i).1)
    (hy : (11:ℤ)^(residues i).2.2∣y-(residues i).2.1) : localSum1 x y=targets1 i :=
  (proofCells i).checked1 hx hy

without_editor_info theorem covered0 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^1∣x-10) (hy : (11:ℤ)^1∣y-5) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨0,hx,hy⟩

without_editor_info theorem covered1 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^1∣x-9) (hy : (11:ℤ)^1∣y-8) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨1,hx,hy⟩

without_editor_info theorem covered2 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^1∣x-7) (hy : (11:ℤ)^1∣y-4) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨2,hx,hy⟩

without_editor_info theorem covered3 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^1∣x-6) (hy : (11:ℤ)^1∣y-0) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨3,hx,hy⟩

without_editor_info theorem covered4 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^1∣x-5) (hy : (11:ℤ)^1∣y-0) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨4,hx,hy⟩

without_editor_info theorem covered5 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1324) (hy : (11:ℤ)^3∣y-843) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨5,hx,hy⟩

without_editor_info theorem covered6 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1203) (hy : (11:ℤ)^3∣y-117) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨6,hx,hy⟩

without_editor_info theorem covered7 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1082) (hy : (11:ℤ)^3∣y-722) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨7,hx,hy⟩

without_editor_info theorem covered8 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-961) (hy : (11:ℤ)^3∣y-1327) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨8,hx,hy⟩

without_editor_info theorem covered9 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-840) (hy : (11:ℤ)^3∣y-601) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨9,hx,hy⟩

without_editor_info theorem covered10 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-719) (hy : (11:ℤ)^3∣y-1206) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨10,hx,hy⟩

without_editor_info theorem covered11 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-598) (hy : (11:ℤ)^3∣y-480) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨11,hx,hy⟩

without_editor_info theorem covered12 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-477) (hy : (11:ℤ)^3∣y-1085) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨12,hx,hy⟩

without_editor_info theorem covered13 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-356) (hy : (11:ℤ)^3∣y-359) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨13,hx,hy⟩

without_editor_info theorem covered14 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-235) (hy : (11:ℤ)^3∣y-964) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨14,hx,hy⟩

without_editor_info theorem covered15 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-114) (hy : (11:ℤ)^3∣y-238) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨15,hx,hy⟩

without_editor_info theorem covered16 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1313) (hy : (11:ℤ)^3∣y-1019) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨16,hx,hy⟩

without_editor_info theorem covered17 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1192) (hy : (11:ℤ)^3∣y-293) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨17,hx,hy⟩

without_editor_info theorem covered18 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1071) (hy : (11:ℤ)^3∣y-898) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨18,hx,hy⟩

without_editor_info theorem covered19 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-950) (hy : (11:ℤ)^3∣y-172) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨19,hx,hy⟩

without_editor_info theorem covered20 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-829) (hy : (11:ℤ)^3∣y-777) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨20,hx,hy⟩

without_editor_info theorem covered21 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-708) (hy : (11:ℤ)^3∣y-51) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨21,hx,hy⟩

without_editor_info theorem covered22 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-587) (hy : (11:ℤ)^3∣y-656) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨22,hx,hy⟩

without_editor_info theorem covered23 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-466) (hy : (11:ℤ)^3∣y-1261) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨23,hx,hy⟩

without_editor_info theorem covered24 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-345) (hy : (11:ℤ)^3∣y-535) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨24,hx,hy⟩

without_editor_info theorem covered25 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-224) (hy : (11:ℤ)^3∣y-1140) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨25,hx,hy⟩

without_editor_info theorem covered26 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-103) (hy : (11:ℤ)^3∣y-414) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨26,hx,hy⟩

without_editor_info theorem covered27 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1302) (hy : (11:ℤ)^3∣y-227) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨27,hx,hy⟩

without_editor_info theorem covered28 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1181) (hy : (11:ℤ)^3∣y-832) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨28,hx,hy⟩

without_editor_info theorem covered29 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1060) (hy : (11:ℤ)^3∣y-106) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨29,hx,hy⟩

without_editor_info theorem covered30 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-939) (hy : (11:ℤ)^3∣y-711) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨30,hx,hy⟩

without_editor_info theorem covered31 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-818) (hy : (11:ℤ)^3∣y-1316) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨31,hx,hy⟩

without_editor_info theorem covered32 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-697) (hy : (11:ℤ)^3∣y-590) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨32,hx,hy⟩

without_editor_info theorem covered33 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-576) (hy : (11:ℤ)^3∣y-1195) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨33,hx,hy⟩

without_editor_info theorem covered34 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-455) (hy : (11:ℤ)^3∣y-469) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨34,hx,hy⟩

without_editor_info theorem covered35 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-334) (hy : (11:ℤ)^3∣y-1074) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨35,hx,hy⟩

without_editor_info theorem covered36 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-213) (hy : (11:ℤ)^3∣y-348) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨36,hx,hy⟩

without_editor_info theorem covered37 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-92) (hy : (11:ℤ)^3∣y-953) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨37,hx,hy⟩

without_editor_info theorem covered38 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1291) (hy : (11:ℤ)^3∣y-1129) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨38,hx,hy⟩

without_editor_info theorem covered39 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1170) (hy : (11:ℤ)^3∣y-403) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨39,hx,hy⟩

without_editor_info theorem covered40 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1049) (hy : (11:ℤ)^3∣y-1008) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨40,hx,hy⟩

without_editor_info theorem covered41 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-928) (hy : (11:ℤ)^3∣y-282) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨41,hx,hy⟩

without_editor_info theorem covered42 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-807) (hy : (11:ℤ)^3∣y-887) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨42,hx,hy⟩

without_editor_info theorem covered43 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-686) (hy : (11:ℤ)^3∣y-161) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨43,hx,hy⟩

without_editor_info theorem covered44 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-565) (hy : (11:ℤ)^3∣y-766) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨44,hx,hy⟩

without_editor_info theorem covered45 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-444) (hy : (11:ℤ)^3∣y-40) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨45,hx,hy⟩

without_editor_info theorem covered46 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-323) (hy : (11:ℤ)^3∣y-645) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨46,hx,hy⟩

without_editor_info theorem covered47 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-202) (hy : (11:ℤ)^3∣y-1250) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨47,hx,hy⟩

without_editor_info theorem covered48 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-81) (hy : (11:ℤ)^3∣y-524) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨48,hx,hy⟩

without_editor_info theorem covered49 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1280) (hy : (11:ℤ)^3∣y-1063) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨49,hx,hy⟩

without_editor_info theorem covered50 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1159) (hy : (11:ℤ)^3∣y-337) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨50,hx,hy⟩

without_editor_info theorem covered51 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1038) (hy : (11:ℤ)^3∣y-942) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨51,hx,hy⟩

without_editor_info theorem covered52 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-917) (hy : (11:ℤ)^3∣y-216) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨52,hx,hy⟩

without_editor_info theorem covered53 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-796) (hy : (11:ℤ)^3∣y-821) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨53,hx,hy⟩

without_editor_info theorem covered54 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-675) (hy : (11:ℤ)^3∣y-95) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨54,hx,hy⟩

without_editor_info theorem covered55 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-554) (hy : (11:ℤ)^3∣y-700) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨55,hx,hy⟩

without_editor_info theorem covered56 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-433) (hy : (11:ℤ)^3∣y-1305) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨56,hx,hy⟩

without_editor_info theorem covered57 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-312) (hy : (11:ℤ)^3∣y-579) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨57,hx,hy⟩

without_editor_info theorem covered58 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-191) (hy : (11:ℤ)^3∣y-1184) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨58,hx,hy⟩

without_editor_info theorem covered59 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-70) (hy : (11:ℤ)^3∣y-458) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨59,hx,hy⟩

without_editor_info theorem covered60 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1269) (hy : (11:ℤ)^3∣y-29) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨60,hx,hy⟩

without_editor_info theorem covered61 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1148) (hy : (11:ℤ)^3∣y-634) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨61,hx,hy⟩

without_editor_info theorem covered62 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1027) (hy : (11:ℤ)^3∣y-1239) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨62,hx,hy⟩

without_editor_info theorem covered63 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-906) (hy : (11:ℤ)^3∣y-513) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨63,hx,hy⟩

without_editor_info theorem covered64 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-785) (hy : (11:ℤ)^3∣y-1118) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨64,hx,hy⟩

without_editor_info theorem covered65 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-664) (hy : (11:ℤ)^3∣y-392) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨65,hx,hy⟩

without_editor_info theorem covered66 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-543) (hy : (11:ℤ)^3∣y-997) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨66,hx,hy⟩

without_editor_info theorem covered67 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-422) (hy : (11:ℤ)^3∣y-271) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨67,hx,hy⟩

without_editor_info theorem covered68 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-301) (hy : (11:ℤ)^3∣y-876) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨68,hx,hy⟩

without_editor_info theorem covered69 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-180) (hy : (11:ℤ)^3∣y-150) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨69,hx,hy⟩

without_editor_info theorem covered70 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-59) (hy : (11:ℤ)^3∣y-755) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨70,hx,hy⟩

without_editor_info theorem covered71 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1258) (hy : (11:ℤ)^3∣y-689) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨71,hx,hy⟩

without_editor_info theorem covered72 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1137) (hy : (11:ℤ)^3∣y-1294) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨72,hx,hy⟩

without_editor_info theorem covered73 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1016) (hy : (11:ℤ)^3∣y-568) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨73,hx,hy⟩

without_editor_info theorem covered74 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-895) (hy : (11:ℤ)^3∣y-1173) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨74,hx,hy⟩

without_editor_info theorem covered75 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-774) (hy : (11:ℤ)^3∣y-447) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨75,hx,hy⟩

without_editor_info theorem covered76 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-653) (hy : (11:ℤ)^3∣y-1052) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨76,hx,hy⟩

without_editor_info theorem covered77 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-532) (hy : (11:ℤ)^3∣y-326) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨77,hx,hy⟩

without_editor_info theorem covered78 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-411) (hy : (11:ℤ)^3∣y-931) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨78,hx,hy⟩

without_editor_info theorem covered79 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-290) (hy : (11:ℤ)^3∣y-205) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨79,hx,hy⟩

without_editor_info theorem covered80 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-169) (hy : (11:ℤ)^3∣y-810) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨80,hx,hy⟩

without_editor_info theorem covered81 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-48) (hy : (11:ℤ)^3∣y-84) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨81,hx,hy⟩

without_editor_info theorem covered82 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1247) (hy : (11:ℤ)^3∣y-381) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨82,hx,hy⟩

without_editor_info theorem covered83 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1126) (hy : (11:ℤ)^3∣y-986) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨83,hx,hy⟩

without_editor_info theorem covered84 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1005) (hy : (11:ℤ)^3∣y-260) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨84,hx,hy⟩

without_editor_info theorem covered85 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-884) (hy : (11:ℤ)^3∣y-865) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨85,hx,hy⟩

without_editor_info theorem covered86 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-763) (hy : (11:ℤ)^3∣y-139) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨86,hx,hy⟩

without_editor_info theorem covered87 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-642) (hy : (11:ℤ)^3∣y-744) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨87,hx,hy⟩

without_editor_info theorem covered88 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-521) (hy : (11:ℤ)^3∣y-18) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨88,hx,hy⟩

without_editor_info theorem covered89 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-400) (hy : (11:ℤ)^3∣y-623) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨89,hx,hy⟩

without_editor_info theorem covered90 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-279) (hy : (11:ℤ)^3∣y-1228) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨90,hx,hy⟩

without_editor_info theorem covered91 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-158) (hy : (11:ℤ)^3∣y-502) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨91,hx,hy⟩

without_editor_info theorem covered92 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-37) (hy : (11:ℤ)^3∣y-1107) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨92,hx,hy⟩

without_editor_info theorem covered93 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1236) (hy : (11:ℤ)^3∣y-436) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨93,hx,hy⟩

without_editor_info theorem covered94 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1115) (hy : (11:ℤ)^3∣y-1041) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨94,hx,hy⟩

without_editor_info theorem covered95 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-994) (hy : (11:ℤ)^3∣y-315) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨95,hx,hy⟩

without_editor_info theorem covered96 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-873) (hy : (11:ℤ)^3∣y-920) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨96,hx,hy⟩

without_editor_info theorem covered97 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-752) (hy : (11:ℤ)^3∣y-194) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨97,hx,hy⟩

without_editor_info theorem covered98 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-631) (hy : (11:ℤ)^3∣y-799) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨98,hx,hy⟩

without_editor_info theorem covered99 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-510) (hy : (11:ℤ)^3∣y-73) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨99,hx,hy⟩

without_editor_info theorem covered100 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-389) (hy : (11:ℤ)^3∣y-678) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨100,hx,hy⟩

without_editor_info theorem covered101 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-268) (hy : (11:ℤ)^3∣y-1283) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨101,hx,hy⟩

without_editor_info theorem covered102 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-147) (hy : (11:ℤ)^3∣y-557) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨102,hx,hy⟩

without_editor_info theorem covered103 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-26) (hy : (11:ℤ)^3∣y-1162) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨103,hx,hy⟩

without_editor_info theorem covered104 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1225) (hy : (11:ℤ)^3∣y-854) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨104,hx,hy⟩

without_editor_info theorem covered105 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1104) (hy : (11:ℤ)^3∣y-128) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨105,hx,hy⟩

without_editor_info theorem covered106 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-983) (hy : (11:ℤ)^3∣y-733) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨106,hx,hy⟩

without_editor_info theorem covered107 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-862) (hy : (11:ℤ)^3∣y-7) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨107,hx,hy⟩

without_editor_info theorem covered108 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-741) (hy : (11:ℤ)^3∣y-612) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨108,hx,hy⟩

without_editor_info theorem covered109 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-620) (hy : (11:ℤ)^3∣y-1217) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨109,hx,hy⟩

without_editor_info theorem covered110 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-499) (hy : (11:ℤ)^3∣y-491) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨110,hx,hy⟩

without_editor_info theorem covered111 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-378) (hy : (11:ℤ)^3∣y-1096) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨111,hx,hy⟩

without_editor_info theorem covered112 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-257) (hy : (11:ℤ)^3∣y-370) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨112,hx,hy⟩

without_editor_info theorem covered113 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-136) (hy : (11:ℤ)^3∣y-975) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨113,hx,hy⟩

without_editor_info theorem covered114 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-15) (hy : (11:ℤ)^3∣y-249) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨114,hx,hy⟩

without_editor_info theorem covered115 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1214) (hy : (11:ℤ)^3∣y-304) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨115,hx,hy⟩

without_editor_info theorem covered116 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-1093) (hy : (11:ℤ)^3∣y-909) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨116,hx,hy⟩

without_editor_info theorem covered117 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-972) (hy : (11:ℤ)^3∣y-183) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨117,hx,hy⟩

without_editor_info theorem covered118 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-851) (hy : (11:ℤ)^3∣y-788) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨118,hx,hy⟩

without_editor_info theorem covered119 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-730) (hy : (11:ℤ)^3∣y-62) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨119,hx,hy⟩

without_editor_info theorem covered120 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-609) (hy : (11:ℤ)^3∣y-667) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨120,hx,hy⟩

without_editor_info theorem covered121 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-488) (hy : (11:ℤ)^3∣y-1272) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨121,hx,hy⟩

without_editor_info theorem covered122 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-367) (hy : (11:ℤ)^3∣y-546) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨122,hx,hy⟩

without_editor_info theorem covered123 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-246) (hy : (11:ℤ)^3∣y-1151) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨123,hx,hy⟩

without_editor_info theorem covered124 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-125) (hy : (11:ℤ)^3∣y-425) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨124,hx,hy⟩

without_editor_info theorem covered125 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^3∣x-4) (hy : (11:ℤ)^3∣y-1030) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨125,hx,hy⟩

without_editor_info theorem covered126 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^1∣x-3) (hy : (11:ℤ)^1∣y-10) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨126,hx,hy⟩

without_editor_info theorem covered127 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^1∣x-3) (hy : (11:ℤ)^1∣y-6) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨127,hx,hy⟩

without_editor_info theorem covered128 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^1∣x-0) (hy : (11:ℤ)^1∣y-8) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨128,hx,hy⟩

without_editor_info theorem covered129 {x y : ℤ} (_hf : equation x y=0) (hx : (11:ℤ)^1∣x-0) (hy : (11:ℤ)^1∣y-6) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := ⟨129,hx,hy⟩

without_editor_info theorem branch0 {x y : ℤ} (hf : equation x y=0) (hx : (11:ℤ)^2∣x-4) (hy : (11:ℤ)^2∣y-62) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1) 11 (by decide) 121 4 62 [(4,1030),(125,425),(246,1151),(367,546),(488,1272),(609,667),(730,62),(851,788),(972,183),(1093,909),(1214,304)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro X Y hF hX hY
    apply covered125 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered124 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered123 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered122 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered121 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered120 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered119 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered118 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered117 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered116 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered115 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch1 {x y : ℤ} (hf : equation x y=0) (hx : (11:ℤ)^2∣x-15) (hy : (11:ℤ)^2∣y-7) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1) 11 (by decide) 121 15 7 [(15,249),(136,975),(257,370),(378,1096),(499,491),(620,1217),(741,612),(862,7),(983,733),(1104,128),(1225,854)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro X Y hF hX hY
    apply covered114 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered113 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered112 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered111 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered110 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered109 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered108 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered107 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered106 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered105 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered104 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch2 {x y : ℤ} (hf : equation x y=0) (hx : (11:ℤ)^2∣x-26) (hy : (11:ℤ)^2∣y-73) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1) 11 (by decide) 121 26 73 [(26,1162),(147,557),(268,1283),(389,678),(510,73),(631,799),(752,194),(873,920),(994,315),(1115,1041),(1236,436)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro X Y hF hX hY
    apply covered103 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered102 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered101 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered100 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered99 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered98 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered97 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered96 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered95 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered94 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered93 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch3 {x y : ℤ} (hf : equation x y=0) (hx : (11:ℤ)^2∣x-37) (hy : (11:ℤ)^2∣y-18) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1) 11 (by decide) 121 37 18 [(37,1107),(158,502),(279,1228),(400,623),(521,18),(642,744),(763,139),(884,865),(1005,260),(1126,986),(1247,381)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro X Y hF hX hY
    apply covered92 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered91 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered90 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered89 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered88 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered87 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered86 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered85 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered84 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered83 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered82 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch4 {x y : ℤ} (hf : equation x y=0) (hx : (11:ℤ)^2∣x-48) (hy : (11:ℤ)^2∣y-84) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1) 11 (by decide) 121 48 84 [(48,84),(169,810),(290,205),(411,931),(532,326),(653,1052),(774,447),(895,1173),(1016,568),(1137,1294),(1258,689)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro X Y hF hX hY
    apply covered81 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered80 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered79 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered78 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered77 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered76 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered75 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered74 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered73 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered72 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered71 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch5 {x y : ℤ} (hf : equation x y=0) (hx : (11:ℤ)^2∣x-59) (hy : (11:ℤ)^2∣y-29) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1) 11 (by decide) 121 59 29 [(59,755),(180,150),(301,876),(422,271),(543,997),(664,392),(785,1118),(906,513),(1027,1239),(1148,634),(1269,29)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro X Y hF hX hY
    apply covered70 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered69 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered68 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered67 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered66 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered65 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered64 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered63 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered62 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered61 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered60 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch6 {x y : ℤ} (hf : equation x y=0) (hx : (11:ℤ)^2∣x-70) (hy : (11:ℤ)^2∣y-95) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1) 11 (by decide) 121 70 95 [(70,458),(191,1184),(312,579),(433,1305),(554,700),(675,95),(796,821),(917,216),(1038,942),(1159,337),(1280,1063)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro X Y hF hX hY
    apply covered59 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered58 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered57 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered56 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered55 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered54 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered53 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered52 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered51 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered50 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered49 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch7 {x y : ℤ} (hf : equation x y=0) (hx : (11:ℤ)^2∣x-81) (hy : (11:ℤ)^2∣y-40) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1) 11 (by decide) 121 81 40 [(81,524),(202,1250),(323,645),(444,40),(565,766),(686,161),(807,887),(928,282),(1049,1008),(1170,403),(1291,1129)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro X Y hF hX hY
    apply covered48 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered47 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered46 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered45 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered44 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered43 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered42 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered41 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered40 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered39 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered38 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch8 {x y : ℤ} (hf : equation x y=0) (hx : (11:ℤ)^2∣x-92) (hy : (11:ℤ)^2∣y-106) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1) 11 (by decide) 121 92 106 [(92,953),(213,348),(334,1074),(455,469),(576,1195),(697,590),(818,1316),(939,711),(1060,106),(1181,832),(1302,227)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro X Y hF hX hY
    apply covered37 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered36 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered35 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered34 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered33 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered32 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered31 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered30 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered29 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered28 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered27 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch9 {x y : ℤ} (hf : equation x y=0) (hx : (11:ℤ)^2∣x-103) (hy : (11:ℤ)^2∣y-51) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1) 11 (by decide) 121 103 51 [(103,414),(224,1140),(345,535),(466,1261),(587,656),(708,51),(829,777),(950,172),(1071,898),(1192,293),(1313,1019)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · intro X Y hF hX hY
    apply covered17 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered16 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch10 {x y : ℤ} (hf : equation x y=0) (hx : (11:ℤ)^2∣x-114) (hy : (11:ℤ)^2∣y-117) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1) 11 (by decide) 121 114 117 [(114,238),(235,964),(356,359),(477,1085),(598,480),(719,1206),(840,601),(961,1327),(1082,722),(1203,117),(1324,843)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro X Y hF hX hY
    apply covered15 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
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
  · intro X Y hF hX hY
    apply covered5 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num

without_editor_info theorem branch11 {x y : ℤ} (hf : equation x y=0) (hx : (11:ℤ)^1∣x-4) (hy : (11:ℤ)^1∣y-7) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1) 11 (by decide) 11 4 7 [(4,62),(15,7),(26,73),(37,18),(48,84),(59,29),(70,95),(81,40),(92,106),(103,51),(114,117)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · intro X Y hF hX hY
    apply branch3 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
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
  · intro X Y hF hX hY
    apply branch7 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
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

without_editor_info theorem branch12 {x y : ℤ} (hf : equation x y=0) (hx : (11:ℤ)^0∣x-0) (hy : (11:ℤ)^0∣y-0) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := by
  apply CompactResidueCover.cover equation (@equation_congr) (fun x y => ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1) 11 (by decide) 1 0 0 [(0,6),(0,8),(3,6),(3,10),(4,7),(5,0),(6,0),(7,4),(9,8),(10,5)] (by decide +kernel) ?_ hf hx hy
  intro q hq
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro X Y hF hX hY
    apply covered129 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered128 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered127 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply covered126 hF
    · convert hX using 1 <;> norm_num
    · convert hY using 1 <;> norm_num
  · intro X Y hF hX hY
    apply branch11 hF
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

without_editor_info theorem local_cover {x y : ℤ} (hf : equation x y=0) : ∃ i : Fin 130, (11:ℤ)^(residues i).2.2∣x-(residues i).1 ∧ (11:ℤ)^(residues i).2.2∣y-(residues i).2.1 := branch12 hf (by simp) (by simp)

without_editor_info theorem local_values {x y : ℤ} (hf : equation x y=0) : (value (oddH 11) (arguments0 x y),value (oddH 11) (arguments1 x y)) ∈ ([(1,1)]:List (ℤ × ℤ)) := by
  obtain ⟨i,hx,hy⟩ := local_cover hf
  have ht : ∀ i : Fin 130, (sign (targets0 i),sign (targets1 i)) ∈ ([(1,1)]:List (ℤ × ℤ)) := by intro i; simp only [targets0,targets1]; decide +kernel
  simpa only [value_phase0 hf,cell_value0 i hx hy,value_phase1 hf,cell_value1 i hx hy] using ht i

end RationalAt11

without_editor_info theorem local11 {x y : ℤ} (hf : equation x y=0) : (value (oddH 11) (arguments0 x y),value (oddH 11) (arguments1 x y)) ∈ ([(1,1)]:List (ℤ × ℤ)) := RationalAt11.local_values hf

without_editor_info theorem constant_local457_0 {x y : ℤ} (hf : equation x y=0) : value (oddH 457) (arguments0 x y)=1 := by
  exact ordinary_support0 hf 457 (by decide) (by decide) (by decide)

without_editor_info theorem constant_local457_1 {x y : ℤ} (hf : equation x y=0) : value (oddH 457) (arguments1 x y)=1 := by
  have hd0 : ¬(457:ℤ)∣(eval H4 x y) := by norm_num [H4,eval]
  have hj0 : jacobiSym (eval H4 x y) 457=1 := by norm_num [H4,eval]
  have he0 : oddH 457 (eval H3 x y) (eval H4 x y)=1 := by
    rw [odd_edge (eval H3 x y) (eval H4 x y) (fun h => hd0 h.2),padicValInt.eq_zero_of_not_dvd hd0,hj0] <;> norm_num
  simp only [value,arguments1,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,he0,mul_one]

without_editor_info theorem local457 {x y : ℤ} (hf : equation x y=0) : (value (oddH 457) (arguments0 x y),value (oddH 457) (arguments1 x y)) ∈ ([(1,1)]:List (ℤ × ℤ)) := by
  rw [constant_local457_0 hf,constant_local457_1 hf]
  exact List.mem_singleton_self _

without_editor_info theorem negative_bit {a : ℤ} : decide (a<0)=true ↔ 0<(-1:ℤ)*a := by simp

without_editor_info theorem positive_bit {a : ℤ} (ha : a≠0) : decide (a<0)=false ↔ 0<(1:ℤ)*a := by
  simp only [decide_eq_false_iff_not,not_lt,one_mul]
  omega

without_editor_info theorem infinity_bits (a b : ℤ) : infinity a b =
    (if decide (a<0) && decide (b<0) then (-1:ℤ) else 1) := by simp [infinity]

without_editor_info theorem real_check : ∀ b0 b1 b2 b3 b4 : Bool,
    (b0=false) →
    (b1=false) →
    (b2=false) →
    (b3=false) →
    (b4=true) →
    (([(if b0 && b1 then (-1:ℤ) else 1)]:List ℤ).prod,([(if b3 && b4 then (-1:ℤ) else 1)]:List ℤ).prod) ∈ ([(1,1)]:List (ℤ × ℤ)) := by
  intro b0 b1 b2 b3 b4 h0 h1 h2 h3 h4
  subst b0
  subst b1
  subst b2
  subst b3
  subst b4
  try simp only [Bool.false_and,Bool.and_false,Bool.true_and,Bool.and_true,ite_false,ite_true,one_mul,mul_one]
  all_goals
    decide +kernel

without_editor_info theorem real_values {x y : ℤ} (hf : equation x y=0) : (value infinity (arguments0 x y),value infinity (arguments1 x y)) ∈ ([(1,1)]:List (ℤ × ℤ)) := by
  have h := real_check (decide ((eval H0 x y)<0)) (decide ((eval H1 x y)<0)) (decide ((eval H2 x y)<0)) (decide ((eval H3 x y)<0)) (decide ((eval H4 x y)<0))
    ((positive_bit (nonzero0 hf)).2 (positive0 hf))
    ((positive_bit (nonzero1 hf)).2 (positive1 hf))
    ((positive_bit (nonzero2 hf)).2 (positive2 hf))
    ((positive_bit (nonzero3 hf)).2 (positive3 hf))
    ((negative_bit).2 (positive4 hf))
  simpa only [value,infinity_bits,List.map_cons,List.map_nil,arguments0,arguments1] using h

without_editor_info theorem no_solution {x y : ℤ} (hf : equation x y=0) : False := by
  have h0 := GraphCert.Quadratic.global_except (E := ({11,457}:Finset ℕ)) (arguments0 x y)
    (by intro p hp; simp only [Finset.mem_insert,Finset.mem_singleton] at hp; rcases hp with rfl | rfl <;> decide)
    (arguments_nonzero0 hf) (ordinary0 hf)
  have h1 := GraphCert.Quadratic.global_except (E := ({11,457}:Finset ℕ)) (arguments1 x y)
    (by intro p hp; simp only [Finset.mem_insert,Finset.mem_singleton] at hp; rcases hp with rfl | rfl <;> decide)
    (arguments_nonzero1 hf) (ordinary1 hf)
  have hp2 := local2 hf
  have hp11 := local11 hf
  have hp457 := local457 hf
  have hr := real_values hf
  norm_num only [Finset.prod_insert,Finset.prod_singleton,Finset.mem_singleton,Finset.mem_insert,Finset.notMem_empty,not_false_eq_true,Finset.prod_empty] at h0 h1
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hp2
  all_goals rcases hp2 with hp2 | hp2
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hp11
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hp457
  all_goals
    simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hr
    rcases hr with hr
  all_goals simp_all

end GraphCert.Generated.gd2742d1b04aace1cbd711c94

namespace OriginalEquation
def f (x y : ℤ) : ℤ := x^4+x*y+2*y^3+y+2
theorem no_integer_solutions : ¬ ∃ x y : ℤ, f x y = 0 := by
  rintro ⟨x, y, hf⟩
  apply GraphCert.Generated.gd2742d1b04aace1cbd711c94.no_solution (x := x) (y := y)
  change GraphCert.Generated.gd2742d1b04aace1cbd711c94.equation x y = 0
  convert hf using 1 <;>
    simp [f, GraphCert.Generated.gd2742d1b04aace1cbd711c94.equation, GraphCert.Generated.gd2742d1b04aace1cbd711c94.F,
      QuadraticNorm.eval] <;> ring
end OriginalEquation


                                       
theorem E146192020_1 : ¬ ∃ x y : ℤ, x^4 + x*y + 2*y^3 + y + 2 = 0 := by
  rintro ⟨x, y, h⟩
  apply OriginalEquation.no_integer_solutions
  refine ⟨x, y, ?_⟩
  dsimp [OriginalEquation.f]
  linear_combination h

#print axioms E146192020_1
