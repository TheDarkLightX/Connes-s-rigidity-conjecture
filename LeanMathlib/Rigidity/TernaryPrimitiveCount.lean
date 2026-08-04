import Mathlib
import LeanMathlib.Rigidity.TernaryPrimitiveArithmetic
import LeanMathlib.Rigidity.TernaryTruncatedInvariant

namespace LeanMathlib.Rigidity

noncomputable section

open scoped BigOperators

private abbrev F₃ := ZMod 3
private abbrev R₃ := Polynomial F₃
private abbrev V₃ := Fin 3 → R₃

/-- Ternary polynomials of degree strictly below `N`. -/
abbrev TernaryBoundedPolynomial (N : ℕ) := Polynomial.degreeLT F₃ N

/-- Monic ternary polynomials of exact degree `N`. -/
abbrev TernaryMonicPolynomial (N : ℕ) :=
  {p : R₃ // p.Monic ∧ p.natDegree = N}

/-- Coefficient equivalence for bounded ternary polynomials. -/
noncomputable def ternaryBoundedPolynomialEquiv (N : ℕ) :
    TernaryBoundedPolynomial N ≃ (Fin N → F₃) :=
  (Polynomial.degreeLTEquiv F₃ N).toEquiv

noncomputable instance ternaryBoundedPolynomialFintype (N : ℕ) :
    Fintype (TernaryBoundedPolynomial N) :=
  Fintype.ofEquiv (Fin N → F₃) (ternaryBoundedPolynomialEquiv N).symm

/-- There are `3^N` ternary polynomials of degree below `N`. -/
theorem card_ternaryBoundedPolynomial (N : ℕ) :
    Fintype.card (TernaryBoundedPolynomial N) = 3 ^ N := by
  rw [Fintype.card_congr (ternaryBoundedPolynomialEquiv N),
    Fintype.card_fun, Fintype.card_fin, ZMod.card]

/-- A monic degree-`N` polynomial is determined by its `N` lower coefficients. -/
noncomputable def ternaryMonicPolynomialEquiv (N : ℕ) :
    TernaryMonicPolynomial N ≃ TernaryBoundedPolynomial N :=
  Polynomial.monicEquivDegreeLT N

noncomputable instance ternaryMonicPolynomialFintype (N : ℕ) :
    Fintype (TernaryMonicPolynomial N) :=
  Fintype.ofEquiv (TernaryBoundedPolynomial N)
    (ternaryMonicPolynomialEquiv N).symm

/-- There are `3^N` monic ternary polynomials of exact degree `N`. -/
theorem card_ternaryMonicPolynomial (N : ℕ) :
    Fintype.card (TernaryMonicPolynomial N) = 3 ^ N := by
  rw [Fintype.card_congr (ternaryMonicPolynomialEquiv N),
    card_ternaryBoundedPolynomial]

/-- There are `3^(3N)` rank-three ternary polynomial vectors in the degree box. -/
theorem card_ternaryPolynomialVector (N : ℕ) :
    Fintype.card (TernaryTruncatedPolynomialVector N) = 3 ^ (3 * N) :=
  card_ternaryTruncatedPolynomialVector N

/-- GCD of the three polynomial coordinates. -/
def ternaryVectorGCD (v : V₃) : R₃ :=
  (Finset.univ : Finset (Fin 3)).gcd v

/-- A rank-three polynomial vector is primitive when its coordinate gcd is one. -/
def IsTernaryPrimitiveVector (v : V₃) : Prop :=
  ternaryVectorGCD v = 1

/-- Primitive vectors inside the finite degree box. -/
abbrev TernaryPrimitivePolynomialVector (N : ℕ) :=
  {v : TernaryTruncatedPolynomialVector N //
    IsTernaryPrimitiveVector (fun i => (v i : R₃))}

/-- Raw polynomial vector underlying a bounded vector. -/
def ternaryPolynomialVectorVal {N : ℕ}
    (v : TernaryTruncatedPolynomialVector N) : V₃ :=
  fun i => (v i : R₃)

@[simp]
theorem ternaryPolynomialVectorVal_apply {N : ℕ}
    (v : TernaryTruncatedPolynomialVector N) (i : Fin 3) :
    ternaryPolynomialVectorVal v i = (v i : R₃) := rfl

@[simp]
theorem ternaryPolynomialVectorVal_eq_zero_iff {N : ℕ}
    (v : TernaryTruncatedPolynomialVector N) :
    ternaryPolynomialVectorVal v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    apply Subtype.ext
    exact congrFun h i
  · rintro rfl
    rfl

/-- Nonzero bounded polynomial vectors. -/
abbrev TernaryNonzeroPolynomialVector (N : ℕ) :=
  {v : TernaryTruncatedPolynomialVector N // v ≠ 0}

noncomputable instance ternaryPrimitivePolynomialVectorFintype (N : ℕ) :
    Fintype (TernaryPrimitivePolynomialVector N) := by
  classical
  exact Fintype.ofFinite _

/-- The coordinate gcd divides every coordinate. -/
theorem ternaryVectorGCD_dvd (v : V₃) (i : Fin 3) :
    ternaryVectorGCD v ∣ v i :=
  Finset.gcd_dvd (Finset.mem_univ i)

@[simp]
theorem ternaryVectorGCD_eq_zero_iff (v : V₃) :
    ternaryVectorGCD v = 0 ↔ v = 0 := by
  rw [ternaryVectorGCD, Finset.gcd_eq_zero_iff]
  simp [funext_iff]

/-- Nonzero vector has nonzero gcd. -/
theorem ternaryVectorGCD_ne_zero {v : V₃} (hv : v ≠ 0) :
    ternaryVectorGCD v ≠ 0 := by
  simpa [ternaryVectorGCD_eq_zero_iff] using hv

/-- The normalized polynomial gcd is monic. -/
theorem ternaryVectorGCD_monic {v : V₃} (hv : v ≠ 0) :
    (ternaryVectorGCD v).Monic := by
  have hnormalized : normalize (ternaryVectorGCD v) = ternaryVectorGCD v :=
    Finset.normalize_gcd
  rw [← hnormalized]
  exact Polynomial.monic_normalize (ternaryVectorGCD_ne_zero hv)

/-- A primitive vector is nonzero. -/
theorem IsTernaryPrimitiveVector.ne_zero {v : V₃}
    (hv : IsTernaryPrimitiveVector v) : v ≠ 0 := by
  intro hzero
  have hgzero : ternaryVectorGCD v = 0 :=
    (ternaryVectorGCD_eq_zero_iff v).mpr hzero
  exact zero_ne_one (hgzero.symm.trans hv)

/-- GCD scales by a monic common factor. -/
theorem ternaryVectorGCD_mul (g : R₃) (hg : g.Monic) (v : V₃) :
    ternaryVectorGCD (fun i => g * v i) = g * ternaryVectorGCD v := by
  unfold ternaryVectorGCD
  rw [Finset.gcd_mul_left, hg.normalize_eq_self]

/-- Dividing by the gcd produces a primitive vector. -/
theorem ternaryVectorGCD_div_eq_one {v : V₃} (hv : v ≠ 0) :
    ternaryVectorGCD (fun i => v i / ternaryVectorGCD v) = 1 := by
  obtain ⟨i, _, hi⟩ :=
    Finset.gcd_ne_zero_iff.mp (ternaryVectorGCD_ne_zero hv)
  change Finset.univ.gcd
    (fun i => v i / Finset.univ.gcd v) = 1
  exact Finset.gcd_div_eq_one (Finset.mem_univ i) hi

/-- A nonzero bounded polynomial has natural degree below the box bound. -/
theorem ternaryBounded_natDegree_lt {N : ℕ}
    (p : TernaryBoundedPolynomial N) (hp : (p : R₃) ≠ 0) :
    (p : R₃).natDegree < N := by
  apply (Polynomial.natDegree_lt_iff_degree_lt hp).mpr
  exact Polynomial.mem_degreeLT.mp p.property

/-- Repackage a polynomial with a degree bound as a bounded polynomial. -/
theorem ternary_mem_degreeLT_of_natDegree_lt {N : ℕ} (p : R₃)
    (hp : p = 0 ∨ p.natDegree < N) :
    p ∈ Polynomial.degreeLT F₃ N := by
  rcases hp with rfl | hp
  · exact (Polynomial.degreeLT F₃ N).zero_mem
  · apply Polynomial.mem_degreeLT.mpr
    by_cases hpzero : p = 0
    · simp [hpzero]
    · exact (Polynomial.natDegree_lt_iff_degree_lt hpzero).mp hp

/-- Cardinality as a sum of fiber cardinalities. -/
theorem ternary_card_eq_sum_card_fibers
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) :
    Fintype.card α = ∑ b : β, Fintype.card {a : α // f a = b} := by
  classical
  calc
    Fintype.card α = Fintype.card (Σ b : β, {a : α // f a = b}) :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ b : β, Fintype.card {a : α // f a = b} := Fintype.card_sigma

/-- Fiber cardinality after splitting each fiber as a product. -/
theorem ternary_card_eq_sum_card_products
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (G P : β → Type*) [∀ b, Fintype (G b)] [∀ b, Fintype (P b)]
    (f : α → β) (e : ∀ b, {a : α // f a = b} ≃ G b × P b) :
    Fintype.card α =
      ∑ b : β, Fintype.card (G b) * Fintype.card (P b) := by
  classical
  calc
    Fintype.card α = ∑ b : β, Fintype.card {a : α // f a = b} :=
      ternary_card_eq_sum_card_fibers f
    _ = ∑ b : β, Fintype.card (G b) * Fintype.card (P b) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Fintype.card_congr (e b), Fintype.card_prod]

/-- Number of nonzero vectors in the degree box. -/
theorem card_ternaryNonzeroPolynomialVector (N : ℕ) :
    Fintype.card (TernaryNonzeroPolynomialVector N) =
      3 ^ (3 * N) - 1 := by
  classical
  rw [show Fintype.card (TernaryNonzeroPolynomialVector N) =
      Fintype.card (TernaryTruncatedPolynomialVector N) -
        Fintype.card {v : TernaryTruncatedPolynomialVector N // v = 0} from
      Fintype.card_subtype_compl
        (fun v : TernaryTruncatedPolynomialVector N => v = 0)]
  rw [Fintype.card_subtype_eq, card_ternaryPolynomialVector]

/-- GCD degree lies below the finite box size. -/
theorem ternaryVectorGCD_natDegree_lt {N : ℕ}
    (v : TernaryNonzeroPolynomialVector N) :
    (ternaryVectorGCD (ternaryPolynomialVectorVal v.val)).natDegree < N := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, v.val i ≠ 0 := by
    by_contra h
    apply v.property
    apply funext
    intro i
    exact not_ne_iff.mp (not_exists.mp h i)
  have hi' : (v.val i : R₃) ≠ 0 := by
    intro hzero
    apply hi
    apply Subtype.ext
    simpa using hzero
  exact lt_of_le_of_lt
    (Polynomial.natDegree_le_of_dvd
      (ternaryVectorGCD_dvd _ i) hi')
    (ternaryBounded_natDegree_lt (v.val i) hi')

/-- Classify a nonzero vector by the degree of its monic gcd. -/
def ternaryGCDDegreeMap (N : ℕ) :
    TernaryNonzeroPolynomialVector N → Fin N :=
  fun v => ⟨(ternaryVectorGCD
    (ternaryPolynomialVectorVal v.val)).natDegree,
    ternaryVectorGCD_natDegree_lt v⟩

/-- Coercing a nonzero bounded vector gives a nonzero raw vector. -/
theorem ternaryNonzeroVector_coe_ne_zero {N : ℕ}
    (v : TernaryNonzeroPolynomialVector N) :
    ternaryPolynomialVectorVal v.val ≠ 0 := by
  exact fun hzero => v.property
    ((ternaryPolynomialVectorVal_eq_zero_iff v.val).mp hzero)

/-- The coordinatewise gcd quotient is primitive. -/
theorem ternaryQuotient_isPrimitive {N : ℕ}
    (v : TernaryNonzeroPolynomialVector N) :
    IsTernaryPrimitiveVector
      (fun i => (v.val i : R₃) /
        ternaryVectorGCD (ternaryPolynomialVectorVal v.val)) :=
  ternaryVectorGCD_div_eq_one (ternaryNonzeroVector_coe_ne_zero v)

/-- Quotient coordinates remain inside the reduced degree box. -/
theorem ternaryQuotient_mem_degreeLT {N : ℕ} {d : Fin N}
    (v : {v : TernaryNonzeroPolynomialVector N //
      ternaryGCDDegreeMap N v = d})
    (i : Fin 3) :
    (v.val.val i : R₃) /
        ternaryVectorGCD (ternaryPolynomialVectorVal v.val.val) ∈
      Polynomial.degreeLT F₃ (N - d.val) := by
  let p : R₃ := v.val.val i
  let g : R₃ := ternaryVectorGCD
    (ternaryPolynomialVectorVal v.val.val)
  have hg : g.Monic :=
    ternaryVectorGCD_monic (ternaryNonzeroVector_coe_ne_zero v.val)
  have hd : g.natDegree = d.val := congrArg Fin.val v.property
  apply ternary_mem_degreeLT_of_natDegree_lt
  by_cases hq : p / g = 0
  · exact Or.inl hq
  · right
    have hp : p ≠ 0 := by
      intro hzero
      simp [hzero] at hq
    have hpbound : p.natDegree < N :=
      ternaryBounded_natDegree_lt (v.val.val i) hp
    have hdegree : (p / g).natDegree = p.natDegree - g.natDegree := by
      rw [← Polynomial.divByMonic_eq_div p hg,
        Polynomial.natDegree_divByMonic p hg]
    rw [hdegree, hd]
    omega

/-- Monic gcd factor of a fiber element. -/
def ternaryFiberFactor {N : ℕ} {d : Fin N}
    (v : {v : TernaryNonzeroPolynomialVector N //
      ternaryGCDDegreeMap N v = d}) :
    TernaryMonicPolynomial d.val :=
  ⟨ternaryVectorGCD (ternaryPolynomialVectorVal v.val.val),
    ternaryVectorGCD_monic (ternaryNonzeroVector_coe_ne_zero v.val),
    congrArg Fin.val v.property⟩

/-- Primitive quotient of a fiber element. -/
def ternaryFiberPrimitive {N : ℕ} {d : Fin N}
    (v : {v : TernaryNonzeroPolynomialVector N //
      ternaryGCDDegreeMap N v = d}) :
    TernaryPrimitivePolynomialVector (N - d.val) :=
  ⟨fun i => ⟨(v.val.val i : R₃) /
      ternaryVectorGCD (ternaryPolynomialVectorVal v.val.val),
      ternaryQuotient_mem_degreeLT v i⟩,
    ternaryQuotient_isPrimitive v.val⟩

/-- Fiber decomposition map into monic factor and primitive quotient. -/
def ternaryFiberToProduct {N : ℕ} {d : Fin N}
    (v : {v : TernaryNonzeroPolynomialVector N //
      ternaryGCDDegreeMap N v = d}) :
    TernaryMonicPolynomial d.val ×
      TernaryPrimitivePolynomialVector (N - d.val) :=
  ⟨ternaryFiberFactor v, ternaryFiberPrimitive v⟩

/-- Multiplying the factor and primitive quotient stays in the original box. -/
theorem ternaryProduct_mem_degreeLT {N : ℕ} (d : Fin N)
    (x : TernaryMonicPolynomial d.val ×
      TernaryPrimitivePolynomialVector (N - d.val))
    (i : Fin 3) :
    x.1.val * (x.2.val i : R₃) ∈ Polynomial.degreeLT F₃ N := by
  apply ternary_mem_degreeLT_of_natDegree_lt
  by_cases hw : (x.2.val i : R₃) = 0
  · exact Or.inl (by simp [hw])
  · right
    have hwbound := ternaryBounded_natDegree_lt (x.2.val i) hw
    have hdegree := x.1.property.1.natDegree_mul' hw
    rw [hdegree, x.1.property.2]
    omega

/-- Reconstruct the original bounded vector from factor and quotient. -/
def ternaryProductVector {N : ℕ} (d : Fin N)
    (x : TernaryMonicPolynomial d.val ×
      TernaryPrimitivePolynomialVector (N - d.val)) :
    TernaryTruncatedPolynomialVector N :=
  fun i => ⟨x.1.val * (x.2.val i : R₃),
    ternaryProduct_mem_degreeLT d x i⟩

/-- The reconstructed vector has the prescribed gcd. -/
theorem ternaryProductVector_gcd {N : ℕ} (d : Fin N)
    (x : TernaryMonicPolynomial d.val ×
      TernaryPrimitivePolynomialVector (N - d.val)) :
    ternaryVectorGCD
      (ternaryPolynomialVectorVal (ternaryProductVector d x)) = x.1.val := by
  change ternaryVectorGCD
    (fun i => x.1.val * (x.2.val i : R₃)) = x.1.val
  rw [ternaryVectorGCD_mul x.1.val x.1.property.1,
    x.2.property, mul_one]

/-- The reconstructed vector is nonzero. -/
theorem ternaryProductVector_ne_zero {N : ℕ} (d : Fin N)
    (x : TernaryMonicPolynomial d.val ×
      TernaryPrimitivePolynomialVector (N - d.val)) :
    ternaryProductVector d x ≠ 0 := by
  intro hzero
  have hraw : ternaryPolynomialVectorVal (ternaryProductVector d x) = 0 := by
    rw [hzero]
    rfl
  have hgzero : ternaryVectorGCD
      (ternaryPolynomialVectorVal (ternaryProductVector d x)) = 0 := by
    rw [hraw]
    exact (ternaryVectorGCD_eq_zero_iff _).mpr rfl
  rw [ternaryProductVector_gcd d x] at hgzero
  exact x.1.property.1.ne_zero hgzero

/-- Reconstructed nonzero vector. -/
def ternaryProductToNonzero {N : ℕ} (d : Fin N)
    (x : TernaryMonicPolynomial d.val ×
      TernaryPrimitivePolynomialVector (N - d.val)) :
    TernaryNonzeroPolynomialVector N :=
  ⟨ternaryProductVector d x, ternaryProductVector_ne_zero d x⟩

/-- Reconstructed vector lies in the correct gcd-degree fiber. -/
theorem ternaryProductToNonzero_gcdDegree {N : ℕ} (d : Fin N)
    (x : TernaryMonicPolynomial d.val ×
      TernaryPrimitivePolynomialVector (N - d.val)) :
    ternaryGCDDegreeMap N (ternaryProductToNonzero d x) = d := by
  apply Fin.ext
  change (ternaryVectorGCD
    (ternaryPolynomialVectorVal (ternaryProductVector d x))).natDegree = d.val
  rw [ternaryProductVector_gcd d x, x.1.property.2]

/-- Product data as a fiber element. -/
def ternaryProductToFiber {N : ℕ} (d : Fin N)
    (x : TernaryMonicPolynomial d.val ×
      TernaryPrimitivePolynomialVector (N - d.val)) :
    {v : TernaryNonzeroPolynomialVector N //
      ternaryGCDDegreeMap N v = d} :=
  ⟨ternaryProductToNonzero d x,
    ternaryProductToNonzero_gcdDegree d x⟩

/-- Reconstructing after factoring gives the original vector. -/
theorem ternaryProductToFiber_fiberToProduct {N : ℕ} {d : Fin N}
    (v : {v : TernaryNonzeroPolynomialVector N //
      ternaryGCDDegreeMap N v = d}) :
    ternaryProductToFiber d (ternaryFiberToProduct v) = v := by
  apply Subtype.ext
  apply Subtype.ext
  apply funext
  intro i
  apply Subtype.ext
  change ternaryVectorGCD (ternaryPolynomialVectorVal v.val.val) *
      ((v.val.val i : R₃) /
        ternaryVectorGCD (ternaryPolynomialVectorVal v.val.val)) =
      (v.val.val i : R₃)
  exact EuclideanDomain.mul_div_cancel'
    (ternaryVectorGCD_monic
      (ternaryNonzeroVector_coe_ne_zero v.val)).ne_zero
    (ternaryVectorGCD_dvd _ i)

/-- Factoring after reconstructing gives the original product data. -/
theorem ternaryFiberToProduct_productToFiber {N : ℕ} (d : Fin N)
    (x : TernaryMonicPolynomial d.val ×
      TernaryPrimitivePolynomialVector (N - d.val)) :
    ternaryFiberToProduct (ternaryProductToFiber d x) = x := by
  apply Prod.ext
  · apply Subtype.ext
    exact ternaryProductVector_gcd d x
  · apply Subtype.ext
    apply funext
    intro i
    apply Subtype.ext
    change (x.1.val * (x.2.val i : R₃)) /
        ternaryVectorGCD
          (ternaryPolynomialVectorVal (ternaryProductVector d x)) =
      (x.2.val i : R₃)
    rw [ternaryProductVector_gcd d x,
      ← Polynomial.divByMonic_eq_div _ x.1.property.1]
    exact Polynomial.mul_divByMonic_cancel_left _ x.1.property.1

/-- Exact gcd-degree fiber decomposition. -/
noncomputable def ternaryGCDDegreeFiberEquiv {N : ℕ} (d : Fin N) :
    {v : TernaryNonzeroPolynomialVector N //
      ternaryGCDDegreeMap N v = d} ≃
      TernaryMonicPolynomial d.val ×
        TernaryPrimitivePolynomialVector (N - d.val) where
  toFun := ternaryFiberToProduct
  invFun := ternaryProductToFiber d
  left_inv := ternaryProductToFiber_fiberToProduct
  right_inv := ternaryFiberToProduct_productToFiber d

/-- GCD convolution for ternary rank-three vectors. -/
theorem ternary_primitive_gcd_convolution (N : ℕ) :
    3 ^ (3 * N) - 1 =
      ∑ d : Fin N,
        3 ^ d.val *
          Fintype.card (TernaryPrimitivePolynomialVector (N - d.val)) := by
  rw [← card_ternaryNonzeroPolynomialVector]
  calc
    Fintype.card (TernaryNonzeroPolynomialVector N) =
      ∑ d : Fin N,
        Fintype.card (TernaryMonicPolynomial d.val) *
          Fintype.card (TernaryPrimitivePolynomialVector (N - d.val)) :=
      ternary_card_eq_sum_card_products
        (fun d : Fin N => TernaryMonicPolynomial d.val)
        (fun d : Fin N => TernaryPrimitivePolynomialVector (N - d.val))
        (ternaryGCDDegreeMap N) ternaryGCDDegreeFiberEquiv
    _ = _ := by simp_rw [card_ternaryMonicPolynomial]

/-- Range-indexed gcd convolution. -/
theorem ternary_primitive_gcd_convolution_range (N : ℕ) :
    3 ^ (3 * N) - 1 =
      ∑ d ∈ Finset.range N,
        3 ^ d *
          Fintype.card (TernaryPrimitivePolynomialVector (N - d)) := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact ternary_primitive_gcd_convolution N

/-- Shift identity for a ternary gcd convolution. -/
theorem ternary_primitive_convolution_shift (P : ℕ → ℕ) (n : ℕ) :
    (∑ d ∈ Finset.range (n + 1), 3 ^ d * P (n + 1 - d)) =
      P (n + 1) +
        3 * ∑ d ∈ Finset.range n, 3 ^ d * P (n - d) := by
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.sub_zero]
  have hterm : ∀ d : ℕ, n + 1 - (d + 1) = n - d := by
    intro d
    omega
  simp_rw [hterm, pow_succ]
  rw [Finset.mul_sum]
  simp [Nat.mul_left_comm, Nat.mul_comm, Nat.add_comm]

/-- Closed-form arithmetic subtraction for the ternary primitive count. -/
theorem ternaryPrimitiveCount_subtraction (N : ℕ) (hN : 0 < N) :
    (3 ^ (3 * N) - 1) -
        3 * (3 ^ (3 * (N - 1)) - 1) =
      ternaryPrimitiveCount N := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  rw [ternaryPrimitiveCount_succ]
  have hcube : 3 ^ (3 * n + 3) = 27 * 3 ^ (3 * n) := by
    calc
      3 ^ (3 * n + 3) = 3 ^ (3 * n) * 3 ^ 3 := by rw [pow_add]
      _ = 27 * 3 ^ (3 * n) := by ring
  have hcurrent : 3 ^ (3 * (n + 1)) = 27 * 3 ^ (3 * n) := by
    calc
      3 ^ (3 * (n + 1)) = 3 ^ (3 * n + 3) := by
        congr 1
      _ = 27 * 3 ^ (3 * n) := hcube
  have hprev : 3 ^ (3 * ((n + 1) - 1)) = 3 ^ (3 * n) := by
    congr 1
  have hnext : 3 ^ (3 * n + 1) = 3 * 3 ^ (3 * n) := by
    calc
      3 ^ (3 * n + 1) = 3 ^ (3 * n) * 3 ^ 1 := by rw [pow_add]
      _ = 3 * 3 ^ (3 * n) := by ring
  rw [hcurrent, hprev, hcube, hnext]
  have hpositive : 0 < 3 ^ (3 * n) := pow_pos (by omega) _
  omega

/-- A convolution satisfying the gcd identity has the ternary closed form. -/
theorem ternary_primitive_card_of_convolution (P : ℕ → ℕ)
    (hP : ∀ N : ℕ, 3 ^ (3 * N) - 1 =
      ∑ d ∈ Finset.range N, 3 ^ d * P (N - d))
    (N : ℕ) (hN : 0 < N) :
    P N = ternaryPrimitiveCount N := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  have hcurrent := hP (n + 1)
  have hprevious := hP n
  rw [ternary_primitive_convolution_shift] at hcurrent
  rw [← hprevious] at hcurrent
  have hsub :
      (3 ^ (3 * (n + 1)) - 1) -
          3 * (3 ^ (3 * n) - 1) =
        ternaryPrimitiveCount (n + 1) := by
    simpa using ternaryPrimitiveCount_subtraction (n + 1) (by omega)
  calc
    P (n + 1) =
        (P (n + 1) + 3 * (3 ^ (3 * n) - 1)) -
          3 * (3 ^ (3 * n) - 1) :=
      (Nat.add_sub_cancel_right _ _).symm
    _ = (3 ^ (3 * (n + 1)) - 1) -
          3 * (3 ^ (3 * n) - 1) := by rw [← hcurrent]
    _ = ternaryPrimitiveCount (n + 1) := hsub

/-- Exact cardinality of primitive ternary rank-three polynomial vectors. -/
theorem card_ternaryPrimitivePolynomialVector (N : ℕ) (hN : 0 < N) :
    Fintype.card (TernaryPrimitivePolynomialVector N) =
      ternaryPrimitiveCount N := by
  exact ternary_primitive_card_of_convolution
    (fun n => Fintype.card (TernaryPrimitivePolynomialVector n))
    ternary_primitive_gcd_convolution_range N hN

/-- Explicit exact primitive-vector cardinal formula. -/
theorem card_ternaryPrimitivePolynomialVector_formula
    (N : ℕ) (hN : 0 < N) :
    Fintype.card (TernaryPrimitivePolynomialVector N) =
      3 ^ (3 * (N - 1) + 3) - 3 ^ (3 * (N - 1) + 1) + 2 := by
  rw [card_ternaryPrimitivePolynomialVector N hN]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  rfl

end

end LeanMathlib.Rigidity