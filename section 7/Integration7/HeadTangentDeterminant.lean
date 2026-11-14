import Integration7.PolynomialTangentLines

/-! The tangent determinant of a correspondence with a free last
coordinate equals the determinant of its head correspondence. -/
noncomputable section
open SpecialTransformations.Section7 SpecialTransformations.Section9
open scoped BigOperators

namespace IntegrationInACVF.Section7

def headPairIndex (k : ℕ) : Fin (k + k) → Fin ((k + 1) + (k + 1)) :=
  finSumFinEquiv ∘ Sum.map Fin.castSucc Fin.castSucc ∘ finSumFinEquiv.symm

theorem headPairIndex_injective (k : ℕ) : Function.Injective (headPairIndex k) :=
  finSumFinEquiv.injective.comp
    ((Sum.map_injective.mpr ⟨Fin.castSucc_injective k, Fin.castSucc_injective k⟩).comp
      finSumFinEquiv.symm.injective)

@[simp] theorem headPairIndex_left (k : ℕ) (i : Fin k) :
    headPairIndex k (productLeft k k i) = productLeft (k + 1) (k + 1) i.castSucc := by
  change finSumFinEquiv (Sum.map Fin.castSucc Fin.castSucc
    ((finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k + k)).symm (finSumFinEquiv (Sum.inl i)))) =
      finSumFinEquiv (Sum.inl i.castSucc)
  rw [Equiv.symm_apply_apply]
  rfl

@[simp] theorem headPairIndex_right (k : ℕ) (i : Fin k) :
    headPairIndex k (productRight k k i) = productRight (k + 1) (k + 1) i.castSucc := by
  change finSumFinEquiv (Sum.map Fin.castSucc Fin.castSucc
    ((finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k + k)).symm (finSumFinEquiv (Sum.inr i)))) =
      finSumFinEquiv (Sum.inr i.castSucc)
  rw [Equiv.symm_apply_apply]
  rfl

theorem productTuple_comp_headPairIndex {X : Type*} {k : ℕ}
    (x y : Fin (k + 1) → X) :
    productTuple x y ∘ headPairIndex k = productTuple (x ∘ Fin.castSucc) (y ∘ Fin.castSucc) := by
  apply productTuple_ext <;> intro i <;> simp only [Function.comp_apply,
    headPairIndex_left, headPairIndex_right, productTuple_left, productTuple_right]

def lastPairIndices (k : ℕ) : Finset (Fin ((k + 1) + (k + 1))) :=
  {productLeft (k + 1) (k + 1) (Fin.last k), productRight (k + 1) (k + 1) (Fin.last k)}

theorem lastPair_indicator {X : Type*} {k : ℕ} (a b : X) :
    (fun i => if i ∈ lastPairIndices k then a else b) =
      productTuple (Fin.snoc (fun _ : Fin k => b) a) (Fin.snoc (fun _ : Fin k => b) a) := by
  classical
  apply productTuple_ext
  · intro i
    simp only [lastPairIndices, Finset.mem_insert, Finset.mem_singleton,
      (productLeft (k + 1) (k + 1)).injective.eq_iff,
      productLeft_ne_right, or_false, productTuple_left]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [Fin.castSucc_ne_last]
  · intro i
    have hne : productRight (k + 1) (k + 1) i ≠
        productLeft (k + 1) (k + 1) (Fin.last k) :=
      (productLeft_ne_right (Fin.last k) i).symm
    simp only [lastPairIndices, Finset.mem_insert, Finset.mem_singleton, hne,
      (productRight (k + 1) (k + 1)).injective.eq_iff,
      false_or, productTuple_right]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [Fin.castSucc_ne_last]

theorem residueJacobian_det_of_head {K : Type*} [Field K] [Infinite K] {k : ℕ}
    {C : Set (Fin ((k + 1) + (k + 1)) → K)} {D : Set (Fin (k + k) → K)}
    (hproj : ∀ z ∈ C, z ∘ headPairIndex k ∈ D)
    (hline : ∀ a : K, a ≠ 0 →
      productTuple (Fin.snoc (fun _ : Fin k => 1) a) (Fin.snoc (fun _ : Fin k => 1) a) ∈ C)
    (L : (Fin (k + 1) → K) →ₗ[K] (Fin (k + 1) → K))
    (H : (Fin k → K) →ₗ[K] (Fin k → K))
    (hL : ∀ x y, IsPolynomialTangent C (fun _ => 1) (productTuple x y) ↔ y = L x)
    (hH : ∀ x y, IsPolynomialTangent D (fun _ => 1) (productTuple x y) ↔ y = H x) :
    (LinearMap.toMatrix' L).det = (LinearMap.toMatrix' H).det := by
  classical
  have hhead (x : Fin (k + 1) → K) : (L x) ∘ Fin.castSucc = H (x ∘ Fin.castSucc) := by
    have ht := polynomialTangent_projection (headPairIndex k) (headPairIndex_injective k)
      hproj ((hL x (L x)).mpr rfl)
    rw [productTuple_comp_headPairIndex] at ht
    exact (hH _ _).mp ht
  have htan := polynomialTangent_of_punctured_coordinate_line (lastPairIndices k) C (by
    intro a ha
    rw [lastPair_indicator]
    exact hline a ha)
  have hsingle : Fin.snoc (α := fun _ : Fin (k + 1) => K) (fun _ : Fin k => 0) 1 =
      Pi.single (Fin.last k) 1 := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Pi.single_apply, Fin.castSucc_ne_last]
  rw [lastPair_indicator, hsingle] at htan
  have hlast : L (Pi.single (Fin.last k) 1) = Pi.single (Fin.last k) 1 :=
    ((hL _ _).mp htan).symm
  have htop (i j : Fin k) :
      LinearMap.toMatrix' L i.castSucc j.castSucc = LinearMap.toMatrix' H i j := by
    rw [LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply]
    have h := congrFun (hhead (Pi.single j.castSucc 1)) i
    have he : (Pi.single j.castSucc (1 : K)) ∘ Fin.castSucc = Pi.single j 1 := by
      funext l
      simp only [Function.comp_apply, Pi.single_apply, Fin.castSucc_inj]
    simpa only [Function.comp_apply, he] using h
  rw [Matrix.det_succ_column _ (Fin.last k), Finset.sum_eq_single (Fin.last k)]
  · have hminor : (LinearMap.toMatrix' L).submatrix (Fin.last k).succAbove (Fin.last k).succAbove =
        LinearMap.toMatrix' H := by
      ext i j
      simpa only [Matrix.submatrix_apply, Fin.succAbove_last] using htop i j
    rw [hminor, LinearMap.toMatrix'_apply, hlast]
    have hsign : (-1 : K) ^ (k + k) = 1 := by
      rw [← two_mul, pow_mul]
      simp
    simp only [Pi.single_eq_same, Fin.val_last, hsign, one_mul, mul_one]
  · intro i _ hi
    rw [LinearMap.toMatrix'_apply, hlast, Pi.single_eq_of_ne hi, mul_zero, zero_mul]
  · simp

end IntegrationInACVF.Section7
