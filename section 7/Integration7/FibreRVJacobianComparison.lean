import Integration7.FibreTangentDeterminant

/-! A defined full RV Jacobian of a correspondence fixing its head
agrees with the defined Jacobian on any fixed-head fibre through it. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4.ResiduePurity
open SpecialTransformations.Section7 SpecialTransformations.Section9
open scoped BigOperators

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m : ℕ}
local notation "RV" => CanonicalRV.RVSort M

theorem rvJacobian_eq_fixed_head_fibre
    {C : Set (Fin ((n+m)+(n+m)) → RV)} {D : Set (Fin (m+m) → RV)}
    (hHead : ∀ z ∈ C, ∀ i : Fin n,
      z (productLeft (n+m) (n+m) (Fin.castAdd m i)) =
        z (productRight (n+m) (n+m) (Fin.castAdd m i)))
    (t : Fin n → RV) (u v : Fin m → RV)
    (hFibre : ∀ z ∈ D, insertHeadPair t t z ∈ C) {ω J : RV}
    (hFull : IsRVJacobianAt C (Fin.append t u) (Fin.append t v) ω)
    (hRow : IsRVJacobianAt D u v J) : ω = J := by
  obtain ⟨_,ht,_,L,hL,_,hω⟩ := hFull
  obtain ⟨_,_,_,G,hG,_,hJ⟩ := hRow
  have hT (i : Fin n) : t i ≠ 0 := by simpa only [Fin.append_left] using ht (Fin.castAdd m i)
  have hHead' : ∀ z ∈ normalizedCorrespondence C (Fin.append t u) (Fin.append t v),
      ∀ i : Fin n, z (productLeft (n+m) (n+m) (Fin.castAdd m i)) =
        z (productRight (n+m) (n+m) (Fin.castAdd m i)) := by
    intro z hz i
    apply residueRV_injective
    apply mul_left_cancel₀ (hT i)
    have h := hHead _ hz.1 i
    simpa only [residueScale,productTuple_left,productTuple_right,Fin.append_left] using h
  have hFibre' : ∀ z ∈ normalizedCorrespondence D u v,
      insertHeadPair (fun _ : Fin n => (1 : ModelResidue M)) (fun _ => 1) z ∈
        normalizedCorrespondence C (Fin.append t u) (Fin.append t v) := by
    intro z hz
    have he : residueScale (productTuple (Fin.append t u) (Fin.append t v))
        (insertHeadPair (fun _ : Fin n => (1 : ModelResidue M)) (fun _ => 1) z) =
        insertHeadPair t t (residueScale (productTuple u v) z) := by
      apply productTuple_ext
      · intro i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
          simp only [residueScale,insertHeadPair,productTuple_left,Fin.append_left,Fin.append_right,
            Function.comp_apply,residueRV_one,mul_one]
      · intro i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
          simp only [residueScale,insertHeadPair,productTuple_right,Fin.append_left,Fin.append_right,
            Function.comp_apply,residueRV_one,mul_one]
    refine ⟨he.symm ▸ hFibre _ hz.1,?_⟩
    intro i
    obtain ⟨s,rfl⟩ := finSumFinEquiv.surjective i
    cases s with
    | inl i =>
      change insertHeadPair (fun _ : Fin n => (1 : ModelResidue M)) (fun _ => 1) z
        (productLeft (n+m) (n+m) i) ≠ 0
      simp only [insertHeadPair,productTuple_left]
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left] using (one_ne_zero : (1 : ModelResidue M) ≠ 0)
      · simpa only [Fin.append_right,Function.comp_apply] using hz.2 (productLeft m m i)
    | inr i =>
      change insertHeadPair (fun _ : Fin n => (1 : ModelResidue M)) (fun _ => 1) z
        (productRight (n+m) (n+m) i) ≠ 0
      simp only [insertHeadPair,productTuple_right]
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left] using (one_ne_zero : (1 : ModelResidue M) ≠ 0)
      · simpa only [Fin.append_right,Function.comp_apply] using hz.2 (productRight m m i)
  have hd := residueJacobian_det_of_fixed_head_fibre hHead' hFibre' L G hL hG
  rw [hω,hJ,hd]
  have hprod : (∏ i, t i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hT i)
  simp only [Fin.prod_univ_add,Fin.append_left,Fin.append_right,mul_div_mul_left _ _ hprod]

end IntegrationInACVF.Section7
