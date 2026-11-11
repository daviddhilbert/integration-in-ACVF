import IntegrationSection3ACVF.GammaSpecialization
import IntegrationSection3ACVF.AtomicPolynomialRoots
import IntegrationSection3ACVF.GammaCosetGeometry
import Section3.MixedRootFree

/-! RV-profile constancy on balls inside a possibly undefinable complete
type, over real/Gamma bases. The root-free argument reuses the pinned MIT
Section3/MixedRootFree proof and its unchanged-coefficient-field support.
This file does not assert the extension to old ball parameters. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open SpecialTransformations.Section3.MixedPolynomialSyntax

namespace IntegrationInACVF.Section3ACVF.CompleteTypeRVProfiles

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m : ℕ}

theorem presentation (B : FullBaseAtomicity.Base (M := M))
    (hOnly : ∀ i ∈ B.imaginary, ∃ γ : Values.Gamma (M := M), i = Sum.inr γ)
    (R : Set (Fin (m+1) → M)) (hR : FullBaseAtomicity.OverBase B R) :
    ∃ T : Set M, T.Finite ∧ ∃ p : Parameters (B.real ∪ T),
      ∃ ψ : LRV.BoundedFormula (Fin p.length) (m+1),
        ψ.IsQF ∧ WellSorted p.sorts contextSort ψ ∧
        (∀ i (hi : iVF (p.values i)),
          (⟨p.values i,hi⟩ : VFType (M := M)) ∈ vfParameterField B.real) ∧
        ∀ (x : VFType (M := M)) (ys : Fin m → M), (∀ j, iRV (ys j)) →
          (ψ.Realize p.values (Fin.cons x.val ys) ↔ Fin.cons x.val ys ∈ R) := by
  obtain ⟨T,hT,hdef,hfield⟩ := GammaSpecialization.specialize_preserving_field B hOnly hR
  let S := B.real ∪ T
  let D : Set (Fin (m+1) → M) := {z | (∀ i, sortEval (contextSort i) (z i)) ∧ z ∈ R}
  have hguard : @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) (Fin (m+1))
      {z | ∀ i, sortEval (contextSort i) (z i)} := by
    have hd (j : Fin (m+1)) :=
      ((@definableAt_iff_normalized_raw M sM hM S (contextSort j) _).mp
        (@definableAt_sort M sM S (contextSort j))).1
    letI := @CanonicalStructure.normalize M sM
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun j => (hd j).preimage_comp (fun _ : Fin 1 => j))
  have hD : DefinableOver S contextSort D := by
    apply (definableOver_iff_normalized_raw S contextSort D).mpr
    have hn : @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) (Fin (m+1)) D := by
      letI := @CanonicalStructure.normalize M sM
      exact hguard.inter hdef
    exact ⟨hn,fun _ h => h.1⟩
  obtain ⟨p,ψ,hqf,hws,hψ⟩ := hD.quantifier_free hM
  have hp (i : Fin p.length) (hi : iVF (p.values i)) :
      (⟨p.values i,hi⟩ : VFType (M := M)) ∈ vfParameterField B.real := by
    rw [← hfield]
    exact Subfield.subset_closure (p.mem_base i)
  refine ⟨T,hT,p,ψ,hqf,hws,hp,?_⟩
  intro x ys hys
  have hsort : ∀ i, sortEval (contextSort i) ((Fin.cons x.val ys : Fin (m+1) → M) i) := by
    intro i
    cases i using Fin.cases with
    | zero => exact x.property
    | succ j => exact hys j
  have hm : Fin.cons x.val ys ∈ D ↔ Fin.cons x.val ys ∈ R := and_iff_right hsort
  rw [hψ] at hm
  exact (and_iff_right hsort).symm.trans hm

theorem constant_on_open_ball (B : FullBaseAtomicity.Base (M := M))
    (hOnly : ∀ i ∈ B.imaginary, ∃ γ : Values.Gamma (M := M), i = Sum.inr γ)
    {A : Set M} (hA : FullBallCoset.CompleteType B A) (hinf : A.Infinite)
    (a : VFType (M := M)) (α : Values.Gamma (M := M)) (hsub : gammaBall a α true ⊆ A)
    (R : Set (Fin (m+1) → M)) (hR : FullBaseAtomicity.OverBase B R)
    (x y : VFType (M := M)) (hx : x.val ∈ gammaBall a α true) (hy : y.val ∈ gammaBall a α true)
    (ys : Fin m → M) (hys : ∀ j, iRV (ys j)) :
    Fin.cons x.val ys ∈ R ↔ Fin.cons y.val ys ∈ R := by
  obtain ⟨T,_,p,ψ,hqf,hws,hp,hψ⟩ := presentation B hOnly R hR
  let E := vfParameterField (M := M) B.real
  let F := PolynomialObstacles.obstacles E (MixedPolynomialSupport.formula p E hp ψ)
  let Z : Set M := Subtype.val '' (F : Set (VFType (M := M)))
  have hZ : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ Z} :=
    FullBaseAtomicity.OverBase.of_real
      (((@definableAt_iff_normalized_raw M sM hM B.real .vf Z).mp
        (PolynomialObstacles.obstacles_definable B.real E
          (vfParameterField_le_definableClosureField B.real) _)).1)
  have hdis : Disjoint A Z := by
    rcases hA Z hZ with hAll | hDis
    · exact (hinf ((F.finite_toSet.image Subtype.val).subset hAll)).elim
    · exact hDis
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative α
  have hrNZ : r ≠ 0 := by
    intro hz
    have hi : Values.vfValueHom r = Values.infinity := by
      rw [hz,map_zero]
      exact Values.infinity_eq_zero.symm
    exact α.property (hr.symm.trans hi)
  have hvr : v r ≠ 0 := v.ne_zero_iff.mpr hrNZ
  let ρ : Balls.Radius Γ := ↑(OrderDual.toDual (v r))
  have hm (u : VFType (M := M)) : u.val ∈ gammaBall a α true ↔ u ∈ Balls.openDisc v a ρ :=
    (GammaCosetGeometry.gammaBall_mem_valuation v hv a r α hr u).trans
      (by simp [ρ,Balls.openDisc,hvr])
  have hAvoid (c : VFType (M := M)) (hc : c ∈ F) : c ∉ Balls.openDisc v a ρ := by
    intro hcB
    exact Set.disjoint_left.mp hdis (hsub ((hm c).mpr hcB)) ⟨c,hc,rfl⟩
  exact (hψ x ys hys).symm.trans
    ((mixed_qf_rootFree_constant v hv (B.real ∪ T) p E hp ψ hqf hws a ρ hAvoid x y
      ((hm x).mp hx) ((hm y).mp hy) ys hys).trans (hψ y ys hys))

end IntegrationInACVF.Section3ACVF.CompleteTypeRVProfiles
