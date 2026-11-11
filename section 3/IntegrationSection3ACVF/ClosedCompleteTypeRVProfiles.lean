import IntegrationSection3ACVF.CompleteTypeRVProfiles
import IntegrationSection3ACVF.BallKindPredicates

/-! Real/Gamma RV-profile constancy on an ordinary closed ball inside
a possibly undefinable complete type. Reuses the pinned checked
mixed_qf_rootFree_constant_closed with its actual coefficient-field scope. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open SpecialTransformations.Section3.MixedPolynomialSyntax

namespace IntegrationInACVF.Section3ACVF.ClosedCompleteTypeRVProfiles

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m : ℕ}

theorem constant_on_closed_ball (B : FullBaseAtomicity.Base (M := M))
    (hOnly : ∀ i ∈ B.imaginary, ∃ γ : Values.Gamma (M := M), i = Sum.inr γ)
    {A : Set M} (hA : FullBallCoset.CompleteType B A) (hinf : A.Infinite)
    (a : VFType (M := M)) (α : Values.Gamma (M := M)) (hsub : gammaBall a α false ⊆ A)
    (R : Set (Fin (m+1) → M)) (hR : FullBaseAtomicity.OverBase B R)
    (x y : VFType (M := M)) (hx : x.val ∈ gammaBall a α false) (hy : y.val ∈ gammaBall a α false)
    (ys : Fin m → M) (hys : ∀ j, iRV (ys j)) :
    Fin.cons x.val ys ∈ R ↔ Fin.cons y.val ys ∈ R := by
  obtain ⟨T,_,p,ψ,hqf,hws,hp,hψ⟩ := CompleteTypeRVProfiles.presentation B hOnly R hR
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
  have hm (u : VFType (M := M)) : u.val ∈ gammaBall a α false ↔ u ∈ Balls.closedDisc v a ρ :=
    (BallKindPredicates.gammaBall_mem_valuation_closed v hv a r α hr u).trans
      (by simp [ρ,Balls.closedDisc,hvr])
  have hAvoid (c : VFType (M := M)) (hc : c ∈ F) : c ∉ Balls.closedDisc v a ρ := by
    intro hcB
    exact Set.disjoint_left.mp hdis (hsub ((hm c).mpr hcB)) ⟨c,hc,rfl⟩
  exact (hψ x ys hys).symm.trans
    ((mixed_qf_rootFree_constant_closed v hv (B.real ∪ T) p E hp ψ hqf hws a ρ hAvoid x y
      ((hm x).mp hx) ((hm y).mp hy) ys hys).trans (hψ y ys hys))


end IntegrationInACVF.Section3ACVF.ClosedCompleteTypeRVProfiles
