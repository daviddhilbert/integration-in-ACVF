import IntegrationSection4.RadiusPreparationGeometry
import Section3.RootFreeConstancy

/-! A definable unary VF set with no open ball is finite. The proof uses
the predecessor's actual finite polynomial obstacle set. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF
open GammaRadiusAtomicity

namespace IntegrationInACVF.Section4.EmptyInteriorFinite

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem finite_of_no_open (S U : Set M) (hU : DefinableAt S .vf U)
    (hNo : ∀ D : Set M, PaperBalls.IsOpenBall D → D ⊆ U → False) : U.Finite := by
  let v := Values.presentationValuation (M := M)
  have hv := Values.presentation_compatible (M := M)
  obtain ⟨Q,hQ,_,hConst⟩ := finite_definable_obstacles v hv S U hU
  apply (Q.finite_toSet.image Subtype.val).subset
  intro x hx
  by_contra hxQ
  let X : VFType (M := M) := ⟨x,hU.2 hx⟩
  have hcx (c : VFType (M := M)) (hc : c ∈ Q) : c ≠ X := by
    intro he
    exact hxQ ⟨c,hc,congrArg Subtype.val he⟩
  let F := Q.image (fun c => v (c-X))
  have hF : F.Nonempty := hQ.image _
  let ρ := F.min' hF
  obtain ⟨c,hc,hcv⟩ := Finset.mem_image.mp (F.min'_mem hF)
  change v (c-X) = ρ at hcv
  have hρ0 : ρ ≠ 0 := fun hz =>
    ((map_ne_zero v).mpr (sub_ne_zero.mpr (hcx c hc))) (hcv.trans hz)
  have hρle (z : VFType (M := M)) (hz : z ∈ Q) : ρ ≤ v (z-X) :=
    F.min'_le _ (Finset.mem_image.mpr ⟨z,hz,rfl⟩)
  let r := c-X
  have hr0 : r ≠ 0 := sub_ne_zero.mpr (hcx c hc)
  have hγ0 : Values.vfValueHom r ≠ Values.infinity := by
    intro he
    have hz := (Values.vrv_eq_infinity_iff (CanonicalRV.encodedRv r)).mp he
    exact hr0 ((CanonicalRV.encodedRv_zero_iff r).mp hz)
  let γ : Values.Gamma (M := M) := ⟨Values.vfValueHom r,hγ0⟩
  let R : Balls.Radius (Values.presentationType (M := M)) := ↑(OrderDual.toDual ρ)
  have hMem (y : VFType (M := M)) : y.val ∈ gammaBall X γ true ↔ y ∈ Balls.openDisc v X R := by
    rw [GammaCosetGeometry.gammaBall_mem_valuation v hv X r γ rfl y]
    have hr : v r = ρ := hcv
    simp only [Balls.openDisc,R,OrderDual.ofDual_toDual,if_neg hρ0,Set.mem_setOf_eq,hr]
  have hAvoid : ∀ z ∈ Q, z ∉ Balls.openDisc v X R := by
    intro z hz hm
    have hl : v (z-X) < ρ := by
      simpa only [Balls.openDisc,R,OrderDual.ofDual_toDual,if_neg hρ0,Set.mem_setOf_eq] using hm
    exact not_lt_of_ge (hρle z hz) hl
  have hX : X ∈ Balls.openDisc v X R := Balls.centre_mem_openDisc v X R
  apply hNo (gammaBall X γ true) (Or.inr ⟨X,γ,rfl⟩)
  intro y hy
  let Y : VFType (M := M) := ⟨y,hy.1⟩
  exact (hConst X R hAvoid X hX Y ((hMem Y).mp hy)).mp hx

end IntegrationInACVF.Section4.EmptyInteriorFinite
