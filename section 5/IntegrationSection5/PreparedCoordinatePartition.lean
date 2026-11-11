import IntegrationSection5.UnaryCoordinateGeometry
import IntegrationSection5.GammaMembershipPreparation

/-! Actual special preparation of a finite coordinate-open partition.
No source-cell purity or desired open-image conclusion is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : GammaParameters.Base (M := M)} {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

theorem prepared_coordinate_partition {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk P.real < κ)
    (FBase : VFFieldBase P.real) (hPS : P.real ⊆ S)
    (f : Map A B) (hc : Contractible f)
    (hA : IsRVPullback (carrier A)) (hADef : GammaSetDefinable P (carrier A))
    {ι : Type} (D : ι → DefSet (M := M) S 1 m) (F : Finset ι)
    (hD : ∀ i ∈ F, GammaSetDefinable P (carrier (D i)))
    (hCover : ∀ a : A, ∃ i ∈ F, a.val ∈ carrier (D i))
    (hOpen : ∀ i ∈ F, CoordinateOpenToOpen.At (pointValues '' carrier (D i))
      (unaryTupleMap f) (.inl 0) (.inl 0)) :
    ∃ r : ℕ, ∃ A' : DefSet (M := M) S 1 r, ∃ T : SpecialBijection A A',
      GammaChainDefinable P T.chain ∧ IsRVPullback (carrier A') ∧
      Contractible (Map.comp f T.inverseMap) ∧ CellwiseOpenEquivalence (Map.comp f T.inverseMap) := by
  classical
  obtain ⟨r,A',T,hT,hA',hFlags⟩ :=
    gamma_prepare_finite_membership hs h00 hsmall FBase hPS A hA hADef D F hD
  let Q := F.image (fun i => pointValues '' carrier (D i))
  have hQ : ∀ W ∈ Q, CoordinateOpenToOpen.At W (unaryTupleMap f) (.inl 0) (.inl 0) := by
    intro W hW
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hW
    exact hOpen i hi
  have hPure : ∀ a : A', ∃ W ∈ Q, ∀ b : A', SameRV b.val a.val →
      pointValues (T.inverseMap b).val ∈ W := by
    intro a
    obtain ⟨i,hi,hai⟩ := hCover (T.inverseMap a)
    refine ⟨pointValues '' carrier (D i),Finset.mem_image.mpr ⟨i,hi,rfl⟩,?_⟩
    intro b hba
    have hflags := hFlags i hi b a hba
    have he := congrFun ((sameRV_iff _ _).mp hflags).2 0
    have hbi := (membershipMap_eq_iff A (D i) (T.inverseMap b) (T.inverseMap a)).mp he
    exact ⟨(T.inverseMap b).val,hbi.mpr hai,rfl⟩
  exact ⟨r,A',T,hT,hA',contractible_comp T.inverseMap f T.inverse_contractible hc,
    refined_coordinate_open_to_cellwise f T Q hQ hPure⟩

end IntegrationInACVF.Section5
