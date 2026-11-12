import IntegrationSection6.FiniteGammaProductAdmissibility
import IntegrationSection6.GammaAdmissibility

/-! Original-base admissibility survives an unrelated finite RV factor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k l : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem gammaAdmissible_product_left {U : GammaObjectAt B S k} {i : Fin k}
    (h : GammaAdmissible U.toGamma.toGammaRVObject i) (V : GammaObjectAt B S l) :
    GammaAdmissible (gammaProductAt V U).toGamma.toGammaRVObject (Fin.natAdd l i) where
  nonzero a := by
    obtain ⟨v,u,rfl⟩ := @exists_rvPackPair M N S _ _ (rvObjectDomain V.object.obj) (rvObjectDomain U.object.obj) a
    simpa only [gammaProductAt_volume_pair,Fin.append_right] using h.nonzero u
  algebraic a := by
    obtain ⟨v,u,rfl⟩ := @exists_rvPackPair M N S _ _ (rvObjectDomain V.object.obj) (rvObjectDomain U.object.obj) a
    rw [gammaProductAt_volume_pair]
    simp only [Fin.append_right]
    apply (h.algebraic u).mono (C := ⟨coordinateBase B.real (Fin.natAdd l i)
      (Fin.append (gammaVolumeValue V.toGamma.toGammaRVObject v) (gammaVolumeValue U.toGamma.toGammaRVObject u)),B.gamma⟩)
      ?_ (Set.Subset.refl _)
    rintro x (hx | ⟨j,hj,rfl⟩)
    · exact Or.inl hx
    · refine Or.inr ⟨Fin.natAdd l j,?_,?_⟩
      · intro he
        apply hj
        apply Fin.ext
        have hv := congrArg Fin.val he
        change l+j.val = l+i.val at hv
        omega
      · simp only [Fin.append_right]

end IntegrationInACVF.Section6.FiniteRV
