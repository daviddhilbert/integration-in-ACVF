import IntegrationSection6.FiniteGammaProducts
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

theorem gammaProductAt_volume_pair (U : GammaObjectAt B S k) (V : GammaObjectAt B S l)
    (u : rvObjectDomain U.object.obj) (v : rvObjectDomain V.object.obj) :
    gammaVolumeValue (gammaProductAt U V).toGamma.toGammaRVObject
      (@rvPackPair M N S _ _ (rvObjectDomain U.object.obj) (rvObjectDomain V.object.obj) u v) =
        Fin.append (gammaVolumeValue U.toGamma.toGammaRVObject u) (gammaVolumeValue V.toGamma.toGammaRVObject v) :=
  @rvProductObject_value_pair M N S k l U.object.obj V.object.obj u v

theorem gammaAdmissible_product {U : GammaObjectAt B S k} {i : Fin k}
    (h : GammaAdmissible U.toGamma.toGammaRVObject i) (V : GammaObjectAt B S l) :
    GammaAdmissible (gammaProductAt U V).toGamma.toGammaRVObject (Fin.castAdd l i) where
  nonzero a := by
    obtain ⟨u,v,rfl⟩ := @exists_rvPackPair M N S _ _ (rvObjectDomain U.object.obj) (rvObjectDomain V.object.obj) a
    simpa only [gammaProductAt_volume_pair,Fin.append_left] using h.nonzero u
  algebraic a := by
    obtain ⟨u,v,rfl⟩ := @exists_rvPackPair M N S _ _ (rvObjectDomain U.object.obj) (rvObjectDomain V.object.obj) a
    rw [gammaProductAt_volume_pair]
    simp only [Fin.append_left]
    apply (h.algebraic u).mono (C := ⟨coordinateBase B.real (Fin.castAdd l i)
      (Fin.append (gammaVolumeValue U.toGamma.toGammaRVObject u) (gammaVolumeValue V.toGamma.toGammaRVObject v)),B.gamma⟩)
      ?_ (Set.Subset.refl _)
    rintro x (hx | ⟨j,hj,rfl⟩)
    · exact Or.inl hx
    · refine Or.inr ⟨Fin.castAdd l j,?_,?_⟩
      · exact fun he => hj (Fin.castAdd_injective k l he)
      · simp only [Fin.append_left]

end IntegrationInACVF.Section6.FiniteRV
