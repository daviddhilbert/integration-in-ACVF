import Integration7.TermContextGammaGraphs
import Integration7.VolumeSchemaRowSemantics
import Integration7.ElementaryBlowupConstruction
import IntegrationSection6.GammaAdmissibilityPromotion
import IntegrationSection6.GammaSortedSchemaRows

/-! Actual last-coordinate admissibility descends from the original
named term context, then supplies a finite first-order slice bound. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV)
open SpecialTransformations.Section7 (gammaVolumeValue)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

theorem RVVolumeSchemaRow.gammaAdmissibleInTermContext
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp} {z : Fin p → M}
    (PU : RVVolumeSchemaRow U F z)
    (hBase : (C.base : Set M) = (Substructure.closure LRV (B.real ∪ Set.range z) : Set M))
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ U.underlying.obj.arity (k+1)
      (F.object.rowDomain z) (F.object.rowVolume z)) (hAd : BlowupAdmissible U) :
    GammaAdmissible P.toGamma.toGammaRVObject (Fin.last k) := by
  constructor
  · intro u
    let t : Fin (k+1) → CanonicalRV.RVSort M := gammaVolumeValue P.toGamma.toGammaRVObject u
    have ht := ((P.graph_iff u.val t).mp ⟨u,rfl,rfl⟩).2
    obtain ⟨v,_,hv⟩ := (PU.volume_iff _ _).mp ht
    change (t (Fin.last k)).val ≠ iRVZero
    rw [← hv]
    exact (rv_nonzero_iff_raw _).mp (hAd.nonzero v)
  · intro u
    let t : Fin (k+1) → CanonicalRV.RVSort M := gammaVolumeValue P.toGamma.toGammaRVObject u
    have ht := ((P.graph_iff u.val t).mp ⟨u,rfl,rfl⟩).2
    obtain ⟨v,_,hv⟩ := (PU.volume_iff _ _).mp ht
    change AlgebraicAtBase
      ⟨coordinateBase (B.real ∪ Set.range z) (Fin.last k) t,B.gamma⟩
      .rv (t (Fin.last k)).val
    rw [← hv]
    obtain ⟨A,hA,hAf,hAv⟩ := coordinate_algebraic_termContext hc C _ hBase
      (Fin.last k) (U.underlying.obj.value v) (hAd.algebraic v)
    exact ⟨A,real_definableAtBase _ .rv A hA,hAf,hAv⟩

theorem GammaRVVolumeSchema.exists_admissibility_bound {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    {a : ℕ} (F : GammaRVVolumeSchema B p a k sp) (z : Fin p → M) (hF : F.valid z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a (k+1)
      (F.object.rowDomain z) (F.object.rowVolume z))
    (hAd : GammaAdmissible P.toGamma.toGammaRVObject (Fin.last k)) :
    ∃ N : ℕ, (GammaFiniteAdmissibilitySchema.mk F.object (Fin.last k) N).valid z := by
  obtain ⟨N,hN⟩ := GammaAdmissible.uniform_label_slices
    (B := ⟨B.real ∪ Set.range z,B.gamma⟩) (U := P.toGamma.toGammaRVObject) (i := Fin.last k)
    hκ hs h00 (small_union_range hκ B.real hreal z) hgamma hAd
  have hImage (r : Fin (k+1) → M) :
      Fin.append z r ∈ tupleVolumeImage F.object.volume ↔ r ∈ gammaVolumeImage P.toGamma.toGammaRVObject :=
    (tupleVolumeImage_append_iff F.object.volume z r).trans
      ((exists_congr (fun x => F.object.raw_row_volume_presented z
        (fun _ _ h => hF.1.2.2.1 _ _ h) P x r)).trans
          (gammaRawObjectVolume_image_iff P.toGamma.toGammaRVObject r))
  refine ⟨N,hF.1,?_,?_⟩
  · intro r hr
    exact hAd.image_nonzero ((hImage r).mp hr)
  · intro t ht
    have he : {r | Fin.append z r ∈ tupleVolumeImage F.object.volume ∧ ∀ j, j ≠ Fin.last k → r j = t j} =
        {r | r ∈ gammaVolumeImage P.toGamma.toGammaRVObject ∧ ∀ j, j ≠ Fin.last k → r j = t j} :=
      Set.ext (fun r => and_congr (hImage r) Iff.rfl)
    change _ ∧ _
    rw [he]
    exact hN t ht

end IntegrationInACVF.Section7
