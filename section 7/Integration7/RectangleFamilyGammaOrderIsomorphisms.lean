import Integration7.RectangleFamilyRawRetainedDensities
import IntegrationSection6.RawFiniteContractions

/-! The rectangle-family raw comparison is an actual isomorphism of
the original-Gamma finite RV objects, with exact coordinate identities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.IndependentRectangleFamilyPreparations
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ} {κ : Cardinal}
variable (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk G.real < κ)
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (hGC : G.real ⊆ (C.base : Set M))
variable {H : DefSet (M := M) (C.base : Set M) 2 m}
variable (hH : GammaSetDefinable G (carrier H))
variable (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier H}.Finite)
variable {hRect : RectangularRVFibres (carrier H)} (F : IndependentRectangleFamilyPreparations G H hRect)

def rawGammaOrderIso :
    GammaRVIso
      (FiniteRV.gammaRawFiniteContraction hκ hs hreal hGC hH hfin F.headContraction (F.head_contraction_gamma hH)).toGammaRVObject
      (FiniteRV.gammaRawFiniteContraction hκ hs hreal hGC hH hfin F.tailContraction (F.tail_contraction_gamma hH)).toGammaRVObject := by
  let f := nativeRawRVMapTransfer F.headOrderMap
  apply FiniteRV.gammaIsoOfFiniteEquiv _ _
    (Equiv.ofBijective f (native_raw_rv_map_transfer_bijective F.headOrderMap F.head_order_bijective))
  · apply GammaGraphDefinable.congr (F.raw_order_map_gamma hc)
    intro p q
    constructor
    · rintro ⟨u,hu,hq⟩
      exact ⟨⟨u.val,u.property⟩,hu,hq⟩
    · rintro ⟨u,hu,hq⟩
      exact ⟨⟨u.val,u.property⟩,hu,hq⟩
  · intro u
    exact congrArg (fun t : Fin 2 → RV (M := M) => rawWeight (fun j => (t j).val))
      (F.raw_order_map_volume hc ⟨u.val,u.property⟩).symm

theorem raw_gamma_order_coordinates :
    ∀ u, gammaVolumeValue
      (FiniteRV.gammaRawFiniteContraction hκ hs hreal hGC hH hfin F.tailContraction (F.tail_contraction_gamma hH)).toGammaRVObject
      ((F.rawGammaOrderIso hκ hs hreal hc C hGC hH hfin).equiv u) =
        gammaVolumeValue
          (FiniteRV.gammaRawFiniteContraction hκ hs hreal hGC hH hfin F.headContraction (F.head_contraction_gamma hH)).toGammaRVObject u :=
  fun u => F.raw_order_map_volume hc ⟨u.val,u.property⟩

theorem raw_gamma_order_retained_labels (i : Fin m) :
    ∀ u, ((F.rawGammaOrderIso hκ hs hreal hc C hGC hH hfin).equiv u).val
      (suffixIndex F.tailContraction.program.rvArity_le i) =
        u.val (suffixIndex F.headContraction.program.rvArity_le i) :=
  fun u => F.raw_order_retained_labels hc ⟨u.val,u.property⟩ i

end IntegrationInACVF.Section7.IndependentRectangleFamilyPreparations
