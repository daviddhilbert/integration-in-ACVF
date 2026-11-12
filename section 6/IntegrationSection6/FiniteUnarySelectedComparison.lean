import IntegrationSection6.FiniteSelectedContractionSlices
import IntegrationSection6.GammaVolumeSliceUniformity

/-! Unary contraction comparison with selected old RV volumes. The exact
relative-finiteness assumption permits infinite total old RV fibres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {m l e : ℕ}

theorem corollary_6_15_unary_selected {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ) (hBS : B.real ⊆ S)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    {A : SpecialTransformations.Section5.DefSet (M := M) S 1 m}
    {D : SpecialTransformations.Section5.DefSet (M := M) S 1 l}
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaSetDefinable B (carrier D))
    (ρ : Fin e → Fin m) (τ : Fin e → Fin l)
    (hAF : ∀ (x : Fin 1 → VF (M := M)) (t : Fin e → RV (M := M)),
      {r : Fin m → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (hDF : ∀ (x : Fin 1 → VF (M := M)) (t : Fin e → RV (M := M)),
      {r : Fin l → RV (M := M) | (x,r) ∈ carrier D ∧ r ∘ τ = t}.Finite)
    (f : GammaIso B (carrier A) (carrier D))
    (hLabels : ∀ a : A, (f.equiv a).val.2 ∘ τ = a.val.2 ∘ ρ)
    {σ υ : Equiv.Perm (Fin 1)} (C : StandardContraction A σ) (E : StandardContraction D υ)
    (hC : GammaProgramDefinable B C.program) (hE : GammaProgramDefinable B E.program) :
    GammaIsp hκ hs h00 hreal
      (gammaPrependSelectedContraction hκ hs hreal hBS hA ρ hAF C hC)
      (gammaPrependSelectedContraction hκ hs hreal hBS hD τ hDF E hE) := by
  apply gamma_volume_slice_unary_lift_uniformity hκ hs h00 hreal hgamma δ hδ hδ1 FBase
  intro t P Q
  let L := gammaLogicInput (⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩ : Base (M := M))
  let c := gammaSelectedContractionSliceLiftIso hκ hs hreal hBS hA ρ hAF C hC t P
  let d := gammaSelectedContractionSliceLiftIso hκ hs hreal hBS hD τ hDF E hE t Q
  let f' := gammaIsoNamedRVLabels f ρ τ hLabels t
  exact ⟨((c.symm L).trans L f').trans L d⟩

end IntegrationInACVF.Section6.FiniteRV
