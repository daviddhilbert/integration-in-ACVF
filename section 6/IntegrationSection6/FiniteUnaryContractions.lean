import IntegrationSection6.FiniteStandardContractions
import IntegrationSection6.FiniteGammaIsoRealization

/-! The one-VF-coordinate case of contraction invariance, entirely in RV[1].
The higher-dimensional relative-fibre gluing is a separate6.14 obligation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {m l : ℕ}

theorem corollary_6_15_unary {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (hBS : B.real ⊆ S)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    {A : SpecialTransformations.Section5.DefSet (M := M) S 1 m}
    {D : SpecialTransformations.Section5.DefSet (M := M) S 1 l}
    (hA : GammaSetDefinable B (carrier A)) (hD : GammaSetDefinable B (carrier D))
    (hAF : ∀ x : Fin 1 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (hDF : ∀ x : Fin 1 → VF (M := M), {r : Fin l → RV (M := M) | (x,r) ∈ carrier D}.Finite)
    (e : GammaIso B (carrier A) (carrier D))
    {σ τ : Equiv.Perm (Fin 1)} (C : StandardContraction A σ) (E : StandardContraction D τ)
    (hC : GammaProgramDefinable B C.program) (hE : GammaProgramDefinable B E.program) :
    GammaIsp hκ hs h00 hsmall 
      (gammaFiniteContraction hκ hs hsmall hBS hA hAF C hC)
      (gammaFiniteContraction hκ hs hsmall hBS hD hDF E hE) := by
  let L := gammaLogicInput B
  let eC := C.gammaNormalizedLiftIso hBS hA hC
  let eE := E.gammaNormalizedLiftIso hBS hD hE
  exact corollary_6_11_gamma hκ hs h00 hsmall  δ hδ hδ1 FBase _ _
    (((eC.symm L).trans L e).trans L eE)

end IntegrationInACVF.Section6.FiniteRV
