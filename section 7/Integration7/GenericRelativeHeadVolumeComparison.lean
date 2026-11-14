import Integration7.RelativeHeadVolumeExceptionalFamilies
import Integration7.GenericCoordinateFibreDimension

/-! Global measure preservation compares the chosen head contractions over
every VF tuple independent over the original context. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a b : ℕ}

theorem gamma_relative_head_volume_comparison_at_generic_base {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hBC : B.real ⊆ (C.base : Set M))
    (U : DefSet (M := M) (C.base : Set M) (n+1) a) (V : DefSet (M := M) (C.base : Set M) (n+1) b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hfinU : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (hfinV : ∀ x : Fin (n+1) → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier V}.Finite)
    (f : Map U V) (hf : Function.Bijective f) (hfΓ : GammaGraphDefinable B (pointMapGraph f))
    (hi : UnaryRelative f 0)
    (ω : VolumeForm (rawSpecialSet hc U)) (π : VolumeForm (rawSpecialSet hc V))
    (δ : Fin a) (ε : Fin b)
    (hω : ∀ q, ω.value q = q.val.2 δ) (hπ : ∀ q, π.value q = q.val.2 ε)
    (hm : PreservesVFVolume ω π (rawSpecialMap hc f))
    (T : HeadPreparation U) (E : HeadPreparation V)
    (hT : GammaGraphDefinable B (pointMapGraph T.map)) (hE : GammaGraphDefinable B (pointMapGraph E.map))
    (hTarget : GammaSetDefinable B (carrier T.target)) (hETarget : GammaSetDefinable B (carrier E.target))
    (x : Fin n → VF (M := M))
    (hx : AlgebraicIndependent (vfParameterField (C.base : Set M)) x) :
    (gammaSelectedVolumeSchema (k := 0) T.contractedSet (gamma_headImage T.target hTarget)
          (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a))
          (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ))).commonByGammaGeometry
        (gammaSelectedVolumeSchema (k := 0) E.contractedSet (gamma_headImage E.target hETarget)
          (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b))
          (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le E.special) ε))) (fun j => (x j).val) := by
  obtain ⟨D,_,hD,hCompare⟩ := gamma_relative_head_comparison_with_global_exception
    hc C hκ hs hreal hgamma γ hγ hγ1 hBC U V hU hV hfinU hfinV f hf hfΓ hi
    ω π δ ε hω hπ hm T E hT hE hTarget hETarget
  exact hCompare x (generic_head_coordinate_fibre_small hc C.uncountable.le C.saturated C.small D hD x hx)

end IntegrationInACVF.Section7
