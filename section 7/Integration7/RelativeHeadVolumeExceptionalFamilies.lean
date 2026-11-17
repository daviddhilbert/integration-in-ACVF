module

public import Integration7.RelativeHeadVolumeComparison

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A single witnessed global exception controls all frozen head
comparisons. Every fibre with a VF-small intersection with that exception
has actual original-Gamma common head-volume blowups. -/

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

theorem gamma_relative_head_comparison_with_global_exception {κ : Cardinal}
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
    (hTarget : GammaSetDefinable B (carrier T.target)) (hETarget : GammaSetDefinable B (carrier E.target)) :
    ∃ D : SpecialTransformations.DefinableGeometry.DefSet (rawMixedSpace (M := M) (n+1) a) (C.base : Set M),
      D.carrier ⊆ (rawSpecialSet hc U).carrier ∧
      vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1) D < n+1 ∧
      ∀ x : Fin n → VF (M := M),
        vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1)
          (rawSpecialSet hc (coordinateFibre (nativeMixedVolumeDomain hc D) 0 (headFrozenTuple x))) < 1 →
        (gammaSelectedVolumeSchema (k := 0) T.contractedSet (gamma_headImage T.target hTarget)
          (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a))
          (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ))).commonByGammaGeometry
        (gammaSelectedVolumeSchema (k := 0) E.contractedSet (gamma_headImage E.target hETarget)
          (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b))
          (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le E.special) ε))) (fun j => (x j).val) := by
  obtain ⟨D,hDU,hdim,hMeasure⟩ := hm
  refine ⟨D,hDU,hdim,fun x hx => ?_⟩
  exact gamma_relative_head_volume_comparison hc C hκ hs hreal hgamma γ hγ hγ1 hBC
    U V hU hV hfinU hfinV f hf hfΓ hi ω π δ ε hω hπ T E hT hE hTarget hETarget x
    (relative_volume_on_fibre_of_small_exception hc f 0 hi ω π δ ε hω hπ D hMeasure (headFrozenTuple x) hx)

end IntegrationInACVF.Section7
