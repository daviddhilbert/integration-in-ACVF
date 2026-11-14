import Integration7.RelativeHeadVolumeComparison
import Integration7.OrderedAppendVolumeContractions

/-! A relatively unary comparison whose actual frozen fibres preserve
volume extends through every remaining chosen contraction. The first
head tag provides the positive selected degree required by Lemma 7.5. -/

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
variable {B : Base (M := M)} {n a b l r : ℕ}

set_option maxHeartbeats 2400000 in
theorem ordered_relative_volume_comparison_of_fibrewise_measure {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hBC : B.real ⊆ (C.base : Set M))
    (U : DefSet (M := M) (C.base : Set M) (n+1) a) (V : DefSet (M := M) (C.base : Set M) (n+1) b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hfinU : ∀ x : Fin (n+1) → VF (M := M), {s : Fin a → RV (M := M) | (x,s) ∈ carrier U}.Finite)
    (hfinV : ∀ x : Fin (n+1) → VF (M := M), {s : Fin b → RV (M := M) | (x,s) ∈ carrier V}.Finite)
    (f : Map U V) (hf : Function.Bijective f) (hfΓ : GammaGraphDefinable B (pointMapGraph f))
    (hi : UnaryRelative f 0)
    (ω : VolumeForm (rawSpecialSet hc U)) (π : VolumeForm (rawSpecialSet hc V))
    (δ : Fin a) (ε : Fin b)
    (hω : ∀ q, ω.value q = q.val.2 δ) (hπ : ∀ q, π.value q = q.val.2 ε)
    (hm : ∀ x : Fin n → VF (M := M), PreservesVFVolume
      (coordinateFibreRetainedVolumeForm hc U ω δ hω 0 (headFrozenTuple x))
      (coordinateFibreRetainedVolumeForm hc V π ε hπ 0 (headFrozenTuple x))
      (rawSpecialMap hc (coordinateFibreMap f 0 hi (headFrozenTuple x))))
    (T : HeadPreparation U) (E : HeadPreparation V)
    (hT : GammaGraphDefinable B (pointMapGraph T.map)) (hE : GammaGraphDefinable B (pointMapGraph E.map))
    (hTarget : GammaSetDefinable B (carrier T.target)) (hETarget : GammaSetDefinable B (carrier E.target))
    {U₀ : DefSet (M := M) (C.base : Set M) 0 l} {V₀ : DefSet (M := M) (C.base : Set M) 0 r}
    (tail : OrderedContractionProgram (C.base : Set M) T.contractedSet U₀)
    (etail : OrderedContractionProgram (C.base : Set M) E.contractedSet V₀)
    (htail : GammaProgramDefinable B tail) (hetail : GammaProgramDefinable B etail) :
    ∀ x : Fin 0 → VF (M := M),
      (gammaSelectedVolumeSchema U₀ (gamma_program_final_set tail htail)
        (orderedAppendVolumeIndex (k := 0) tail (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)))
        (orderedAppendDensityIndex tail (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ)))).commonByGammaGeometry
      (gammaSelectedVolumeSchema V₀ (gamma_program_final_set etail hetail)
        (orderedAppendVolumeIndex (k := 0) etail (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b)))
        (orderedAppendDensityIndex etail (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le E.special) ε))))
      (fun j => (x j).val) := by
  have hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero := fun p hp =>
    (rv_nonzero_iff_raw _).mp (fun h => ω.nonzero ⟨p,hp⟩ ((hω ⟨p,hp⟩).trans h))
  have hε : ∀ p ∈ carrier V, (p.2 ε).val ≠ iRVZero := fun p hp =>
    (rv_nonzero_iff_raw _).mp (fun h => π.nonzero ⟨p,hp⟩ ((hπ ⟨p,hp⟩).trans h))
  have hfinU₀ (y : Fin (n+1) → VF (M := M)) (t : Fin 0 → RV (M := M)) :
      {s : Fin a → RV (M := M) | (y,s) ∈ carrier U ∧ s ∘ Fin.elim0 = t}.Finite :=
    (hfinU y).subset (fun _ h => h.1)
  have hfinV₀ (y : Fin (n+1) → VF (M := M)) (t : Fin 0 → RV (M := M)) :
      {s : Fin b → RV (M := M) | (y,s) ∈ carrier V ∧ s ∘ Fin.elim0 = t}.Finite :=
    (hfinV y).subset (fun _ h => h.1)
  exact lemma_7_5_ordered_geometric (k := 0) hc C hκ hs C.model00 hreal hgamma γ hγ hγ1 hBC
    T.contractedSet E.contractedSet (gamma_headImage T.target hTarget) (gamma_headImage E.target hETarget)
    (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b))
    (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ))
    (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le E.special) ε))
    (head_retained_density_nonzero T δ hδ) (head_retained_density_nonzero E ε hε)
    (head_selected_fibres_finite hκ hs hreal T hT hTarget Fin.elim0 hfinU₀)
    (head_selected_fibres_finite hκ hs hreal E hE hETarget Fin.elim0 hfinV₀)
    (fun x => gamma_relative_head_volume_comparison hc C hκ hs hreal hgamma γ hγ hγ1 hBC
      U V hU hV hfinU hfinV f hf hfΓ hi ω π δ ε hω hπ T E hT hE hTarget hETarget x (hm x))
    tail etail htail hetail

end IntegrationInACVF.Section7
