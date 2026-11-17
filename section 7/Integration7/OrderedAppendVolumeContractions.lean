module

public import Integration7.GammaHeadVolumeCommonComparison

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The positive selected-volume induction for actual ordered contraction
programs. Original selected coordinates come first, followed by the VF
head tags in contraction order. The retained density is transported at
every actual stage. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M}

def appendVolumeDegree : ℕ → ℕ → ℕ
  | 0,k => k
  | n+1,k => appendVolumeDegree n (k+1)

theorem append_volume_degree_eq (n k : ℕ) : appendVolumeDegree n k = k+n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => rw [appendVolumeDegree,ih];omega

def orderedAppendVolumeIndex {n a l : ℕ} {U : DefSet (M := M) S n a} {V : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S U V) {k : ℕ} (ρ : Fin (k+1) → Fin a) :
    Fin (appendVolumeDegree n k+1) → Fin l := by
  induction T generalizing k with
  | zero U => exact ρ
  | step T tail ih => exact ih (headAppendVolumeIndex T ρ)

def orderedAppendDensityIndex {n a l : ℕ} {U : DefSet (M := M) S n a} {V : DefSet (M := M) S 0 l}
    (T : OrderedContractionProgram S U V) (δ : Fin a) : Fin l := by
  induction T with
  | zero U => exact δ
  | step T tail ih => exact ih (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ))

set_option maxHeartbeats 2400000 in
theorem lemma_7_5_ordered_geometric {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hBC : B.real ⊆ (C.base : Set M)) :
    ∀ {n a b l r k : ℕ}
    (U : DefSet (M := M) (C.base : Set M) n a) (V : DefSet (M := M) (C.base : Set M) n b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (ρ : Fin (k+1) → Fin a) (τ : Fin (k+1) → Fin b) (δ : Fin a) (ε : Fin b)
    (hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero)
    (hε : ∀ p ∈ carrier V, (p.2 ε).val ≠ iRVZero)
    (hfinU : ∀ (x : Fin n → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {v : Fin a → RV (M := M) | (x,v) ∈ carrier U ∧ v ∘ ρ = t}.Finite)
    (hfinV : ∀ (x : Fin n → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {v : Fin b → RV (M := M) | (x,v) ∈ carrier V ∧ v ∘ τ = t}.Finite)
    (hCommon : ∀ x : Fin n → VF (M := M),
      (gammaSelectedVolumeSchema U hU ρ δ).commonByGammaGeometry
        (gammaSelectedVolumeSchema V hV τ ε) (fun j => (x j).val))
    {U₀ : DefSet (M := M) (C.base : Set M) 0 l} {V₀ : DefSet (M := M) (C.base : Set M) 0 r}
    (T : OrderedContractionProgram (C.base : Set M) U U₀)
    (E : OrderedContractionProgram (C.base : Set M) V V₀)
    (hT : GammaProgramDefinable B T) (hE : GammaProgramDefinable B E),
    ∀ x : Fin 0 → VF (M := M),
      (gammaSelectedVolumeSchema U₀ (gamma_program_final_set T hT) (orderedAppendVolumeIndex T ρ)
        (orderedAppendDensityIndex T δ)).commonByGammaGeometry
        (gammaSelectedVolumeSchema V₀ (gamma_program_final_set E hE) (orderedAppendVolumeIndex E τ)
          (orderedAppendDensityIndex E ε)) (fun j => (x j).val) := by
  intro n
  induction n with
  | zero =>
    intro a b l r k U V hU hV ρ τ δ ε hδ hε hfinU hfinV hCommon U₀ V₀ T E hT hE
    cases T
    cases E
    exact hCommon
  | succ n ih =>
    intro a b l r k U V hU hV ρ τ δ ε hδ hε hfinU hfinV hCommon U₀ V₀ T E hT hE
    cases T with
    | step T tail =>
      cases E with
      | step E etail =>
        exact ih T.contractedSet E.contractedSet
          (gamma_headImage T.target hT.2.1) (gamma_headImage E.target hE.2.1)
          (headAppendVolumeIndex T ρ) (headAppendVolumeIndex E τ)
          (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ))
          (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le E.special) ε))
          (head_retained_density_nonzero T δ hδ) (head_retained_density_nonzero E ε hε)
          (head_append_selected_fibres_finite hκ hs hreal T hT.1 hT.2.1 ρ hfinU)
          (head_append_selected_fibres_finite hκ hs hreal E hE.1 hE.2.1 τ hfinV)
          (fun x => gamma_head_volume_common_comparison hc C hκ hs h00 hreal hgamma γ hγ hγ1 hBC
            U V hU hV ρ τ δ ε hδ hε hfinU hfinV hCommon T E hT.1 hE.1 hT.2.1 hE.2.1 x)
          tail etail hT.2.2 hE.2.2

end IntegrationInACVF.Section7
