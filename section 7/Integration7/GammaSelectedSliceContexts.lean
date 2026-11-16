module

public import Integration7.GammaFiniteFamilyContexts
public import IntegrationSection6.GammaNamedRVFibres

@[expose] public section

/-! Selected RV-label slices have actual presentations inside genuine
small contexts. Internal real codes are finite; the Gamma base names only
the original parameters and selected RV tuple. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a k : ℕ}

theorem gamma_selected_slice_context
    (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (U : DefSet (M := M) (C.base : Set M) n a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a) (t : Fin k → RV (M := M)) :
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
      B.real ∪ Set.range (fun j => (t j).val) ⊆ (D.base : Set M) ∧
      ∃ L : DefSet (M := M) (D.base : Set M) n a,
        carrier L = carrier U ∩ {q | q.2 ∘ ρ = t} := by
  let E := Set.range (fun j => (t j).val)
  let Ct := finiteVolumeParameterContext C E (Set.finite_range _)
  have hCCt : (C.base : Set M) ⊆ (Ct.base : Set M) :=
    fun _ hx => finiteVolumeParameterContext_contains C E (Set.finite_range _) (Or.inl hx)
  let Bt : Base (M := M) := ⟨B.real ∪ E,B.gamma⟩
  have hBt : Bt.real ⊆ (Ct.base : Set M) := by
    rintro x (hx | hx)
    · exact hCCt (hBC hx)
    · exact finiteVolumeParameterContext_contains C E (Set.finite_range _) (Or.inr hx)
  let W : Set (Point (M := M) n a) := carrier U ∩ {q | q.2 ∘ ρ = t}
  have hW : GammaSetDefinable Bt W := (gammaLogicInput Bt).inter
    (hU.mono Set.subset_union_left (Set.Subset.refl _)) (gamma_named_rv_label_fibre ρ t)
  obtain ⟨D,hCtD,L,hL⟩ := gamma_finite_family_context Ct Bt hBt (fun _ : Fin 1 => W) (fun _ => hW)
  exact ⟨D,hCCt.trans hCtD,hBt.trans hCtD,L 0,hL 0⟩

theorem selected_slice_presentation_finite {S R : Set M}
    (U : DefSet (M := M) S n a) (L : DefSet (M := M) R n a)
    (ρ : Fin k → Fin a) (t : Fin k → RV (M := M))
    (hL : carrier L = carrier U ∩ {q | q.2 ∘ ρ = t})
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite) :
    ∀ x : Fin n → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier L}.Finite := by
  intro x
  convert hfin x t using 1
  ext r
  exact Set.ext_iff.mp hL (x,r)

end IntegrationInACVF.Section7
