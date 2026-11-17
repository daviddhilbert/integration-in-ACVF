module

public import Integration7.GammaRVLabelIdentity

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Identity on full RV labels retains the original Gamma graph across
different real presentations of the same label set. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a : ℕ}

theorem gamma_equal_label_equivalence_graph
    (U V : Set (Fin a → RV (M := M)))
    (hU : GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ U})
    (e : U ≃ V) (he : ∀ u, (e u).val = u.val) :
    GammaGraphDefinable B (fun (p q : Point (M := M) 0 a) =>
      ∃ u : U, u.val = p.2 ∧ (e u).val = q.2) := by
  apply GammaGraphDefinable.congr (gamma_rv_restricted_label_identity B U hU)
  intro p q
  constructor
  · rintro ⟨hp,hpq⟩
    exact ⟨⟨p.2,hp⟩,rfl,(he ⟨p.2,hp⟩).trans hpq⟩
  · rintro ⟨u,hu,hq⟩
    have hp : p.2 ∈ U := hu ▸ u.property
    exact ⟨hp,hu.symm.trans ((he u).symm.trans hq)⟩

end IntegrationInACVF.Section7
