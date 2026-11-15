import Integration7.NativeCoordinateDensityVolumeObjects

/-! Finite selected-volume fibres pass through an actual surjective
pure RV map preserving the chosen tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {a b d : ℕ}

theorem native_selected_volume_finiteness_transfer
    {A : DefSet (M := M) S 0 a} {B : DefSet (M := M) S 0 b}
    (α : Fin d → Fin a) (β : Fin d → Fin b) (f : Map A B)
    (hf : Function.Surjective f) (hc : ∀ p, (f p).val.2 ∘ β = p.val.2 ∘ α)
    (hfin : ∀ t : Fin d → RV (M := M),
      {r : Fin a → RV (M := M) | (Fin.elim0,r) ∈ carrier A ∧ r ∘ α = t}.Finite)
    (t : Fin d → RV (M := M)) :
    {r : Fin b → RV (M := M) | (Fin.elim0,r) ∈ carrier B ∧ r ∘ β = t}.Finite := by
  classical
  let g : (Fin a → RV (M := M)) → (Fin b → RV (M := M)) := fun r =>
    if hr : (Fin.elim0,r) ∈ carrier A then (f ⟨(Fin.elim0,r),hr⟩).val.2 else fun _ => 0
  apply ((hfin t).image g).subset
  rintro r ⟨hr,hv⟩
  obtain ⟨p,hp⟩ := hf ⟨(Fin.elim0,r),hr⟩
  have hpoint : p.val = (Fin.elim0,p.val.2) := Prod.ext (funext fun i => i.elim0) rfl
  have hp0 : (Fin.elim0,p.val.2) ∈ carrier A := hpoint ▸ p.property
  have hp' : (⟨(Fin.elim0,p.val.2),hp0⟩ : A) = p := Subtype.ext hpoint.symm
  have hl : (f p).val.2 = r := congrArg (fun q : B => q.val.2) hp
  refine ⟨p.val.2,⟨hp0,?_⟩,?_⟩
  · exact (hc p).symm.trans ((congrArg (fun z => z ∘ β) hl).trans hv)
  · dsimp only [g]
    rw [dif_pos hp0,hp',hl]

end IntegrationInACVF.Section7
