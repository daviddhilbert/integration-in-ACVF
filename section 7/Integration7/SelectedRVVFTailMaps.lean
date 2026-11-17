module

public import Integration7.SelectedRVVFTailLifts
public import Section4.VFAppend

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A map retaining selected RV labels acts on their VF realizations
while fixing every added VF coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a b d : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n a) S} {B : DefSet (rawMixedSpace (M := M) n b) S}

def selectedRVVFTailMap (f : Map A B) (ρ : Fin d → Fin a) (σ : Fin d → Fin b)
    (hLabels : ∀ p : A, (f p).val.2 ∘ σ = p.val.2 ∘ ρ) :
    Map (selectedRVVFTailLift A ρ) (selectedRVVFTailLift B σ) := by
  let H := selectedRVVFTailLift A ρ
  let F := f.comp (selectedRVVFTailProjection A ρ)
  let x := (Map.fst (rawVFSpace n) (rawRVSpace b) S B).comp F
  let y := (Map.fst (rawVFSpace d) (rawRVSpace a) S
    (DefSet.univ (rawMixedSpace d a) S)).comp (vfSelect (Fin.natAdd n) H)
  let z := (vfAppendMap S n d).comp (x.pair y).toUniv
  let r := (Map.snd (rawVFSpace n) (rawRVSpace b) S B).comp F
  let g := (z.pair r).toUniv
  refine g.corestrict ?_
  intro p
  apply (mem_selected_rv_vf_tail_lift B σ (g p).val).mpr
  have hx : ((g p).val.1 ∘ Fin.castAdd d) = (F p).val.1 := funext (Fin.append_left _ _)
  have hy : ((g p).val.1 ∘ Fin.natAdd n) = p.val.1 ∘ Fin.natAdd n := funext (Fin.append_right _ _)
  constructor
  · change ((g p).val.1 ∘ Fin.castAdd d,(F p).val.2) ∈ B.carrier
    rw [hx]
    exact (F p).property
  · change tupleRV ((g p).val.1 ∘ Fin.natAdd n) = (F p).val.2 ∘ σ
    rw [hy]
    change tupleRV (p.val.1 ∘ Fin.natAdd n) =
      (f (selectedRVVFTailProjection A ρ p)).val.2 ∘ σ
    rw [hLabels]
    exact ((mem_selected_rv_vf_tail_lift A ρ p.val).mp p.property).2

theorem selected_rv_vf_tail_map_value (f : Map A B) (ρ : Fin d → Fin a) (σ : Fin d → Fin b)
    (hLabels : ∀ p : A, (f p).val.2 ∘ σ = p.val.2 ∘ ρ) (p : selectedRVVFTailLift A ρ) :
    (selectedRVVFTailMap f ρ σ hLabels p).val =
      (Fin.append (f (selectedRVVFTailProjection A ρ p)).val.1 (p.val.1 ∘ Fin.natAdd n),
        (f (selectedRVVFTailProjection A ρ p)).val.2) := rfl

theorem selected_rv_vf_tail_map_projection (f : Map A B) (ρ : Fin d → Fin a) (σ : Fin d → Fin b)
    (hLabels : ∀ p : A, (f p).val.2 ∘ σ = p.val.2 ∘ ρ) (p : selectedRVVFTailLift A ρ) :
    selectedRVVFTailProjection B σ (selectedRVVFTailMap f ρ σ hLabels p) =
      f (selectedRVVFTailProjection A ρ p) := by
  apply Subtype.ext
  exact Prod.ext (funext (Fin.append_left _ _)) rfl

theorem selected_rv_vf_tail_map_tail (f : Map A B) (ρ : Fin d → Fin a) (σ : Fin d → Fin b)
    (hLabels : ∀ p : A, (f p).val.2 ∘ σ = p.val.2 ∘ ρ) (p : selectedRVVFTailLift A ρ) :
    (selectedRVVFTailMap f ρ σ hLabels p).val.1 ∘ Fin.natAdd n = p.val.1 ∘ Fin.natAdd n :=
  funext (Fin.append_right _ _)

theorem selected_rv_vf_tail_ext (ρ : Fin d → Fin a) {p q : selectedRVVFTailLift A ρ}
    (hProj : selectedRVVFTailProjection A ρ p = selectedRVVFTailProjection A ρ q)
    (hTail : p.val.1 ∘ Fin.natAdd n = q.val.1 ∘ Fin.natAdd n) : p = q := by
  have hv := congrArg (fun r : A => r.val) hProj
  have hx := congrArg Prod.fst hv
  have hr := congrArg Prod.snd hv
  apply Subtype.ext
  refine Prod.ext ?_ hr
  funext i
  exact Fin.addCases (fun j => congrFun hx j) (fun j => congrFun hTail j) i

theorem selected_rv_vf_tail_map_bijective (f : Map A B) (hf : Function.Bijective f)
    (ρ : Fin d → Fin a) (σ : Fin d → Fin b)
    (hLabels : ∀ p : A, (f p).val.2 ∘ σ = p.val.2 ∘ ρ) :
    Function.Bijective (selectedRVVFTailMap f ρ σ hLabels) := by
  have hInv (q : B) : (f.inverse hf q).val.2 ∘ ρ = q.val.2 ∘ σ := by
    have h := hLabels (f.inverse hf q)
    rw [Map.apply_inverse] at h
    exact h.symm
  let g := selectedRVVFTailMap (f.inverse hf) σ ρ hInv
  constructor
  · intro p q he
    apply selected_rv_vf_tail_ext ρ
    · apply hf.1
      rw [← selected_rv_vf_tail_map_projection f ρ σ hLabels p,
        ← selected_rv_vf_tail_map_projection f ρ σ hLabels q,he]
    · rw [← selected_rv_vf_tail_map_tail f ρ σ hLabels p,
        ← selected_rv_vf_tail_map_tail f ρ σ hLabels q,he]
  · intro q
    refine ⟨g q,?_⟩
    apply selected_rv_vf_tail_ext σ
    · rw [selected_rv_vf_tail_map_projection,selected_rv_vf_tail_map_projection,Map.apply_inverse]
    · rw [selected_rv_vf_tail_map_tail,selected_rv_vf_tail_map_tail]

end IntegrationInACVF.Section7
