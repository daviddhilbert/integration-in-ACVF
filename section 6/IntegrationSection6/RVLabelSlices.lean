import IntegrationSection6.GammaUnivPresentations
import IntegrationSection6.GammaNamedRVFibres
import IntegrationSection5.GammaOrderedContraction

/-! Actual mixed-set slices fixing selected RV labels. Internal real
presentations use the whole model; their Gamma base names only the fixed
RV tuple and the original parameters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m k : ℕ}

theorem rvLabelSlice_gamma (U : DefSet (M := M) Set.univ n m)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin m) (t : Fin k → RV (M := M)) :
    GammaSetDefinable ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
      (carrier U ∩ {q | q.2 ∘ ρ = t}) :=
  (gammaLogicInput _).inter (hU.mono Set.subset_union_left (Set.Subset.refl _)) (gamma_named_rv_label_fibre ρ t)

def rvLabelSlice (U : DefSet (M := M) Set.univ n m)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin m) (t : Fin k → RV (M := M)) :
    DefSet (M := M) Set.univ n m := gammaDefSetUniv (carrier U ∩ {q | q.2 ∘ ρ = t}) (rvLabelSlice_gamma U hU ρ t)

theorem rvLabelSlice_carrier (U : DefSet (M := M) Set.univ n m)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin m) (t : Fin k → RV (M := M)) :
    carrier (rvLabelSlice U hU ρ t) = carrier U ∩ {q | q.2 ∘ ρ = t} := rfl

theorem rvLabelSlice_finite (U : DefSet (M := M) Set.univ n m)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin m)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin m → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (t : Fin k → RV (M := M)) :
    ∀ x : Fin n → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier (rvLabelSlice U hU ρ t)}.Finite :=
  fun x => hfin x t

theorem headKey_selected_old_labels (q : Point (M := M) (n+1) m) (ρ : Fin k → Fin m) :
    (headKey q).2 ∘ (fun j => Fin.natAdd 1 (ρ j)) = q.2 ∘ ρ := by
  funext j
  change Fin.append (fun _ : Fin 1 => @rv M sM hM (vfAt q 0)) q.2 (Fin.natAdd 1 (ρ j)) = q.2 (ρ j)
  exact Fin.append_right _ _ _

theorem rvLabelSlice_headImage (U : DefSet (M := M) Set.univ (n+1) m)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin m) (t : Fin k → RV (M := M)) :
    headImage (rvLabelSlice U hU ρ t) =
      rvLabelSlice (headImage U) (gamma_headImage U hU) (fun j => Fin.natAdd 1 (ρ j)) t := by
  apply defSet_eq_of_carrier_eq
  ext q
  constructor
  · rintro ⟨a,ha⟩
    have ha' : headKey a.val = q := (headKeyMap_apply (rvLabelSlice U hU ρ t) a).symm.trans ha
    let b : U := ⟨a.val,a.property.1⟩
    refine ⟨⟨b,(headKeyMap_apply U b).trans ha'⟩,?_⟩
    exact (congrArg (fun p : Point (M := M) n (1+m) => p.2 ∘ (fun j => Fin.natAdd 1 (ρ j))) ha').symm.trans
      ((headKey_selected_old_labels a.val ρ).trans a.property.2)
  · rintro ⟨⟨b,hb⟩,ht⟩
    have hb' : headKey b.val = q := (headKeyMap_apply U b).symm.trans hb
    have hOld : b.val.2 ∘ ρ = t := (headKey_selected_old_labels b.val ρ).symm.trans
      ((congrArg (fun p : Point (M := M) n (1+m) => p.2 ∘ (fun j => Fin.natAdd 1 (ρ j))) hb').trans ht)
    let a : rvLabelSlice U hU ρ t := ⟨b.val,b.property,hOld⟩
    exact ⟨a,(headKeyMap_apply (rvLabelSlice U hU ρ t) a).trans hb'⟩

end IntegrationInACVF.Section6
