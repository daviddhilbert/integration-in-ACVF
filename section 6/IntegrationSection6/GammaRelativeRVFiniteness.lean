import IntegrationSection6.GammaIsoRestrictions
import IntegrationSection6.GammaNamedRVFibres
import IntegrationSection6.GammaWitnessUniformity
import Section5.GammaFiniteFibres

/-! Finite RV fibres relative to selected old labels are preserved by
Gamma isomorphisms preserving those labels. Only the named selected labels
are added to the real base, and the VF arity is unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m l e : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem finite_selected_rv_fibres_of_gammaIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk B.real < κ)
    {A : Set (Point (M := M) n m)} {D : Set (Point (M := M) n l)} (f : GammaIso B A D)
    (ρ : Fin e → Fin m) (τ : Fin e → Fin l)
    (hLabels : ∀ a : A, (f.equiv a).val.2 ∘ τ = a.val.2 ∘ ρ)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin e → RV (M := M)),
      {r : Fin m → RV (M := M) | (x,r) ∈ A ∧ r ∘ ρ = t}.Finite) :
    ∀ (x : Fin n → VF (M := M)) (t : Fin e → RV (M := M)),
      {r : Fin l → RV (M := M) | (x,r) ∈ D ∧ r ∘ τ = t}.Finite := by
  intro x t
  let Bt : Base (M := M) := ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
  let At := A ∩ {p | p.2 ∘ ρ = t}
  let Dt := D ∩ {p | p.2 ∘ τ = t}
  let ft : GammaIso Bt A D := ⟨f.equiv,f.graph.mono Set.subset_union_left (Set.Subset.refl _)⟩
  have hAΓ : GammaSetDefinable Bt A := (ft.symm (gammaLogicInput Bt)).target_definable (gammaLogicInput Bt)
  have hAt : GammaSetDefinable Bt At :=
    (gammaLogicInput Bt).inter hAΓ (gamma_named_rv_label_fibre ρ t)
  have hCompat (a : A) : a.val ∈ At ↔ (ft.equiv a).val ∈ Dt := by
    change (_ ∧ a.val.2 ∘ ρ = t) ↔ (_ ∧ (f.equiv a).val.2 ∘ τ = t)
    rw [hLabels a]
    exact ⟨fun h => ⟨(f.equiv a).property,h.2⟩,fun h => ⟨a.property,h.2⟩⟩
  let e := gammaIsoRestrict ft (fun _ h => h.1) (fun _ h => h.1) hCompat hAt
  exact finiteRVFibres_of_gammaIso hκ hs Bt
    (small_union_range hκ B.real hsmall (fun j => (t j).val)) e
    (fun p _ => @vfTupleTrdeg_le_arity M N hN Bt.real n p.1)
    (fun z => hfin z t) x

end IntegrationInACVF.Section6
