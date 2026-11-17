module

public import Integration7.GammaMixedCoordinatePredicates
public import Integration7.NativeRVParameterSelections
public import IntegrationSection5.GammaOrderedContraction

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Restricting a native domain by an arbitrary original-Gamma set
of selected old RV labels keeps its original small real presentation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n m k : ℕ}

theorem gamma_rv_label_cut (A : DefSet (M := M) S n m) (hA : GammaSetDefinable G (carrier A))
    (ρ : Fin k → Fin m) (R : Set (Point (M := M) 0 k)) (hR : GammaSetDefinable G R) :
    GammaSetDefinable G (carrier A ∩ {p | (Fin.elim0,p.2 ∘ ρ) ∈ R}) := by
  apply (gammaLogicInput G).inter hA
  have h := gamma_mixed_coordinate_preimage hR (Fin.elim0 : Fin 0 → Fin n) ρ
  convert h using 1
  ext p
  have he : (p.1 ∘ (Fin.elim0 : Fin 0 → Fin n),p.2 ∘ ρ) = (Fin.elim0,p.2 ∘ ρ) :=
    Prod.ext (Subsingleton.elim _ _) rfl
  change ((Fin.elim0,p.2 ∘ ρ) ∈ R ↔ (p.1 ∘ (Fin.elim0 : Fin 0 → Fin n),p.2 ∘ ρ) ∈ R)
  rw [he]

def rvLabelCut (A : DefSet (M := M) S n m) (hA : GammaSetDefinable G (carrier A))
    (ρ : Fin k → Fin m) (R : Set (Point (M := M) 0 k)) (hR : GammaSetDefinable G R)
    (hNames : commonRealNames G ⊆ S) : DefSet (M := M) S n m :=
  PresentedSet.mk (carrier A ∩ {p | (Fin.elim0,p.2 ∘ ρ) ∈ R}) (SetDefinable.mono _
    (gamma_native_set_common_names (gamma_rv_label_cut A hA ρ R hR)) hNames)

theorem rv_label_cut_finite_labels (A : DefSet (M := M) S n m) (hA : GammaSetDefinable G (carrier A))
    (ρ : Fin k → Fin m) (R : Set (Point (M := M) 0 k)) (hR : GammaSetDefinable G R)
    (hNames : commonRealNames G ⊆ S)
    (hfin : ∀ x : Fin n → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite) :
    ∀ x : Fin n → VF (M := M),
      {r : Fin m → RV (M := M) | (x,r) ∈ carrier (rvLabelCut A hA ρ R hR hNames)}.Finite :=
  fun x => (hfin x).subset (fun _ h => h.1)

theorem rv_label_cut_head_image {A : DefSet (M := M) S (n+1) m}
    (hA : GammaSetDefinable G (carrier A)) (ρ : Fin k → Fin m)
    (R : Set (Point (M := M) 0 k)) (hR : GammaSetDefinable G R) (hNames : commonRealNames G ⊆ S) :
    headImage (rvLabelCut A hA ρ R hR hNames) =
      rvLabelCut (headImage A) (gamma_headImage A hA) (Fin.natAdd 1 ∘ ρ) R hR hNames := by
  apply defSet_eq_of_carrier_eq
  ext q
  constructor
  · rintro ⟨a,ha⟩
    have he := (headKeyMap_apply _ a).symm.trans ha
    let b : A := ⟨a.val,a.property.1⟩
    refine ⟨⟨b,(headKeyMap_apply A b).trans he⟩,?_⟩
    have hLabel : q.2 ∘ (Fin.natAdd 1 ∘ ρ) = a.val.2 ∘ ρ := by
      rw [← he]
      funext j
      change Fin.append (fun _ : Fin 1 => rv (vfAt a.val 0)) a.val.2 (Fin.natAdd 1 (ρ j)) = a.val.2 (ρ j)
      exact Fin.append_right _ _ _
    exact (congrArg (fun r : Fin k → RV (M := M) => (Fin.elim0,r) ∈ R) hLabel).mpr a.property.2
  · rintro ⟨⟨b,hb⟩,hR⟩
    have he := (headKeyMap_apply A b).symm.trans hb
    have hLabel : b.val.2 ∘ ρ = q.2 ∘ (Fin.natAdd 1 ∘ ρ) := by
      rw [← he]
      funext j
      change b.val.2 (ρ j) = Fin.append (fun _ : Fin 1 => rv (vfAt b.val 0)) b.val.2 (Fin.natAdd 1 (ρ j))
      exact (Fin.append_right _ _ _).symm
    let a : rvLabelCut A hA ρ R ‹GammaSetDefinable G R› hNames := ⟨b.val,b.property,
      (congrArg (fun r : Fin k → RV (M := M) => (Fin.elim0,r) ∈ R) hLabel).mpr hR⟩
    exact ⟨a,(headKeyMap_apply _ a).trans he⟩

end IntegrationInACVF.Section7
