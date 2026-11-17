module

public import Integration7.GammaRVParameterSelections
public import Integration7.GammaNativeCommonNames

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual native definable domains for whole RV-parameter selections.
They use the fixed common names, retain every old coordinate and density
label, and inherit finite RV fibres from the original source. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n m d : ℕ}

def nativeRVParameterSelection (A : DefSet (M := M) S n m) (P : GammaRVMap G (carrier A) d)
    (R : Set (Point (M := M) 0 d)) (hR : GammaSetDefinable G R) (hNames : commonRealNames G ⊆ S) :
    DefSet (M := M) S n m :=
  PresentedSet.mk (P.selectedDomain R) (SetDefinable.mono _
    (gamma_native_set_common_names (P.selected_domain_gamma hR)) hNames)

theorem gamma_native_rv_parameter_selection (A : DefSet (M := M) S n m) (P : GammaRVMap G (carrier A) d)
    (R : Set (Point (M := M) 0 d)) (hR : GammaSetDefinable G R) (hNames : commonRealNames G ⊆ S) :
    GammaSetDefinable G (carrier (nativeRVParameterSelection A P R hR hNames)) := P.selected_domain_gamma hR

theorem native_rv_parameter_selection_finite_labels (A : DefSet (M := M) S n m)
    (P : GammaRVMap G (carrier A) d) (R : Set (Point (M := M) 0 d)) (hR : GammaSetDefinable G R)
    (hNames : commonRealNames G ⊆ S)
    (hfin : ∀ x : Fin n → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite) :
    ∀ x : Fin n → VF (M := M),
      {r : Fin m → RV (M := M) | (x,r) ∈ carrier (nativeRVParameterSelection A P R hR hNames)}.Finite := by
  intro x
  apply (hfin x).subset
  rintro r ⟨a,ha,_⟩
  exact (congrArg (fun p : Point (M := M) n m => p ∈ carrier A) ha).mp a.property

theorem native_rv_parameter_selection_density_nonzero (A : DefSet (M := M) S n m)
    (P : GammaRVMap G (carrier A) d) (R : Set (Point (M := M) 0 d)) (hR : GammaSetDefinable G R)
    (hNames : commonRealNames G ⊆ S) (δ : Fin m) (hδ : ∀ a : A, (a.val.2 δ).val ≠ iRVZero) :
    ∀ a : nativeRVParameterSelection A P R hR hNames, (a.val.2 δ).val ≠ iRVZero :=
  fun a => hδ (P.selectedInclusion R a)

end IntegrationInACVF.Section7
