module

public import Integration7.RVCoordinateSelection
public import Integration7.VFVolumeObjects
public import Integration7.RVNonzero
public import Section4.CodeMaps

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A retained nonzero RV coordinate is an actual definable density on
any mixed VF/RV domain. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ}

def mixedRetainedLabelVolumeForm
    (A : DefSet (rawMixedSpace (M := M) n a) S) (δ : Fin a)
    (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) : VolumeForm A where
  map := (rvCoordinateSelectMap S (fun _ : Fin 1 => δ)).comp (Map.snd (rawVFSpace n) (rawRVSpace a) S A)
  nonzero p := (rv_nonzero_iff_raw _).mpr (hδ p)

theorem mixed_retained_label_volume_form_value
    (A : DefSet (rawMixedSpace (M := M) n a) S) (δ : Fin a)
    (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) (p : A) :
    (mixedRetainedLabelVolumeForm A δ hδ).value p = p.val.2 δ := rfl

end IntegrationInACVF.Section7
