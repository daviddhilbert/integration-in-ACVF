module

public import Integration7.OrdinaryZeroVolumeRows
public import Integration7.SelectedVolumeRowContexts
public import Integration7.VFVolumeObjects
public import Integration7.GradedVolumeProducts

@[expose] public section

/-! Genuine ordinary degree-zero-valued families: each VF fibre has
finitely many RV labels, no volume coordinates, and no assigned density.
Their positive-dimensional VF realization has the unit volume form. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a : ℕ}

structure OrdinaryVFVolumeFamily (C : BaseContext M) (n a : ℕ) where
  domain : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)
  finite_labels : ∀ x : Fin n → VFType (M := M), {r : Fin a → CanonicalRV.RVSort M | (x,r) ∈ domain.carrier}.Finite

def OrdinaryVFVolumeFamily.rowInContext (F : OrdinaryVFVolumeFamily C n a)
    (x : Fin n → VFType (M := M)) : RVFiniteObject (M := M) ((vfParameterVolumeContext C x).base : Set M) 0 :=
  Section6.FiniteRV.extendObject (vfParameterVolumeContext_contains C x)
    (ordinaryZeroVolumeRow F.domain F.finite_labels x)

def OrdinaryVFVolumeFamily.fullVFObject (F : OrdinaryVFVolumeFamily C (n+1) a) :
    PositiveVFVolumeObject (M := M) (C.base : Set M) n where
  arity := a
  domain := F.domain
  finite_labels := F.finite_labels
  form := VolumeForm.one F.domain

@[simp] theorem OrdinaryVFVolumeFamily.fullVFObject_density
    (F : OrdinaryVFVolumeFamily C (n+1) a) (q : F.fullVFObject.domain) : F.fullVFObject.form.value q=1 := rfl

end IntegrationInACVF.Section7
