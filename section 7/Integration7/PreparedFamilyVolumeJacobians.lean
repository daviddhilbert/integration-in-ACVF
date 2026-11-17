module

public import Integration7.FiniteVFBaseProjection
public import Integration7.SpecialVolumeJacobians

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Preparing the VF base of a finite RV family has Jacobian one.
The actual family projection is finite-to-one, so the checked special
Jacobian exception pulls back to a VF-small set over the same base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a b l : ℕ}

theorem finite_family_special_jacobian_one
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A₀ : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 0}
    {Z : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 l}
    (K : SpecialBijection A₀ Z)
    {U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a}
    {V : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
    (f : SpecialTransformations.Section5.Map U V)
    (hBase : ∀ p : U, (p.val.1,Fin.elim0) ∈ carrier A₀)
    (hfin : ∀ x : Fin 1 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (hVF : ∀ p : U, (f p).val.1 = (K.toMap ⟨(p.val.1,Fin.elim0),hBase p⟩).val.1) :
    VFAlmostEverywhere (rawSpecialSet hc U) (fun p => HasMixedVFJacobianAt (rawSpecialMap hc f) p 1) := by
  let q := vfBaseProjection U A₀ hBase
  apply vfJacobianOne_of_finite_vf_projection hc C Nat.one_pos (rawSpecialMap hc q)
    (rawSpecialMap hc K.toMap) (rawSpecialMap hc f) (vfBaseProjection_finiteFibres U A₀ hBase hfin)
    (fun _ => rfl) _ (special_vf_jacobian_one hc C Nat.one_pos K).1
  intro p
  have hq : q p = (⟨(p.val.1,Fin.elim0),hBase p⟩ : A₀) :=
    Subtype.ext (vfBaseProjection_value U A₀ hBase p)
  change (K.toMap (q p)).val.1 = (f p).val.1
  rw [hq]
  exact (hVF p).symm

theorem finite_family_special_preserves_volume
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A₀ : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 0}
    {Z : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 l}
    (K : SpecialBijection A₀ Z)
    {U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a}
    {V : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
    (f : SpecialTransformations.Section5.Map U V)
    (hBase : ∀ p : U, (p.val.1,Fin.elim0) ∈ carrier A₀)
    (hfin : ∀ x : Fin 1 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (hVF : ∀ p : U, (f p).val.1 = (K.toMap ⟨(p.val.1,Fin.elim0),hBase p⟩).val.1)
    (ω : VolumeForm (rawSpecialSet hc U)) (π : VolumeForm (rawSpecialSet hc V))
    (hDensity : ∀ p, ω.value p = π.value ((rawSpecialMap hc f) p)) :
    PreservesVFVolume ω π (rawSpecialMap hc f) := by
  apply (finite_family_special_jacobian_one hc C K f hBase hfin hVF).mono
  intro p hJ
  exact ⟨1,hJ,by rw [RVOperations.rv_one,mul_one]; exact hDensity p⟩

end IntegrationInACVF.Section7
