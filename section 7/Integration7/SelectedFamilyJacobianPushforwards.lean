module

public import Integration7.SelectedFamilyBasePushforwards
public import Integration7.VFBaseJacobianDensities

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual Jacobian transform of a positive selected family is its
base pushforward multiplied by the inverse base-Jacobian density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {C : BaseContext M} {n a k : ℕ}
variable {X Y : DefSet (rawVFSpace (M := M) n) S}

def mixedVFBaseImageProjection (φ : Map X Y) (U : DefSet (rawMixedSpace (M := M) n a) S)
    (hU : ∀ p : U, p.val.1 ∈ X.carrier) : Map (mixedVFBaseMap φ U hU).image Y := by
  let R := DefSet.univ (rawRVSpace (M := M) a) S
  have hD : (mixedVFBaseMap φ U hU).image.carrier ⊆ (Y.prod R).carrier := by
    rintro q ⟨p,hp⟩
    have hBase : (φ ⟨p.val.1,hU p⟩).val = q.1 := congrArg Prod.fst hp
    exact ⟨hBase ▸ (φ ⟨p.val.1,hU p⟩).property,Set.mem_univ _⟩
  exact (Map.prodFst Y R).comp (Map.inclusion hD)

theorem mixed_vf_base_image_projection_value (φ : Map X Y) (U : DefSet (rawMixedSpace (M := M) n a) S)
    (hU : ∀ p : U, p.val.1 ∈ X.carrier) (q : (mixedVFBaseMap φ U hU).image) :
    (mixedVFBaseImageProjection φ U hU q).val = q.val.1 := rfl

def SelectedVFVolumeFamily.jacobianPushforward
    {X Y : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (F : SelectedVFVolumeFamily C n a k) (φ : Map X Y) (hφ : Function.Bijective φ)
    (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier) : SelectedVFVolumeFamily C n a k where
  domain := (F.pushforwardBase φ hφ hF).domain
  selected := F.selected
  finite_selected := (F.pushforwardBase φ hφ hF).finite_selected
  form := ((pureVFInverseJacobianDensityForm φ hφ).pullback
    (mixedVFBaseImageProjection φ F.domain hF)).mul (F.pushforwardBase φ hφ hF).form

theorem SelectedVFVolumeFamily.jacobianPushforward_selected
    {X Y : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (F : SelectedVFVolumeFamily C n a k) (φ : Map X Y) (hφ : Function.Bijective φ)
    (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier) :
    (F.jacobianPushforward φ hφ hF).selected = F.selected := rfl

theorem SelectedVFVolumeFamily.jacobianPushforward_density
    {X Y : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (F : SelectedVFVolumeFamily C n a k) (φ : Map X Y) (hφ : Function.Bijective φ)
    (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier) (p : F.domain) :
    (F.jacobianPushforward φ hφ hF).form.value ((mixedVFBaseMap φ F.domain hF).toImage p) =
      (pureVFInverseJacobianDensityForm φ hφ).value (φ ⟨p.val.1,hF p⟩) * F.form.value p := by
  change (pureVFInverseJacobianDensityForm φ hφ).value (φ ⟨p.val.1,hF p⟩) *
    (F.pushforwardBase φ hφ hF).form.value ((mixedVFBaseMap φ F.domain hF).toImage p) = _
  rw [F.pushforwardBase_density]

end IntegrationInACVF.Section7
