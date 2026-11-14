import Integration7.VolumeRelabeling
import Integration7.RVCoordinateSelection

/-! A retained nonzero RV label is an actual density. Full coordinate
and density-label identities give genuine volume-category isomorphisms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def coordinateDensityVolumeObject (U : RVFiniteObject (M := M) S (k+1))
    (δ : Fin U.obj.arity) (hδ : ∀ u : U.obj.domain, u.val δ ≠ 0) :
    PositiveRVVolumeObject (M := M) S k where
  underlying := U
  form := {
    map := (rvCoordinateSelectMap S (fun _ : Fin 1 => δ)).restrict (Set.subset_univ _)
    nonzero := hδ }

theorem coordinateDensityVolumeObject_density (U : RVFiniteObject (M := M) S (k+1))
    (δ : Fin U.obj.arity) (hδ : ∀ u : U.obj.domain, u.val δ ≠ 0) (u : U.obj.domain) :
    (coordinateDensityVolumeObject U δ hδ).form.value u = u.val δ := rfl

def coordinateDensityVolumeIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : RVFiniteObject (M := M) (C.base : Set M) (k+1))
    (δ : Fin U.obj.arity) (ε : Fin V.obj.arity)
    (hδ : ∀ u : U.obj.domain, u.val δ ≠ 0) (hε : ∀ v : V.obj.domain, v.val ε ≠ 0)
    (e : U ≅ V) (hcoord : ∀ u, V.obj.value (finiteIsoMap e u) = U.obj.value u)
    (hlabel : ∀ u, (finiteIsoMap e u).val ε = u.val δ) :
    RVVolumeIso (coordinateDensityVolumeObject U δ hδ) (coordinateDensityVolumeObject V ε hε) :=
  RVVolumeIso.of_preserving_coordinates_full hc C e hcoord hlabel

end IntegrationInACVF.Section7
