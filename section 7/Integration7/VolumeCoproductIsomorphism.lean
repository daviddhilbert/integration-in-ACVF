import Integration7.CoproductEssentialComparison
import Integration7.ExplicitRVCoproductIso
import Integration7.VolumeIsomorphismGluing
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
noncomputable section
namespace IntegrationInACVF.Section7.RVVolumeIso
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
variable {U U' V V' : PositiveRVVolumeObject (M := M) S k}

def coprodUnderlying (f : RVVolumeIso U U') (g : RVVolumeIso V V') :
    (U.coprod V).essential ≅ (U'.coprod V').essential :=
  (coprodEssentialComparisonIso U V).symm.trans
    ((rvFiniteIsoOfAmbient (rvCoprodIsoExplicit
      ((finiteVolumeProperty S (k+1)).ι.mapIso f.iso)
      ((finiteVolumeProperty S (k+1)).ι.mapIso g.iso))).trans (coprodEssentialComparisonIso U' V'))

theorem coprodUnderlying_left (f : RVVolumeIso U U') (g : RVVolumeIso V V')
    (u : U.essential.obj.domain) :
    finiteIsoMap (coprodUnderlying f g) (coprodEssentialLeftMap U V u) =
      coprodEssentialLeftMap U' V' (finiteIsoMap f.iso u) := by
  have hc : finiteIsoMap (coprodEssentialComparisonIso U V).symm (coprodEssentialLeftMap U V u) =
      rvCoprodLeftMap U.essential.obj V.essential.obj u := by
    rw [← coprodEssentialComparisonIso_left U V u, finiteIsoMap_symm_apply]
  simp only [coprodUnderlying, finiteIsoMap_trans, hc]
  change finiteIsoMap (coprodEssentialComparisonIso U' V')
    ((rvCoprodIsoExplicit ((finiteVolumeProperty S (k+1)).ι.mapIso f.iso)
      ((finiteVolumeProperty S (k+1)).ι.mapIso g.iso)).hom.map
      (rvCoprodLeftMap U.essential.obj V.essential.obj u)) = _
  exact (congrArg (finiteIsoMap (coprodEssentialComparisonIso U' V'))
    (rvCoprodIsoExplicit_left ((finiteVolumeProperty S (k+1)).ι.mapIso f.iso)
      ((finiteVolumeProperty S (k+1)).ι.mapIso g.iso) u)).trans
    (coprodEssentialComparisonIso_left U' V' (finiteIsoMap f.iso u))

theorem coprodUnderlying_right (f : RVVolumeIso U U') (g : RVVolumeIso V V')
    (v : V.essential.obj.domain) :
    finiteIsoMap (coprodUnderlying f g) (coprodEssentialRightMap U V v) =
      coprodEssentialRightMap U' V' (finiteIsoMap g.iso v) := by
  have hc : finiteIsoMap (coprodEssentialComparisonIso U V).symm (coprodEssentialRightMap U V v) =
      rvCoprodRightMap U.essential.obj V.essential.obj v := by
    rw [← coprodEssentialComparisonIso_right U V v, finiteIsoMap_symm_apply]
  simp only [coprodUnderlying, finiteIsoMap_trans, hc]
  change finiteIsoMap (coprodEssentialComparisonIso U' V')
    ((rvCoprodIsoExplicit ((finiteVolumeProperty S (k+1)).ι.mapIso f.iso)
      ((finiteVolumeProperty S (k+1)).ι.mapIso g.iso)).hom.map
      (rvCoprodRightMap U.essential.obj V.essential.obj v)) = _
  exact (congrArg (finiteIsoMap (coprodEssentialComparisonIso U' V'))
    (rvCoprodIsoExplicit_right ((finiteVolumeProperty S (k+1)).ι.mapIso f.iso)
      ((finiteVolumeProperty S (k+1)).ι.mapIso g.iso) v)).trans
    (coprodEssentialComparisonIso_right U' V' (finiteIsoMap g.iso v))

def coprod (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U U' V V' : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (f : RVVolumeIso U U') (g : RVVolumeIso V V') : RVVolumeIso (U.coprod V) (U'.coprod V') := by
  let e := coprodUnderlying f g
  let p : EmbeddedVolumeIso (U.coprod V) (U'.coprod V') e := {
    source := U
    target := U'
    iso := f
    inclusion := coprodEssentialLeftMap U V
    injective := coprodEssentialLeftMap_injective U V
    source_coordinates := coprodEssentialLeftMap_coordinates U V
    target_coordinates := by intro u; rw [coprodUnderlying_left, coprodEssentialLeftMap_coordinates]
    source_density := coprodEssentialLeftMap_density U V
    target_density := by intro u; rw [coprodUnderlying_left, coprodEssentialLeftMap_density] }
  let q : EmbeddedVolumeIso (U.coprod V) (U'.coprod V') e := {
    source := V
    target := V'
    iso := g
    inclusion := coprodEssentialRightMap U V
    injective := coprodEssentialRightMap_injective U V
    source_coordinates := coprodEssentialRightMap_coordinates U V
    target_coordinates := by intro v; rw [coprodUnderlying_right, coprodEssentialRightMap_coordinates]
    source_density := coprodEssentialRightMap_density U V
    target_density := by intro v; rw [coprodUnderlying_right, coprodEssentialRightMap_density] }
  exact glue hc C e p q (coprodEssential_cover U V)
end IntegrationInACVF.Section7.RVVolumeIso
