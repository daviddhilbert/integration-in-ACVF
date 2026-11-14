import Integration7.VolumeRelabeling
import Section4.RVAppend

/-! Any actual positive RV volume object can retain its density as an
extra label, through a genuine full-coordinate volume isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def appendRVVolumeDensity (U : PositiveRVVolumeObject (M := M) S k) :
    Map U.underlying.obj.domain (DefSet.univ (rawRVSpace (U.underlying.obj.arity+1)) S) :=
  (rvAppendMap S U.underlying.obj.arity 1).comp ((Map.id U.underlying.obj.domain).pair U.form.map).toUniv

theorem appendRVVolumeDensity_injective (U : PositiveRVVolumeObject (M := M) S k) :
    Function.Injective (appendRVVolumeDensity U) := by
  intro u v huv
  apply Subtype.ext
  funext i
  have h := congrArg (fun w : DefSet.univ (rawRVSpace (U.underlying.obj.arity+1)) S =>
    w.val (Fin.castAdd 1 i)) huv
  exact (Fin.append_left _ _ i).symm.trans (h.trans (Fin.append_left _ _ i))

theorem appendRVVolumeDensity_bijective (U : PositiveRVVolumeObject (M := M) S k) :
    Function.Bijective (appendRVVolumeDensity U).toImage := by
  constructor
  · intro u v huv
    have hv : ((appendRVVolumeDensity U).toImage u).val = ((appendRVVolumeDensity U).toImage v).val :=
      congrArg (fun w : (appendRVVolumeDensity U).image => w.val) huv
    exact appendRVVolumeDensity_injective U (Subtype.ext hv)
  · rintro ⟨v,u,hu⟩
    exact ⟨u,Subtype.ext hu⟩

def rvVolumeDensityProjection (U : PositiveRVVolumeObject (M := M) S k) :
    Map (appendRVVolumeDensity U).image U.underlying.obj.domain :=
  (appendRVVolumeDensity U).toImage.inverse (appendRVVolumeDensity_bijective U)

def PositiveRVVolumeObject.densityGraph (U : PositiveRVVolumeObject (M := M) S k) :
    PositiveRVVolumeObject (M := M) S k where
  underlying := ⟨{
    arity := U.underlying.obj.arity+1
    domain := (appendRVVolumeDensity U).image
    volume := U.underlying.obj.volume.comp (rvVolumeDensityProjection U) },by
      intro t
      apply ((U.underlying.property t).image (appendRVVolumeDensity U).toImage).subset
      intro v hv
      exact ⟨rvVolumeDensityProjection U v,hv,Map.apply_inverse _ _ v⟩⟩
  form := U.form.pullback (rvVolumeDensityProjection U)

theorem PositiveRVVolumeObject.densityGraph_density_last
    (U : PositiveRVVolumeObject (M := M) S k) (v : U.densityGraph.underlying.obj.domain) :
    U.densityGraph.form.value v = v.val (Fin.last U.underlying.obj.arity) := by
  have h := congrArg (fun w : (appendRVVolumeDensity U).image => w.val (Fin.last U.underlying.obj.arity))
    (Map.apply_inverse (appendRVVolumeDensity U).toImage (appendRVVolumeDensity_bijective U) v)
  exact (Fin.append_right _ _ 0).symm.trans h

def rvVolumeDensityGraphIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) : RVVolumeIso U U.densityGraph := by
  have hcoord : ∀ u, U.densityGraph.underlying.obj.value ((appendRVVolumeDensity U).toImage u) =
      U.underlying.obj.value u := by
    intro u
    change U.underlying.obj.value ((appendRVVolumeDensity U).toImage.inverse _
      ((appendRVVolumeDensity U).toImage u)) = _
    rw [Map.inverse_apply]
  let e : U.underlying ≅ U.densityGraph.underlying := rvFiniteIsoOfAmbient
    (rvIsoOfVolumePreservingBijection (appendRVVolumeDensity U).toImage (appendRVVolumeDensity_bijective U) hcoord)
  apply RVVolumeIso.of_preserving_coordinates_full hc C e hcoord
  intro u
  change U.form.value ((appendRVVolumeDensity U).toImage.inverse _ ((appendRVVolumeDensity U).toImage u)) = _
  rw [Map.inverse_apply]

end IntegrationInACVF.Section7
