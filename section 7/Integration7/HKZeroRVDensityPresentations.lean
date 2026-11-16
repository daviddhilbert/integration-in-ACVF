module

public import Integration7.HKNativeZeroDensityObjects
public import Integration7.RVVolumeDensityGraphs

@[expose] public section

/-! Every weighted finite zero object has an exact original-base
presentation with its supplied density retained as the last label. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def appendZeroRVDensity (Z : ZeroRVVolumeObject (M := M) S) :
    Map Z.underlying.obj.domain (DefSet.univ (rawRVSpace (Z.underlying.obj.arity+1)) S) :=
  (rvAppendMap S Z.underlying.obj.arity 1).comp ((Map.id Z.underlying.obj.domain).pair Z.form.map).toUniv

theorem append_zero_rv_density_bijective (Z : ZeroRVVolumeObject (M := M) S) :
    Function.Bijective (appendZeroRVDensity Z).toImage := by
  constructor
  · intro u v he
    apply Subtype.ext
    funext i
    have h := congrArg (fun w : (appendZeroRVDensity Z).image => w.val (Fin.castAdd 1 i)) he
    exact (Fin.append_left _ _ i).symm.trans (h.trans (Fin.append_left _ _ i))
  · rintro ⟨v,u,hu⟩
    exact ⟨u,Subtype.ext hu⟩

def ZeroRVVolumeObject.densityGraph (Z : ZeroRVVolumeObject (M := M) S) : ZeroRVVolumeObject (M := M) S where
  underlying := ⟨{
    arity := Z.underlying.obj.arity+1
    domain := (appendZeroRVDensity Z).image
    volume := Z.underlying.obj.volume.comp
      ((appendZeroRVDensity Z).toImage.inverse (append_zero_rv_density_bijective Z)) },by
      intro t
      apply ((Z.underlying.property t).image (appendZeroRVDensity Z).toImage).subset
      intro v hv
      exact ⟨(appendZeroRVDensity Z).toImage.inverse (append_zero_rv_density_bijective Z) v,
        hv,Map.apply_inverse _ _ v⟩⟩
  form := Z.form.pullback ((appendZeroRVDensity Z).toImage.inverse (append_zero_rv_density_bijective Z))

theorem ZeroRVVolumeObject.densityGraph_density_last (Z : ZeroRVVolumeObject (M := M) S)
    (v : Z.densityGraph.underlying.obj.domain) :
    Z.densityGraph.form.value v = v.val (Fin.last Z.underlying.obj.arity) := by
  have h := congrArg (fun w : (appendZeroRVDensity Z).image => w.val (Fin.last Z.underlying.obj.arity))
    (Map.apply_inverse (appendZeroRVDensity Z).toImage (append_zero_rv_density_bijective Z) v)
  exact (Fin.append_right _ _ 0).symm.trans h

def zeroRVDensityGraphIso (Z : ZeroRVVolumeObject (M := M) S) : ZeroRVVolumeIso Z Z.densityGraph :=
  ZeroRVVolumeIso.ofBijection (appendZeroRVDensity Z).toImage (append_zero_rv_density_bijective Z) (by
    intro u
    change Z.form.value u = Z.form.value ((appendZeroRVDensity Z).toImage.inverse _
      ((appendZeroRVDensity Z).toImage u))
    rw [Map.inverse_apply])

end IntegrationInACVF.Section7.HK
