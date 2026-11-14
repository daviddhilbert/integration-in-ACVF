import Integration7.VolumeFocusBlowups
import Integration7.CanonicalFiniteRVObjects
import IntegrationSection6.OriginalFocusObjects

/-! The full-focus volume blowup has exactly the released canonical
RV image domain, projected coordinates and retained old-label density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5 (Focus carrier)
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {k : ℕ}

def ElementaryBlowup.relabelFull {S : Set M}
    {U W V : PositiveRVVolumeObject (M := M) S k} (b : ElementaryBlowup U W)
    (f : Map V.underlying.obj.domain W.underlying.obj.domain) (hf : Function.Bijective f)
    (hcoord : ∀ v, V.underlying.obj.value v = W.underlying.obj.value (f v))
    (hDensity : ∀ v, V.form.value v = W.form.value (f v)) : ElementaryBlowup U V where
  admissible := b.admissible
  chartMap := b.chartMap.comp f
  chartMap_bijective := b.chartMap_bijective.comp hf
  head v i := (congrFun (hcoord v) i.castSucc).trans (b.head (f v) i)
  last v := (congrFun (hcoord v) (Fin.last k)).trans (b.last (f v))
  volume v := (hDensity v).trans (b.volume (f v))

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
variable {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) U.underlying.obj.arity}
variable (h : Section6.PresentsLift U.underlying.obj A) {j : Fin U.underlying.obj.arity}
variable (D : Focus A (Fin.last k) j) (hfull : carrier A ⊆ D.locus) (hAd : BlowupAdmissible U)

theorem fullFocusVolumeObject_domain_eq :
    (fullFocusVolumeObject C U h D hfull hAd).underlying.obj.domain.carrier =
      (canonicalRVObject hc (Section6.originalFocusObject D)).domain.carrier := by
  ext r
  exact (Section6.originalFocusObject_mem D r).symm

def fullFocusPresentedVolumeObject : PositiveRVVolumeObject (M := M) (C.base : Set M) k := by
  let W := fullFocusVolumeObject C U h D hfull hAd
  let V := canonicalRVObject hc (Section6.originalFocusObject D)
  let e : W.underlying.obj ≅ V := rvIsoOfCarrierEq _ _ _ _
    (fullFocusVolumeObject_domain_eq hc C U h D hfull hAd) (fun _ => rfl)
  refine { underlying := ⟨V,(Section6.finite_volume_iso e).mp W.underlying.property⟩
           form := W.form.pullback (Map.inclusion
             (fullFocusVolumeObject_domain_eq hc C U h D hfull hAd).ge) }

def fullFocusPresentedVolumeBlowup :
    ElementaryBlowup U (fullFocusPresentedVolumeObject hc C U h D hfull hAd) := by
  let W := fullFocusVolumeObject C U h D hfull hAd
  let V := fullFocusPresentedVolumeObject hc C U h D hfull hAd
  let f : Map V.underlying.obj.domain W.underlying.obj.domain :=
    Map.inclusion (fullFocusVolumeObject_domain_eq hc C U h D hfull hAd).ge
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      have hv : (f x).val = (f y).val := congrArg (fun w : W.underlying.obj.domain => w.val) he
      exact Subtype.ext hv
    · intro w
      exact ⟨⟨w.val,(fullFocusVolumeObject_domain_eq hc C U h D hfull hAd).le w.property⟩,rfl⟩
  exact (fullFocusVolumeBlowup C U h D hfull hAd).relabelFull f hf (fun _ => rfl) (fun _ => rfl)

theorem fullFocusPresentedVolumeObject_density_label (δ : Fin U.underlying.obj.arity)
    (hDensity : ∀ u, U.form.value u = u.val δ)
    (w : (fullFocusPresentedVolumeObject hc C U h D hfull hAd).underlying.obj.domain) :
    (fullFocusPresentedVolumeObject hc C U h D hfull hAd).form.value w = w.val (Fin.natAdd (k+1) δ) :=
  fullFocusVolumeObject_density_label C U h D hfull hAd δ hDensity
    ⟨w.val,(fullFocusVolumeObject_domain_eq hc C U h D hfull hAd).ge w.property⟩

end IntegrationInACVF.Section7
