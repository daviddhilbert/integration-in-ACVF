import Integration7.IndexedVolumeCoproductDensities
import Integration7.VolumeDataRelabelingMaps

/-! Restricting the index base gives the actual restriction of the
joint volume object. The label identity preserves coordinates and density. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5 (RV)
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ}
variable {T E : Set (Fin p → RV (M := M))}
variable {R S : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

def indexedVolumeRestrictionIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (BQ : GammaFiniteGraphPresentation B p d E S)
    (hET : E ⊆ T) (hVolume : ∀ t ∈ E, BQ.totalVolume t = BP.totalVolume t)
    (P : F.IndexedPresentation BP) (Q : F.IndexedPresentation BQ)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (A : DefSet (rawRVSpace (M := M) (p+a)) (C.base : Set M))
    (hA : A.carrier = indexedDomain E (fun t => F.object.rowDomain (rvValues t)))
    (hAU : A.carrier ⊆ (P.inContext hc C hP).underlying.obj.domain.carrier) :
    RVVolumeIso (Q.inContext hc C hQ).toObject ((P.inContext hc C hP).toObject.restrict A hAU) := by
  let U := (P.inContext hc C hP).toObject
  let V := (Q.inContext hc C hQ).toObject
  let W := U.restrict A hAU
  have hDom : V.underlying.obj.domain.carrier = A.carrier :=
    (GammaVolumeGraphPresentation.inContext_domain hc C Q hQ).trans hA.symm
  let f : Map V.underlying.obj.domain W.underlying.obj.domain :=
    Map.inclusion (fun x hx => (Set.ext_iff.mp hDom x).mp hx)
  have hf : Function.Bijective f := by
    constructor
    · intro u v h
      have he : (f u).val = (f v).val := congrArg (fun w : W.underlying.obj.domain => w.val) h
      exact Subtype.ext he
    · intro v
      exact ⟨⟨v.val,(Set.ext_iff.mp hDom v.val).mpr v.property⟩,rfl⟩
  have hCoord (u : V.underlying.obj.domain) : W.underlying.obj.value (f u) = V.underlying.obj.value u := by
    have hPValue := indexedVolume_coordinates hc C P hP ⟨u.val,hAU (f u).property⟩
    have hQValue := indexedVolume_coordinates hc C Q hQ u
    have h := congrArg (fun v => Fin.append v
      (F.object.rowValue (rvValues (indexedLeft u.val)) (indexedRight u.val))) (hVolume (indexedLeft u.val) ((indexedVolume_domain_iff hc C Q hQ u.val).mp u.property).1)
    exact hPValue.trans (h.symm.trans hQValue.symm)
  have hDensity (u : V.underlying.obj.domain) : W.form.value (f u) = V.form.value u := by
    let v : U.underlying.obj.domain := ⟨u.val,hAU (f u).property⟩
    have hD := (indexedVolume_domain_iff hc C Q hQ u.val).mp u.property
    have hρ : F.indexedDensity T v.val (fun _ => V.form.value u) :=
      ⟨⟨hET hD.1,hD.2⟩,indexedVolume_density_value hc C Q hQ u⟩
    exact (indexedVolume_density_eq hc C P hP v _ hρ).symm
  let e := rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hCoord)
  exact RVVolumeIso.of_preserving_coordinates_full hc C e hCoord hDensity

end IntegrationInACVF.Section7
