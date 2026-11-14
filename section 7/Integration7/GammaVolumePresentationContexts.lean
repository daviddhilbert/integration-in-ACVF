import Integration7.GammaVolumeCanonicalObjects
import Integration7.VolumeParameterExtension
import Integration7.VolumeDataRelabelingMaps

/-! Internal code presentations may be placed in a containing genuine
base context. No generation claim is made about the code set itself. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a k : ℕ}
variable {D : Set (Fin a → RV (M := M))}
variable {R : (Fin a → RV (M := M)) → (Fin k → RV (M := M)) → Prop}
variable {W : (Fin a → RV (M := M)) → (Fin 1 → RV (M := M)) → Prop}

def GammaVolumeGraphPresentation.inContext
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : GammaVolumeGraphPresentation B a k D R W) (hP : P.finite.codes ⊆ (C.base : Set M)) :
    RVVolumeData (M := M) (C.base : Set M) k := (P.canonicalData hc).extend hP

@[simp] theorem GammaVolumeGraphPresentation.inContext_domain
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : GammaVolumeGraphPresentation B a k D R W) (hP : P.finite.codes ⊆ (C.base : Set M)) :
    (P.inContext hc C hP).underlying.obj.domain.carrier = D := P.finite.domain_eq

def gammaVolumePresentationIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P Q : GammaVolumeGraphPresentation B a k D R W)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M)) :
    RVVolumeIsoInDegree (C.base : Set M) k
      (P.inContext hc C hP).toObject (Q.inContext hc C hQ).toObject := by
  let A := P.inContext hc C hP
  let E := Q.inContext hc C hQ
  have hdom : A.underlying.obj.domain.carrier = E.underlying.obj.domain.carrier :=
    P.finite.domain_eq.trans Q.finite.domain_eq.symm
  let f : Map A.underlying.obj.domain E.underlying.obj.domain :=
    Map.inclusion (fun x hx => (Set.ext_iff.mp hdom x).mp hx)
  apply rvVolumeDataRelabelIso hc C A E f
  · constructor
    · intro x y h
      exact Subtype.ext (congrArg (fun z : E.underlying.obj.domain => z.val) h)
    · intro y
      exact ⟨⟨y.val,(Set.ext_iff.mp hdom y.val).mpr y.property⟩,rfl⟩
  · intro x
    have hx := (P.finite.graph_iff x.val (A.underlying.obj.volume x).val).mp
      ⟨⟨x.val,x.property⟩,rfl,rfl⟩
    obtain ⟨y,hy,hv⟩ := (Q.finite.graph_iff x.val (A.underlying.obj.volume x).val).mpr hx
    have he : y = (⟨(f x).val,(f x).property⟩ : Q.finite.domain) := Subtype.ext hy
    exact (congrArg (fun u => (Q.finite.volume u).val) he).symm.trans hv
  · intro x
    have hx := (P.density_iff x.val (A.form.map x).val).mp ⟨⟨x.val,x.property⟩,rfl,rfl⟩
    obtain ⟨y,hy,hv⟩ := (Q.density_iff x.val (A.form.map x).val).mpr hx
    have he : y = (⟨(f x).val,(f x).property⟩ : Q.finite.domain) := Subtype.ext hy
    have hval : (E.form.map (f x)).val = (A.form.map x).val :=
      (congrArg (fun u => (@VolumeForm.map M (@CanonicalStructure.normalize M sM)
        (@CanonicalStructure.normalized_model M sM hM) _ Q.finite.codes Q.finite.domain Q.form u).val) he).symm.trans hv
    exact congrFun hval 0

end IntegrationInACVF.Section7
