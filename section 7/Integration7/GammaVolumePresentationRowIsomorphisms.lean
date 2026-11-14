import Integration7.GammaVolumePresentationCongruence
import Integration7.GammaVolumePresentationContexts

/-! Equal full coordinate/density rows induce actual volume isomorphisms
by the identity on labels, even when the presentation formulas differ. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV)
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a d : ℕ}
variable {D D' : Set (Fin a → RV (M := M))}
variable {R R' : (Fin a → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
variable {W W' : (Fin a → RV (M := M)) → (Fin 1 → RV (M := M)) → Prop}

def gammaVolumePresentationIsoOfRelations
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : GammaVolumeGraphPresentation B a d D R W) (Q : GammaVolumeGraphPresentation B a d D' R' W')
    (hD : D = D') (hR : ∀ x t, R x t ↔ R' x t) (hW : ∀ x ω, W x ω ↔ W' x ω)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M)) :
    RVVolumeIsoInDegree (C.base : Set M) d
      (P.inContext hc C hP).toObject (Q.inContext hc C hQ).toObject := by
  let A := P.inContext hc C hP
  let E := Q.inContext hc C hQ
  have hdom : A.underlying.obj.domain.carrier = E.underlying.obj.domain.carrier :=
    P.finite.domain_eq.trans (hD.trans Q.finite.domain_eq.symm)
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
    have hx' : x.val ∈ D' ∧ R' x.val (A.underlying.obj.volume x).val :=
      ⟨hD ▸ hx.1,(hR _ _).mp hx.2⟩
    obtain ⟨y,hy,hv⟩ := (Q.finite.graph_iff x.val (A.underlying.obj.volume x).val).mpr hx'
    have he : y = (⟨(f x).val,(f x).property⟩ : Q.finite.domain) := Subtype.ext hy
    exact (congrArg (fun u => (Q.finite.volume u).val) he).symm.trans hv
  · intro x
    have hx := (P.density_iff x.val (A.form.map x).val).mp ⟨⟨x.val,x.property⟩,rfl,rfl⟩
    obtain ⟨y,hy,hv⟩ := (Q.density_iff x.val (A.form.map x).val).mpr ((hW _ _).mp hx)
    have he : y = (⟨(f x).val,(f x).property⟩ : Q.finite.domain) := Subtype.ext hy
    have hval : (E.form.map (f x)).val = (A.form.map x).val :=
      (congrArg (fun u => (@VolumeForm.map M (@CanonicalStructure.normalize M sM)
        (@CanonicalStructure.normalized_model M sM hM) _ Q.finite.codes Q.finite.domain Q.form u).val) he).symm.trans hv
    exact congrFun hval 0

def GammaRVVolumeSchema.sameRowIso {p k : ℕ} {sp : Fin p → SortTag}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F G : GammaRVVolumeSchema B p a k sp) (z : Fin p → M) (h : F.sameRow G z)
    (P : GammaVolumeGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a (k+1)
      (F.object.rowDomain z) (F.object.rowVolume z) (F.rowDensity z))
    (Q : GammaVolumeGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a (k+1)
      (G.object.rowDomain z) (G.object.rowVolume z) (G.rowDensity z))
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M)) :
    RVVolumeIso (P.inContext hc C hP).toObject (Q.inContext hc C hQ).toObject :=
  gammaVolumePresentationIsoOfRelations hc C P Q (F.object.sameRow_domains G.object h.1)
    (fun x t => h.1.2.2 (fun i => (x i).val) (fun i => (t i).val))
    (fun x ω => h.2.2.2 (fun i => (x i).val) (fun i => (ω i).val)) hP hQ

end IntegrationInACVF.Section7
