import IntegrationSection6.GammaGraphPresentationExtension
import IntegrationSection6.FiniteGammaCoproducts

/-! Actual finite coproducts of graph presentations at their common
internal code union, with literal tagged domain and volume formulas. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a b k : ℕ}
variable {D : Set (Fin a → RV (M := M))} {E : Set (Fin b → RV (M := M))}
variable {R : (Fin a → RV (M := M)) → (Fin k → RV (M := M)) → Prop}
variable {T : (Fin b → RV (M := M)) → (Fin k → RV (M := M)) → Prop}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def GammaFiniteGraphPresentation.atOwnCodes (P : GammaFiniteGraphPresentation B a k D R) :
    FiniteRV.GammaObjectAt B P.codes k where
  object := FiniteRV.ofGamma P.toGamma
  real_contains := P.real_contains
  domain_graph := P.toGamma.domain_graph
  volume_graph := P.volume_graph

def gammaGraphCoprodAt (P : GammaFiniteGraphPresentation B a k D R)
    (Q : GammaFiniteGraphPresentation B b k E T) : FiniteRV.GammaObjectAt B (P.codes ∪ Q.codes) k :=
  FiniteRV.gammaCoprodAt
    (P.extend (P.codes ∪ Q.codes) Set.subset_union_left (P.union_finite_extra Q)).atOwnCodes
    (Q.extend (P.codes ∪ Q.codes) Set.subset_union_right (P.union_finite_extra Q)).atOwnCodes

def graphCoprodDomain (D : Set (Fin a → RV (M := M))) (E : Set (Fin b → RV (M := M))) :
    Set (Fin (1+(a+b)) → RV (M := M)) := {w |
  (∃ x, x ∈ D ∧ @rvLeftTag M N hN a b x = w) ∨
    ∃ y, y ∈ E ∧ @rvRightTag M N hN b a y = w}

def graphCoprodRelation (D : Set (Fin a → RV (M := M))) (E : Set (Fin b → RV (M := M)))
    (R : (Fin a → RV (M := M)) → (Fin k → RV (M := M)) → Prop)
    (T : (Fin b → RV (M := M)) → (Fin k → RV (M := M)) → Prop)
    (w : Fin (1+(a+b)) → RV (M := M)) (v : Fin k → RV (M := M)) : Prop :=
  (∃ x, x ∈ D ∧ @rvLeftTag M N hN a b x = w ∧ R x v) ∨
    ∃ y, y ∈ E ∧ @rvRightTag M N hN b a y = w ∧ T y v

theorem gammaGraphCoprodAt_domain (P : GammaFiniteGraphPresentation B a k D R)
    (Q : GammaFiniteGraphPresentation B b k E T) (w : Fin (1+(a+b)) → RV (M := M)) :
    w ∈ graphCoprodDomain D E ↔
      w ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ (P.codes ∪ Q.codes)
        (rvObjectDomain (gammaGraphCoprodAt P Q).object.obj) := by
  let S := P.codes ∪ Q.codes
  let P' := P.extend S Set.subset_union_left (P.union_finite_extra Q)
  let Q' := Q.extend S Set.subset_union_right (P.union_finite_extra Q)
  let U := P'.atOwnCodes
  let V := Q'.atOwnCodes
  constructor
  · rintro (⟨x,hx,hw⟩ | ⟨y,hy,hw⟩)
    · exact Or.inl ⟨⟨x,(Set.ext_iff.mp P'.domain_eq x).mpr hx⟩,hw⟩
    · exact Or.inr ⟨⟨y,(Set.ext_iff.mp Q'.domain_eq y).mpr hy⟩,hw⟩
  · rintro (⟨u,hu⟩ | ⟨v,hv⟩)
    · exact Or.inl ⟨u.val,(Set.ext_iff.mp P'.domain_eq u.val).mp u.property,hu⟩
    · exact Or.inr ⟨v.val,(Set.ext_iff.mp Q'.domain_eq v.val).mp v.property,hv⟩

theorem gammaGraphCoprodAt_graph (P : GammaFiniteGraphPresentation B a k D R)
    (Q : GammaFiniteGraphPresentation B b k E T) (w : Fin (1+(a+b)) → RV (M := M))
    (v : Fin k → RV (M := M)) :
    graphCoprodRelation D E R T w v ↔
      ∃ u : rvObjectDomain (gammaGraphCoprodAt P Q).object.obj, u.val = w ∧
        (rvObjectVolume (gammaGraphCoprodAt P Q).object.obj u).val = v := by
  let S := P.codes ∪ Q.codes
  let P' := P.extend S Set.subset_union_left (P.union_finite_extra Q)
  let Q' := Q.extend S Set.subset_union_right (P.union_finite_extra Q)
  let U := P'.atOwnCodes
  let V := Q'.atOwnCodes
  constructor
  · rintro (⟨x,hx,hw,hv⟩ | ⟨y,hy,hw,hv⟩)
    · obtain ⟨u,hu,huv⟩ := (P'.graph_iff x v).mpr ⟨hx,hv⟩
      exact ⟨@rvCoprodLeftMap M N hN S k U.object.obj V.object.obj u,
        (congrArg (@rvLeftTag M N hN a b) hu).trans hw,
        (@rvCoprod_value_left M N hN S k U.object.obj V.object.obj u).trans huv⟩
    · obtain ⟨u,hu,huv⟩ := (Q'.graph_iff y v).mpr ⟨hy,hv⟩
      exact ⟨@rvCoprodRightMap M N hN S k U.object.obj V.object.obj u,
        (congrArg (@rvRightTag M N hN b a) hu).trans hw,
        (@rvCoprod_value_right M N hN S k U.object.obj V.object.obj u).trans huv⟩
  · rintro ⟨u,hu,hv⟩
    rcases u.property with ⟨x,hx⟩ | ⟨y,hy⟩
    · have he : u = @rvCoprodLeftMap M N hN S k U.object.obj V.object.obj x := Subtype.ext hx.symm
      have hxv : (P'.volume x).val = v := by
        rw [he] at hv
        exact (@rvCoprod_value_left M N hN S k U.object.obj V.object.obj x).symm.trans hv
      have hp := (P'.graph_iff x.val v).mp ⟨x,rfl,hxv⟩
      exact Or.inl ⟨x.val,hp.1,hx.trans hu,hp.2⟩
    · have he : u = @rvCoprodRightMap M N hN S k U.object.obj V.object.obj y := Subtype.ext hy.symm
      have hyv : (Q'.volume y).val = v := by
        rw [he] at hv
        exact (@rvCoprod_value_right M N hN S k U.object.obj V.object.obj y).symm.trans hv
      have hp := (Q'.graph_iff y.val v).mp ⟨y,rfl,hyv⟩
      exact Or.inr ⟨y.val,hp.1,hy.trans hu,hp.2⟩

def GammaFiniteGraphPresentation.coprod (P : GammaFiniteGraphPresentation B a k D R)
    (Q : GammaFiniteGraphPresentation B b k E T) :
    GammaFiniteGraphPresentation B (1+(a+b)) k (graphCoprodDomain D E) (graphCoprodRelation D E R T) := by
  let C := gammaGraphCoprodAt P Q
  refine {
    codes := P.codes ∪ Q.codes
    real_contains := C.real_contains
    finite_extra := P.union_finite_extra Q
    domain := rvObjectDomain C.object.obj
    domain_eq := Set.ext (fun w => (gammaGraphCoprodAt_domain P Q w).symm)
    volume := rvObjectVolume C.object.obj
    graph_iff := ?_
    finite_volume := C.object.property
    domain_graph := ?_
    volume_graph := C.volume_graph }
  · intro w v
    constructor
    · intro hwv
      have hr := (gammaGraphCoprodAt_graph P Q w v).mpr hwv
      have hd : w ∈ graphCoprodDomain D E := by
        rcases hr with ⟨x,hx,hw,_⟩ | ⟨y,hy,hw,_⟩
        · exact Or.inl ⟨x,hx,hw⟩
        · exact Or.inr ⟨y,hy,hw⟩
      exact ⟨hd,hr⟩
    · exact fun hwv => (gammaGraphCoprodAt_graph P Q w v).mp hwv.2
  · have hSized : GammaSetDefinable B
        {w : Point (M := M) 0 (1+(a+b)) | w.2 ∈
          @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ (P.codes ∪ Q.codes)
            (@rvObjectDomain M sM (P.codes ∪ Q.codes) k C.object.obj)} := C.domain_graph
    convert hSized using 1
    apply Set.ext
    intro w
    exact gammaGraphCoprodAt_domain P Q w.2

end IntegrationInACVF.Section6
