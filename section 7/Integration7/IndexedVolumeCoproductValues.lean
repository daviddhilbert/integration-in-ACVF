import Integration7.IndexedVolumeCoproductDensities
import IntegrationSection6.IndexedCoproductVolumes

/-! The index/coproduct label equivalence preserves the entire appended
coordinate tuple and the actual scalar density on both summands. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem indexedVolumeCoprodEquiv_values
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (G : GammaRVVolumeSchema B p b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.object.finiteRow (rvValues t)) (hG : ∀ t ∈ T, G.object.finiteRow (rvValues t))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (Z : (F.coprodFormula G).IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hZ : Z.finite.codes ⊆ (C.base : Set M))
    (u : (Z.inContext hc C hZ).underlying.obj.domain) :
    let e := indexedVolumeCoprodEquiv hc C F G BP P Q Z hP hQ hZ
    let A := (P.inContext hc C hP).toObject.coprod (Q.inContext hc C hQ).toObject
    A.underlying.obj.value (e u) = (Z.inContext hc C hZ).underlying.obj.value u ∧
      A.form.value (e u) = (Z.inContext hc C hZ).form.value u := by
  let D := fun t => F.object.rowDomain (rvValues t)
  let E := fun t => G.object.rowDomain (rvValues t)
  let e := indexedVolumeCoprodEquiv hc C F G BP P Q Z hP hQ hZ
  let U := (P.inContext hc C hP).toObject
  let V := (Q.inContext hc C hQ).toObject
  let A := U.coprod V
  let ZU := (Z.inContext hc C hZ).toObject
  have hZV := indexedVolume_coordinates hc C Z hZ u
  change ZU.underlying.obj.value u =
    indexedVolume BP.totalVolume (fun t => (F.object.coprodFormula G.object).rowValue (rvValues t)) u.val at hZV
  rcases indexedCoprod_cases T D E (indexedVolumeCoprodSourceEquiv hc C F G BP Z hZ u) with
    ⟨t,x,he⟩ | ⟨t,x,he⟩
  · have hu := congrArg Subtype.val he
    change u.val = (indexedCoprodLeft T D E t x).val at hu
    let v : U.underlying.obj.domain := ⟨Fin.append t.val x.val,
      (indexedVolume_domain_iff hc C P hP _).mpr (by
        simpa only [indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right]
          using And.intro t.property x.property)⟩
    have hImage : (e u).val = rvLeftTag (p+b) v.val := by
      change (indexedCoprodEquiv T D E (indexedVolumeCoprodSourceEquiv hc C F G BP Z hZ u)).val = _
      rw [he]
      exact (indexedCoprodEquiv_left T D E t x).trans (rvLeftTag_normalize v.val)
    have hTarget : e u = rvCoprodLeftMap U.underlying.obj V.underlying.obj v := Subtype.ext hImage
    have hUV := indexedVolume_coordinates hc C P hP v
    change U.underlying.obj.value v = indexedVolume BP.totalVolume (fun t => F.object.rowValue (rvValues t)) v.val at hUV
    have hStd := (congrArg
      (indexedVolume BP.totalVolume (fun t => (F.object.coprodFormula G.object).rowValue (rvValues t))) hu).trans
      (indexedCoprodLeft_volume F.object G.object T BP.totalVolume t x
        (hF t.val t.property)
        (hG t.val t.property))
    have hρ : F.indexedDensity T v.val (fun _ => U.form.value v) :=
      ⟨(indexedVolume_domain_iff hc C P hP v.val).mp v.property,indexedVolume_density_value hc C P hP v⟩
    have hρZ := indexedCoprodLeft_density F G t.val x.val (fun _ => U.form.value v) hρ
    change (F.coprodFormula G).indexedDensity T
      (indexedCoprodLeft T D E t x).val (fun _ => U.form.value v) at hρZ
    have hDensity := indexedVolume_density_eq hc C Z hZ u _ (hu.symm ▸ hρZ)
    exact ⟨(congrArg A.underlying.obj.value hTarget).trans
      ((rvCoprod_value_left U.underlying.obj V.underlying.obj v).trans (hUV.trans (hStd.symm.trans hZV.symm))),
      (congrArg A.form.value hTarget).trans ((coprod_density_left U V v).trans hDensity)⟩
  · have hu := congrArg Subtype.val he
    change u.val = (indexedCoprodRight T D E t x).val at hu
    let v : V.underlying.obj.domain := ⟨Fin.append t.val x.val,
      (indexedVolume_domain_iff hc C Q hQ _).mpr (by
        simpa only [indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right]
          using And.intro t.property x.property)⟩
    have hImage : (e u).val = rvRightTag (p+a) v.val := by
      change (indexedCoprodEquiv T D E (indexedVolumeCoprodSourceEquiv hc C F G BP Z hZ u)).val = _
      rw [he]
      exact (indexedCoprodEquiv_right T D E t x).trans (rvRightTag_normalize v.val)
    have hTarget : e u = rvCoprodRightMap U.underlying.obj V.underlying.obj v := Subtype.ext hImage
    have hUV := indexedVolume_coordinates hc C Q hQ v
    change V.underlying.obj.value v = indexedVolume BP.totalVolume (fun t => G.object.rowValue (rvValues t)) v.val at hUV
    have hStd := (congrArg
      (indexedVolume BP.totalVolume (fun t => (F.object.coprodFormula G.object).rowValue (rvValues t))) hu).trans
      (indexedCoprodRight_volume F.object G.object T BP.totalVolume t x
        (hF t.val t.property)
        (hG t.val t.property))
    have hρ : G.indexedDensity T v.val (fun _ => V.form.value v) :=
      ⟨(indexedVolume_domain_iff hc C Q hQ v.val).mp v.property,indexedVolume_density_value hc C Q hQ v⟩
    have hρZ := indexedCoprodRight_density F G t.val x.val (fun _ => V.form.value v) hρ
    change (F.coprodFormula G).indexedDensity T
      (indexedCoprodRight T D E t x).val (fun _ => V.form.value v) at hρZ
    have hDensity := indexedVolume_density_eq hc C Z hZ u _ (hu.symm ▸ hρZ)
    exact ⟨(congrArg A.underlying.obj.value hTarget).trans
      ((rvCoprod_value_right U.underlying.obj V.underlying.obj v).trans (hUV.trans (hStd.symm.trans hZV.symm))),
      (congrArg A.form.value hTarget).trans ((coprod_density_right U V v).trans hDensity)⟩

end IntegrationInACVF.Section7
