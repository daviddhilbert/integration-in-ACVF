import Integration7.HKZeroVolumeIntegration
import Integration7.OrdinaryZeroLiftCoproducts
import Integration7.VolumeFormGluing

/-! The concrete coproduct of arbitrary weighted zero VF presentations
glues their actual forms on the two disjoint tagged images. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def zeroVFCoprod (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A B : ZeroVFVolumeObject (M := M) (C.base : Set M)) : ZeroVFVolumeObject (M := M) (C.base : Set M) where
  underlying := vfFiniteCoprodObject hc C.saturated C.small (rawRVSpace (M := M) 1)
    (rawRVSpace_rvCoded 1) A.underlying B.underlying
  form := (A.form.pullback (mixedUntagLeft A.underlying.obj.obj.set
    B.underlying.obj.obj.index.1 B.underlying.obj.obj.index.2)).union
    (B.form.pullback (mixedUntagRight B.underlying.obj.obj.set
      A.underlying.obj.obj.index.1 A.underlying.obj.obj.index.2))

def zeroVFCoprodLeftMap (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A B : ZeroVFVolumeObject (M := M) (C.base : Set M)) :
    Map A.underlying.obj.obj.set (zeroVFCoprod hc C A B).underlying.obj.obj.set :=
  vfAllCoprodInl A.underlying.obj.obj B.underlying.obj.obj

def zeroVFCoprodRightMap (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A B : ZeroVFVolumeObject (M := M) (C.base : Set M)) :
    Map B.underlying.obj.obj.set (zeroVFCoprod hc C A B).underlying.obj.obj.set :=
  vfAllCoprodInr A.underlying.obj.obj B.underlying.obj.obj

theorem zero_vf_coprod_cases (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A B : ZeroVFVolumeObject (M := M) (C.base : Set M))
    (w : (zeroVFCoprod hc C A B).underlying.obj.obj.set) :
    (∃ u, zeroVFCoprodLeftMap hc C A B u = w) ∨ (∃ v, zeroVFCoprodRightMap hc C A B v = w) := by
  rcases w.property with ⟨u,hu⟩ | ⟨v,hv⟩
  · exact Or.inl ⟨u,Subtype.ext hu⟩
  · exact Or.inr ⟨v,Subtype.ext hv⟩

theorem zero_vf_coprod_density_left (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A B : ZeroVFVolumeObject (M := M) (C.base : Set M)) (u : A.underlying.obj.obj.set) :
    (zeroVFCoprod hc C A B).form.value (zeroVFCoprodLeftMap hc C A B u) = A.form.value u := by
  change (((A.form.map.comp (mixedUntagLeft A.underlying.obj.obj.set
    B.underlying.obj.obj.index.1 B.underlying.obj.obj.index.2)).union
      (B.form.map.comp (mixedUntagRight B.underlying.obj.obj.set
        A.underlying.obj.obj.index.1 A.underlying.obj.obj.index.2)))
      ⟨((mixedLeftTagMap A.underlying.obj.obj.set
        B.underlying.obj.obj.index.1 B.underlying.obj.obj.index.2).toImage u).val,
        Or.inl ((mixedLeftTagMap A.underlying.obj.obj.set
          B.underlying.obj.obj.index.1 B.underlying.obj.obj.index.2).toImage u).property⟩).val 0 = _
  rw [Map.union_on_left]
  exact congrArg A.form.value (Map.inverse_apply _ _ u)

theorem zero_vf_coprod_density_right (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A B : ZeroVFVolumeObject (M := M) (C.base : Set M)) (v : B.underlying.obj.obj.set) :
    (zeroVFCoprod hc C A B).form.value (zeroVFCoprodRightMap hc C A B v) = B.form.value v := by
  change (((A.form.map.comp (mixedUntagLeft A.underlying.obj.obj.set
    B.underlying.obj.obj.index.1 B.underlying.obj.obj.index.2)).union
      (B.form.map.comp (mixedUntagRight B.underlying.obj.obj.set
        A.underlying.obj.obj.index.1 A.underlying.obj.obj.index.2)))
      ⟨((mixedRightTagMap B.underlying.obj.obj.set
        A.underlying.obj.obj.index.1 A.underlying.obj.obj.index.2).toImage v).val,
        Or.inr ((mixedRightTagMap B.underlying.obj.obj.set
          A.underlying.obj.obj.index.1 A.underlying.obj.obj.index.2).toImage v).property⟩).val 0 = _
  rw [Map.union_on_right _ _ (mixedTaggedImages_disjoint A.underlying.obj.obj.set B.underlying.obj.obj.set)]
  exact congrArg B.form.value (Map.inverse_apply _ _ v)

end IntegrationInACVF.Section7.HK
