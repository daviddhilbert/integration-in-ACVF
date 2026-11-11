import IntegrationSection3ACVF.RadialOpenClasses
import IntegrationSection3ACVF.RVDifferencePairs
import IntegrationSection3.SurjectiveQuotientMap

/-! Open-to-open bijections of actual radial VF sets induce bijections
of translated RV classes. The complete existential quotient graph is
proved as part of the conclusion. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RadialClassMaps

open RadialOpenClasses

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem class_image (a b : VFType (M := M)) (V W : Set (Values.GammaTop (M := M)))
    (hV : Values.infinity ∉ V) (hW : Values.infinity ∉ W) (f : M → M)
    (hbij : Set.BijOn f (domain a V) (domain b W))
    (hoo : MaximalOpenClasses.OpenToOpen (domain a V) f)
    (x fx : VFType (M := M)) (hx : x.val ∈ domain a V) (hfx : fx.val = f x.val) :
    f '' classAt a x = classAt b fx := by
  have hMax := MaximalOpenClasses.image_maximal f hbij hoo (class_maximal a x V hV hx)
  exact maximal_eq_class b W hW (f '' classAt a x) hMax fx ⟨x.val,mem_class_self a x,hfx.symm⟩

theorem rv_kernel (a b : VFType (M := M)) (V W : Set (Values.GammaTop (M := M)))
    (hV : Values.infinity ∉ V) (hW : Values.infinity ∉ W) (f : M → M)
    (hbij : Set.BijOn f (domain a V) (domain b W))
    (hoo : MaximalOpenClasses.OpenToOpen (domain a V) f)
    (x y fx fy : VFType (M := M)) (hx : x.val ∈ domain a V) (hy : y.val ∈ domain a V)
    (hfx : fx.val = f x.val) (hfy : fy.val = f y.val) :
    iRv (x-a).val = iRv (y-a).val ↔ iRv (fx-b).val = iRv (fy-b).val := by
  have he := class_image a b V W hV hW f hbij hoo x fx hx hfx
  constructor
  · intro hxy
    have hyC : y.val ∈ classAt a x := ⟨y.property,hxy.symm⟩
    have hfyC : fy.val ∈ classAt b fx := (Set.ext_iff.mp he fy.val).mp ⟨y.val,hyC,hfy.symm⟩
    exact hfyC.choose_spec.symm
  · intro hxy
    have hfyC : fy.val ∈ classAt b fx := ⟨fy.property,hxy.symm⟩
    obtain ⟨z,hz,hfz⟩ := (Set.ext_iff.mp he fy.val).mpr hfyC
    have hzy : z = y.val := hbij.2.1 (class_subset a x V hx hz) hy (hfz.trans hfy)
    have hyC : y.val ∈ classAt a x := hzy ▸ hz
    exact hyC.choose_spec.symm

theorem exists_rv_bijection (a b : VFType (M := M)) (V W : Set (Values.GammaTop (M := M)))
    (hV : Values.infinity ∉ V) (hW : Values.infinity ∉ W) (f : M → M)
    (hbij : Set.BijOn f (domain a V) (domain b W))
    (hoo : MaximalOpenClasses.OpenToOpen (domain a V) f) :
    ∃ g : M → M,
      Set.BijOn g ((fun x => RVDifferencePairs.difference x a.val) '' domain a V)
        ((fun y => RVDifferencePairs.difference y b.val) '' domain b W) ∧
      (∀ x ∈ domain a V, g (RVDifferencePairs.difference x a.val) = RVDifferencePairs.difference (f x) b.val) ∧
      ∀ u v, (u ∈ ((fun x => RVDifferencePairs.difference x a.val) '' domain a V) ∧ v = g u) ↔
        ∃ x ∈ domain a V, RVDifferencePairs.difference x a.val = u ∧ RVDifferencePairs.difference (f x) b.val = v := by
  let p : M → M := fun x => RVDifferencePairs.difference x a.val
  let q : M → M := fun y => RVDifferencePairs.difference y b.val
  have hp : (domain a V).MapsTo p (p '' domain a V) ∧ (domain a V).SurjOn p (p '' domain a V) :=
    ⟨fun x hx => ⟨x,hx,rfl⟩,fun _ hy => hy⟩
  have hq : (domain b W).MapsTo q (q '' domain b W) ∧ (domain b W).SurjOn q (q '' domain b W) :=
    ⟨fun y hy => ⟨y,hy,rfl⟩,fun _ hy => hy⟩
  have hker (x : M) (hx : x ∈ domain a V) (y : M) (hy : y ∈ domain a V) :
      p x = p y ↔ q (f x) = q (f y) := by
    let xx : VFType (M := M) := ⟨x,hx.choose⟩
    let yy : VFType (M := M) := ⟨y,hy.choose⟩
    let fx : VFType (M := M) := ⟨f x,(hbij.1 hx).choose⟩
    let fy : VFType (M := M) := ⟨f y,(hbij.1 hy).choose⟩
    have h := rv_kernel a b V W hV hW f hbij hoo xx yy fx fy hx hy rfl rfl
    change RVDifferencePairs.difference xx.val a.val = RVDifferencePairs.difference yy.val a.val ↔
      RVDifferencePairs.difference fx.val b.val = RVDifferencePairs.difference fy.val b.val
    rw [RVDifferencePairs.difference_vf,RVDifferencePairs.difference_vf,
      RVDifferencePairs.difference_vf,RVDifferencePairs.difference_vf]
    exact h
  letI : Inhabited M := ⟨iRVZero⟩
  exact SurjectiveQuotientMap.exists_bijective_factor f hbij p q hp hq hker

end IntegrationInACVF.Section3ACVF.RadialClassMaps
