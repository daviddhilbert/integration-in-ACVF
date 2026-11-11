import IntegrationSection3ACVF.AnnulusValueIntervals
import IntegrationSection3ACVF.RVValueShellGeometry
import IntegrationSection3ACVF.MaximalOpenClasses

/-! The maximal open balls in a radial VF set avoiding its centre are
exactly the translated nonzero RV fibres. This applies to actual punctured
closed/open balls and retains all endpoint cases in their value domains. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RadialOpenClasses

open GammaRadiusAtomicity AnnulusValueIntervals

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

private noncomputable def relative (x a : VFType (M := M)) : VFType (M := M) := x-a

def domain (a : VFType (M := M)) (V : Set (Values.GammaTop (M := M))) : Set M :=
  {z | ∃ hz : iVF z, @Values.vfValueHom M sM hM (relative (⟨z,hz⟩ : @VFType M sM) a) ∈ V}

def classAt (a x : VFType (M := M)) : Set M :=
  {z | ∃ hz : iVF z, @iRv M sM ((relative (⟨z,hz⟩ : @VFType M sM) a).val) = @iRv M sM (x-a).val}

theorem mem_domain (a x : VFType (M := M)) (V : Set (Values.GammaTop (M := M))) :
    x.val ∈ domain a V ↔ Values.vfValueHom (x-a) ∈ V :=
  ⟨fun ⟨_,h⟩ => h,fun h => ⟨x.property,h⟩⟩

theorem centre_not_mem (a : VFType (M := M)) (V : Set (Values.GammaTop (M := M)))
    (hV : Values.infinity ∉ V) : a.val ∉ domain a V := by
  intro h
  have h' := (mem_domain a a V).mp h
  rw [sub_self,map_zero,← Values.infinity_eq_zero] at h'
  exact hV h'

theorem mem_class_self (a x : VFType (M := M)) : x.val ∈ classAt a x := ⟨x.property,rfl⟩

theorem class_eq_gammaBall (a x : VFType (M := M)) (hxa : x ≠ a) :
    ∃ γ : Values.Gamma (M := M), Values.vfValueHom (x-a) = γ.val ∧
      classAt a x = gammaBall x γ true := by
  have hγ : Values.vfValueHom (x-a) ≠ Values.infinity := by
    intro he
    have hz := (Values.vrv_eq_infinity_iff (CanonicalRV.encodedRv (x-a))).mp he
    exact sub_ne_zero.mpr hxa ((CanonicalRV.encodedRv_zero_iff (x-a)).mp hz)
  let γ : Values.Gamma (M := M) := ⟨Values.vfValueHom (x-a),hγ⟩
  refine ⟨γ,rfl,?_⟩
  have hF := RVValueShellGeometry.gammaBall_eq_fibre (x-a) γ rfl
  ext z
  by_cases hz : iVF z
  · let zz : VFType (M := M) := ⟨z,hz⟩
    have hShift : (zz-a).val ∈ gammaBall (x-a) γ true ↔ z ∈ gammaBall x γ true := by
      rw [@AnnulusValueIntervals.mem_open M sM hM (x-a) (zz-a) γ,
        @AnnulusValueIntervals.mem_open M sM hM x zz γ]
      rw [show (zz-a)-(x-a) = zz-x by ring]
    rw [← hShift,hF]
    change (∃ hz' : @iVF M sM z, @iRv M sM ((relative (⟨z,hz'⟩ : @VFType M sM) a).val) = @iRv M sM (x-a).val) ↔
      (iVF (zz-a).val ∧ iRv (zz-a).val = iRv (x-a).val)
    exact ⟨fun ⟨_,h⟩ => ⟨(zz-a).property,h⟩,fun h => ⟨hz,h.2⟩⟩
  · exact ⟨fun h => (hz h.choose).elim,fun h => (hz h.choose).elim⟩

theorem class_open (a x : VFType (M := M)) (hxa : x ≠ a) : PaperBalls.IsOpenBall (classAt a x) := by
  obtain ⟨γ,_,he⟩ := class_eq_gammaBall a x hxa
  exact Or.inr ⟨x,γ,he⟩

theorem class_subset (a x : VFType (M := M)) (V : Set (Values.GammaTop (M := M)))
    (hx : x.val ∈ domain a V) : classAt a x ⊆ domain a V := by
  rintro z ⟨hz,he⟩
  let zz : VFType (M := M) := ⟨z,hz⟩
  have hv : Values.vfValueHom (zz-a) = Values.vfValueHom (x-a) :=
    congrArg Values.vrv (Subtype.ext he : CanonicalRV.encodedRv (zz-a) = CanonicalRV.encodedRv (x-a))
  exact ⟨hz,hv.symm ▸ (mem_domain a x V).mp hx⟩

theorem open_subset_class (a : VFType (M := M)) (V : Set (Values.GammaTop (M := M)))
    (hV : Values.infinity ∉ V) {E : Set M} (hOpen : PaperBalls.IsOpenBall E)
    (hED : E ⊆ domain a V) (x : VFType (M := M)) (hx : x.val ∈ E) : E ⊆ classAt a x := by
  have ha : a.val ∉ E := fun he => centre_not_mem a V hV (hED he)
  intro z hz
  have hzVF : iVF z := (hED hz).choose
  exact ⟨hzVF,OpenBallRVGeometry.rv_sub_constant hOpen a ⟨z,hzVF⟩ x ha hz hx⟩

theorem class_maximal (a x : VFType (M := M)) (V : Set (Values.GammaTop (M := M)))
    (hV : Values.infinity ∉ V) (hx : x.val ∈ domain a V) :
    MaximalOpenClasses.IsMaximal (domain a V) (classAt a x) := by
  have hxa : x ≠ a := fun he => centre_not_mem a V hV (he ▸ hx)
  refine ⟨class_open a x hxa,class_subset a x V hx,?_⟩
  intro E hE hCE hED
  exact open_subset_class a V hV hE hED x (hCE (mem_class_self a x))

theorem maximal_eq_class (a : VFType (M := M)) (V : Set (Values.GammaTop (M := M)))
    (hV : Values.infinity ∉ V) (E : Set M) (hE : MaximalOpenClasses.IsMaximal (domain a V) E)
    (x : VFType (M := M)) (hx : x.val ∈ E) : E = classAt a x := by
  have hSub := open_subset_class a V hV hE.1 hE.2.1 x hx
  have hDx := hE.2.1 hx
  have hxa : x ≠ a := fun he => centre_not_mem a V hV (he ▸ hDx)
  exact Set.Subset.antisymm hSub (hE.2.2 (classAt a x) (class_open a x hxa) hSub (class_subset a x V hDx))

end IntegrationInACVF.Section3ACVF.RadialOpenClasses
