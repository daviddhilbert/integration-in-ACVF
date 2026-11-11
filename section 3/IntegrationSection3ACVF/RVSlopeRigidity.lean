import IntegrationSection3ACVF.TranslatedErrorGeometry
import IntegrationSection3ACVF.RealAtomicValueBoundRigidity
import IntegrationSection3ACVF.RVSlopePairFormula
import IntegrationSection3ACVF.RVLinearitySlopeValues
import IntegrationSection3ACVF.RVValueBallFamilies
import IntegrationSection3ACVF.NamedBallSetup
import Section3.SmallFiniteParameters

/-! Different actual RV coefficients would give a real-definable error
map on a newly chosen atomic RV fibre. Its strict value bound contradicts
the radius forced by a pair with the different coefficient. The original
source is never assumed atomic after the temporary real names are added. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.RVValueShellGeometry
open IntegrationInACVF.Section3ACVF.TranslatedErrorGeometry

namespace IntegrationInACVF.Section3ACVF.RVSlopeRigidity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem ordered_coefficients_eq {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : FullBaseAtomicity.Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hA : AdjoinBall.AtomicOver B (gammaBall a α true))
    (f : M → M)
    (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (gammaBall a α true) f))
    (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x)) (hinj : Set.InjOn f (gammaBall a α true))
    (s : Values.Gamma (M := M)) (hLinear : GammaLinearity.GammaLinear (gammaBall a α true) f hfVF s)
    (γ η : Values.Gamma (M := M)) (hγη : γ < η) (d e : M)
    (hd : RVSlopeGamma.relation (gammaBall a α true) f γ d)
    (he : RVSlopeGamma.relation (gammaBall a α true) f η e) : d = e := by
  by_contra hde
  have ho : PaperBalls.IsOpenBall (gammaBall a α true) := Or.inr ⟨a,α,rfl⟩
  have hαγ := (GammaSlopeDomain.domain_iff a α γ f hfVF hinj).mp ⟨d,hd⟩
  have hd0 : NonzeroRV d := by
    obtain ⟨t,_,ht⟩ := hd
    exact ht.2.1
  obtain ⟨c,hcRV⟩ := CanonicalRV.encodedRv_surjective (⟨d,hd0.1⟩ : CanonicalRV.RVSort M)
  have hc : iRv c.val = d := congrArg Subtype.val hcRV
  have hdc := RVLinearitySlopeValues.coefficient_value B h00 δ hδ hδ1 a α hA f hf hfVF hinj s hLinear γ d hd
  obtain ⟨hcVal,hcNZ⟩ := RVLinearitySlopeValues.lift_value s d hd0 hdc c hc
  have ha : a.val ∈ gammaBall a α true := BallEnlargementGeometry.gammaBall_centre_mem a α true
  let fa : VFType (M := M) := ⟨f a.val,hfVF _ ha⟩
  have hex : ∃ F : Set M, F.Finite ∧
      @Set.Definable M (B.real ∪ F) LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
        (ImaginaryBaseImages.graphOn (gammaBall a α true) f) := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryParameters.OverBase.specialize hf
  obtain ⟨F,hF,hfReal⟩ := hex
  obtain ⟨tγ,htγ0,htγ⟩ := Values.gamma_has_nonzero_representative γ
  obtain ⟨tδ,htδ0,htδ⟩ := Values.gamma_has_nonzero_representative δ
  let S := B.real ∪ F
  let codes : Fin 6 → M := ![a.val,c.val,fa.val,iVFZero,tγ.val,tδ.val]
  let Q := S ∪ Set.range codes
  let C : FullBaseAtomicity.Base (M := M) := ⟨Q,∅⟩
  have hsmallS : Cardinal.mk S < κ := small_union_finite hκ B.real hsmall F hF
  have hsmallQ : Cardinal.mk Q < κ := small_union_range hκ S hsmallS codes
  have hγC : FullGammaSyntax.Scalar C {γ} :=
    NamedBallSetup.gamma_scalar_of_code h00 C γ tγ htγ0 htγ (Or.inr ⟨4,rfl⟩)
  have hδC : FullGammaSyntax.Scalar C {δ} :=
    NamedBallSetup.gamma_scalar_of_code h00 C δ tδ htδ0 htδ (Or.inr ⟨5,rfl⟩)
  let g : M → M := transformed a.val c.val fa.val f
  have hg : @Set.Definable M Q LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
      (ImaginaryBaseImages.graphOn (TranslationSyntax.domain (gammaBall a α true) a.val) g) := by
    apply graph_definable Q a.val c.val fa.val (Or.inr ⟨0,rfl⟩) (Or.inr ⟨1,rfl⟩)
      (Or.inr ⟨2,rfl⟩) (Or.inr ⟨3,rfl⟩) f
    letI := CanonicalStructure.normalize (M := M)
    exact hfReal.mono Set.subset_union_left
  obtain ⟨i,t,_,htγval,_,hat⟩ := RVValueBallFamilies.exists_atomic_fibre hs C rfl hsmallQ h00 γ hγC
  obtain ⟨r,hrt⟩ := CanonicalRV.encodedRv_surjective t
  have hr : Values.vfValueHom r = γ.val := (congrArg Values.vrv hrt).trans htγval
  have hBall : gammaBall r γ true = fibre t :=
    (gammaBall_eq_fibre r γ hr).trans (congrArg fibre hrt)
  let C' := C.adjoin (Sum.inl i)
  have hAtom : AdjoinBall.AtomicOver C' (gammaBall r γ true) := hBall.symm ▸ hat
  have hδC' : FullGammaSyntax.Scalar C' {δ} :=
    FullBaseAtomicity.OverBase.mono hδC Set.Subset.rfl (Set.subset_insert _ _)
  have hShift (x : VFType (M := M)) (hx : x.val ∈ gammaBall r γ true) :
      (a+x).val ∈ gammaBall a α true :=
    TranslationSyntax.translate_mem a x α γ hαγ
      ((shell_mem x γ).mp (gammaBall_subset_shell r γ hr hx))
  have hGvalue (x : VFType (M := M)) (hx : x.val ∈ gammaBall r γ true) :
      let fx : VFType (M := M) := ⟨f (a+x).val,hfVF _ (hShift x hx)⟩
      g x.val = (fx-fa-c*x).val := transformed_vf a c fa x f hfVF (hShift x hx)
  have hgVF : ∀ x ∈ gammaBall r γ true, iVF (g x) := by
    intro x hx
    let xx : VFType (M := M) := ⟨x,hx.1⟩
    rw [hGvalue xx hx]
    exact (⟨f (a+xx).val,hfVF _ (hShift xx hx)⟩-fa-c*xx : VFType (M := M)).property
  have hsub : gammaBall r γ true ⊆ TranslationSyntax.domain (gammaBall a α true) a.val := by
    intro x hx
    refine ⟨hx.1,?_⟩
    rw [TranslationSyntax.input_vf a (⟨x,hx.1⟩ : VFType (M := M))]
    exact hShift ⟨x,hx.1⟩ hx
  have hBound (x : VFType (M := M)) (hx : x.val ∈ gammaBall r γ true) :
      s.val * γ.val < Values.vfValueHom (⟨g x.val,hgVF _ hx⟩ : VFType (M := M)) := by
    have hxγ := (shell_mem x γ).mp (gammaBall_subset_shell r γ hr hx)
    have hxNZ : x ≠ 0 := by
      intro hz
      have hi : Values.vfValueHom x = Values.infinity := by
        rw [hz,map_zero]
        exact Values.infinity_eq_zero.symm
      exact γ.property (hxγ.symm.trans hi)
    let fx : VFType (M := M) := ⟨f (a+x).val,hfVF _ (hShift x hx)⟩
    have hAx : Values.vfValueHom ((a+x)-a) = γ.val := by simpa only [add_sub_cancel_left] using hxγ
    have hRV : CanonicalRV.encodedRv (fx-fa) = CanonicalRV.encodedRv (c*x) := by
      simpa only [add_sub_cancel_left] using
        RVSlopePairFormula.pair_eq B h00 δ hδ hδ1 ho hA f hf hfVF hinj γ d hd c hc a (a+x) ha (hShift x hx) hAx
    have hVal := strict_value c fa x fx hcNZ hxNZ hRV
    rw [hcVal,hxγ] at hVal
    have heq : (⟨g x.val,hgVF _ hx⟩ : VFType (M := M)) = fx-fa-c*x := Subtype.ext (hGvalue x hx)
    rw [heq]
    exact hVal
  obtain ⟨u,v,hu,hv,hvu,hVal⟩ := GammaDifferenceRealization.exists_pair r γ η hγη
  let fu : VFType (M := M) := ⟨f (a+u).val,hfVF _ (hShift u hu)⟩
  let fv : VFType (M := M) := ⟨f (a+v).val,hfVF _ (hShift v hv)⟩
  have hDiff : (a+v)-(a+u) = v-u := by ring
  have hPairVal : Values.vfValueHom ((a+v)-(a+u)) = η.val := by rw [hDiff,hVal]
  have hEne : e ≠ iRv c.val := by
    rw [hc]
    exact Ne.symm hde
  have hRVne : CanonicalRV.encodedRv (fv-fu) ≠ CanonicalRV.encodedRv (c*(v-u)) := by
    simpa only [hDiff] using
      RVSlopePairFormula.pair_ne B h00 δ hδ hδ1 ho hA f hf hfVF hinj η e he c hEne
        (a+u) (a+v) (hShift u hu) (hShift v hv) hPairVal
  have hSame : Values.vfValueHom (fv-fu) = Values.vfValueHom (c*(v-u)) := by
    have hLin := hLinear (a+u) (a+v) (hShift u hu) (hShift v hv)
    change Values.vfValueHom (fv-fu) = s.val * Values.vfValueHom ((a+v)-(a+u)) at hLin
    rw [hDiff] at hLin
    rw [map_mul,hcVal]
    exact hLin
  have hErr := pair_value c fa u v fu fv hcNZ hvu hSame hRVne
  rw [hcVal] at hErr
  let gu : VFType (M := M) := ⟨g u.val,hgVF _ hu⟩
  let gv : VFType (M := M) := ⟨g v.val,hgVF _ hv⟩
  have hGu : gu = fu-fa-c*u := Subtype.ext (hGvalue u hu)
  have hGv : gv = fv-fa-c*v := Subtype.ext (hGvalue v hv)
  apply RealAtomicValueBoundRigidity.impossible hκ hs C' hsmallQ h00 δ hδC' hδ1 r γ hAtom
    hsub g hg hgVF s hBound u v hu hv hvu
  change Values.vfValueHom (gv-gu) = s.val * Values.vfValueHom (v-u)
  rw [hGu,hGv]
  exact hErr

end IntegrationInACVF.Section3ACVF.RVSlopeRigidity
