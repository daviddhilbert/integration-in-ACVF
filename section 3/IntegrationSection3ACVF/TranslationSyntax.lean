import IntegrationSection3ACVF.RealGraphOperations
import IntegrationSection3ACVF.GammaCosetGeometry

/-! Translation of a partial-domain VF map through an actual named point. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.TranslationSyntax

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def input (e x : M) : M := @iVFAdd M (CanonicalStructure.normalize (M := M)) e x

def domain (D : Set M) (e : M) : Set M := {x | iVF x ∧ input e x ∈ D}

theorem input_vf (e x : VFType (M := M)) : input e.val x.val = (e+x).val :=
  CanonicalStructure.normalize_fun Fn.vfAdd ![e.val,x.val] (fun j => by
    fin_cases j
    · exact e.property
    · exact x.property)

theorem graph_definable (S : Set M) (e : M) (he : e ∈ S)
    {D : Set M} (f : M → M)
    (hf : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
      (ImaginaryBaseImages.graphOn D f)) :
    @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
      (ImaginaryBaseImages.graphOn (domain D e) (fun x => f (input e x))) := by
  let E := @input M sM
  let D' := @domain M sM D e
  have hs := ((@definableAt_iff_normalized_raw M sM hM S .vf _).mp
    (@definableAt_sort M sM S .vf)).1
  let N := @CanonicalStructure.normalize M sM
  letI := N
  have hShift : S.DefinableFun LRV (fun z : Fin 2 → M => E e (z 0)) := by
    have hadd : S.DefinableFun LRV (Structure.funMap (L := LRV) Fn.vfAdd) :=
      Set.DefinableFun.of_empty (@Set.DefinableFun.fun_symbol M LRV N 2 Fn.vfAdd)
    exact Set.DefinableFun.comp (g := fun z : Fin 2 → M => ![e,z 0])
      (fun j => by
        fin_cases j
        · exact LRV.definableFun_const (Fin 2) he
        · exact Set.DefinableFun.proj LRV) hadd
  have hm : S.DefinableMap LRV (fun z : Fin 2 → M => ![E e (z 0),z 1]) := by
    intro j
    fin_cases j
    · exact hShift
    · exact Set.DefinableFun.proj LRV
  have hd := (hs.preimage_comp (fun _ : Fin 1 => (0 : Fin 2))).inter (hf.preimage_map hm)
  change S.Definable LRV (ImaginaryBaseImages.graphOn D' (fun x => f (E e x)))
  convert hd using 1
  ext z
  change ((@iVF M sM (z 0) ∧ E e (z 0) ∈ D) ∧ z 1 = f (E e (z 0))) ↔
    (@iVF M sM (z 0) ∧ E e (z 0) ∈ D ∧ z 1 = f (E e (z 0)))
  exact and_assoc

theorem translate_mem (a r : VFType (M := M)) (α γ : Values.Gamma (M := M))
    (hαγ : α < γ) (hr : Values.vfValueHom r = γ.val) :
    (a+r).val ∈ gammaBall a α true := by
  have he : (a+r)-a = r := by ring
  have hv : Values.vfValueHom ((a+r)-a) = γ.val := (congrArg Values.vfValueHom he).trans hr
  change ∃ h : iVF (a+r).val, α.val ≤ Values.vfValueHom ((a+r)-a) ∧
    (true = true → ¬ Values.vfValueHom ((a+r)-a) ≤ α.val)
  refine ⟨(a+r).property,hv.symm ▸ hαγ.le,?_⟩
  intro _ h
  have h' : γ.val ≤ α.val := hv ▸ h
  exact not_le_of_gt hαγ h'

end IntegrationInACVF.Section3ACVF.TranslationSyntax
