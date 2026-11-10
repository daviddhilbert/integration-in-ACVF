import IntegrationSection3ACVF.BetaSubballFamilies
import IntegrationSection3ACVF.RVIntegerOrbits
import IntegrationSection3ACVF.OpenBallRVGeometry

/-! Actual nonzero RV fibres and infinite RV images of value shells. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.RVValueShellGeometry

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def fibre (t : CanonicalRV.RVSort M) : Set M := {x | iVF x ∧ iRv x = t.val}

def shell (γ : Values.Gamma (M := M)) : Set M :=
  {x | iVF x ∧ iRv x ∈ Values.gammaPullback {γ}}

theorem shell_mem (r : VFType (M := M)) (γ : Values.Gamma (M := M)) :
    r.val ∈ shell γ ↔ Values.vfValueHom r = γ.val := by
  constructor
  · rintro ⟨_,hRV,h0,he⟩
    exact congrArg Subtype.val he
  · intro he
    have h0 : iRv r.val ≠ iRVZero := by
      intro hz
      have hInf : Values.vfValueHom r = Values.infinity :=
        (Values.vrv_eq_infinity_iff (CanonicalRV.encodedRv r)).mpr hz
      exact γ.property (he.symm.trans hInf)
    exact ⟨r.property,rv_mem hM r.property,h0,Subtype.ext he⟩

theorem gammaBall_eq_fibre (r : VFType (M := M)) (γ : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = γ.val) :
    gammaBall r γ true = fibre (CanonicalRV.encodedRv r) := by
  have hr0 : r ≠ 0 := by
    intro he
    have hz : Values.vfValueHom r = Values.infinity := by
      rw [he,map_zero]
      exact Values.infinity_eq_zero.symm
    exact γ.property (hr.symm.trans hz)
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  ext x
  constructor
  · intro hx
    let x' : VFType (M := M) := ⟨x,hx.1⟩
    have hlt := (GammaCosetGeometry.gammaBall_mem_valuation v hv r r γ hr x').mp hx
    refine ⟨x'.property,?_⟩
    apply (CanonicalRV.encoded_eq_iff_close x'.property r.property
      (fun he => hr0 (Subtype.ext he))).mpr
    intro hp
    exact not_le_of_gt hlt ((hv r (x'-r)).mp hp)
  · rintro ⟨hx,he⟩
    let x' : VFType (M := M) := ⟨x,hx⟩
    have hn := (CanonicalRV.encoded_eq_iff_close x'.property r.property
      (fun hz => hr0 (Subtype.ext hz))).mp he
    apply (GammaCosetGeometry.gammaBall_mem_valuation v hv r r γ hr x').mpr
    exact lt_of_not_ge (fun h => hn ((hv r (x'-r)).mpr h))

theorem gammaBall_subset_shell (r : VFType (M := M)) (γ : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = γ.val) : gammaBall r γ true ⊆ shell γ := by
  rw [gammaBall_eq_fibre r γ hr]
  rintro x ⟨hx,he⟩
  apply (shell_mem (⟨x,hx⟩ : VFType (M := M)) γ).mpr
  exact (congrArg Values.vrv (Subtype.ext he :
    CanonicalRV.encodedRv (⟨x,hx⟩ : VFType (M := M)) = CanonicalRV.encodedRv r)).trans hr

theorem rv_image_infinite (h00 : M ⊨ Axioms.ACVF00) (γ : Values.Gamma (M := M)) :
    (CanonicalRV.encodedRv '' {x : VFType (M := M) | x.val ∈ shell γ}).Infinite := by
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative γ
  have hr0 : r ≠ 0 := by
    intro he
    have hz : Values.vfValueHom r = Values.infinity := by
      rw [he,map_zero]
      exact Values.infinity_eq_zero.symm
    exact γ.property (hr.symm.trans hz)
  have hInf := Set.infinite_range_of_injective (RVIntegerOrbits.orbit_injective h00 r hr0)
  apply hInf.mono
  rintro t ⟨n,rfl⟩
  refine ⟨((n+1 : ℕ) : VFType (M := M))*r,?_,rfl⟩
  exact (shell_mem _ γ).mpr ((RVIntegerOrbits.orbit_value h00 r n).trans hr)

end IntegrationInACVF.Section3ACVF.RVValueShellGeometry
