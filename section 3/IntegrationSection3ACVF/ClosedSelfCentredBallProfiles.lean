import IntegrationSection3ACVF.ClosedCompleteTypeRVProfiles
import IntegrationSection3ACVF.BallKindPredicates
import IntegrationSection3ACVF.FullBaseDefinability
import IntegrationSection3ACVF.BallEnlargementGeometry

/-! Replace the centre of a named closed ball by the point being tested.
The radius stays an RV variable, so one VF variable remains in the profile.
All valid real codes are quantified; no centre is named in the base. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.ClosedSelfCentredBallProfiles

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def selfCode (x r : M) : Fin 4 → M := ![x,r,iVFOne,iVFZero]

noncomputable def profile (P : BallImaginaries.Ball M → Set M) : Set (Fin 2 → M) :=
  {z | ∃ r : M, @iRv M (@CanonicalStructure.normalize M sM) r = z 1 ∧
    Sum.elim (selfCode (z 0) r) (fun _ : Fin 1 => z 0) ∈
      (@BallPresentation.presentation M sM hM).relationPullback P}

theorem definable (B : FullBaseAtomicity.Base (M := M))
    (P : BallImaginaries.Ball M → Set M) (hP : FullBaseAtomicity.Relation B P) :
    FullBaseAtomicity.OverBase B (profile P) := by
  let F := fun z : Fin 2 ⊕ Fin 1 → M =>
    Sum.elim (@selfCode M sM (z (.inl 0)) (z (.inr 0))) (fun _ : Fin 1 => z (.inl 0))
  have hz : @iVFZero M (@CanonicalStructure.normalize M sM) = @iVFZero M sM :=
    @CanonicalStructure.sortZero_normalize M sM .vf
  have ho : @iVFOne M (@CanonicalStructure.normalize M sM) = @iVFOne M sM :=
    @CanonicalStructure.normalize_fun M sM 0 Fn.vfOne Fin.elim0 (fun j => j.elim0)
  have hF : @Set.DefinableMap M LRV (@CanonicalStructure.normalize M sM)
      (Fin 2 ⊕ Fin 1) (Fin 4 ⊕ Fin 1) B.real F := by
    letI := @CanonicalStructure.normalize M sM
    have hzero : B.real.DefinableFun LRV (fun _ : Fin 2 ⊕ Fin 1 → M => @iVFZero M sM) := by
      rw [← hz]
      exact SpecialTransformations.DefinableConstants.constant
        (SpecialTransformations.DefinableConstants.function_symbol
          (L := LRV) Fn.vfZero Fin.elim0 (fun j => j.elim0))
    have hone : B.real.DefinableFun LRV (fun _ : Fin 2 ⊕ Fin 1 → M => @iVFOne M sM) := by
      rw [← ho]
      exact SpecialTransformations.DefinableConstants.constant
        (SpecialTransformations.DefinableConstants.function_symbol
          (L := LRV) Fn.vfOne Fin.elim0 (fun j => j.elim0))
    intro j
    cases j with
    | inl j =>
      fin_cases j
      · exact Set.DefinableFun.proj LRV
      · exact Set.DefinableFun.proj LRV
      · exact hone
      · exact hzero
    | inr j => exact Set.DefinableFun.proj LRV
  have hEq : FullBaseAtomicity.OverBase B {z : Fin 2 ⊕ Fin 1 → M |
      @iRv M (@CanonicalStructure.normalize M sM) (z (.inr 0)) = z (.inl 1)} := by
    apply FullBaseAtomicity.OverBase.of_real
    letI := @CanonicalStructure.normalize M sM
    have hr : B.real.DefinableFun LRV
        (fun z : Fin 2 ⊕ Fin 1 → M => iRv (z (.inr 0))) := by
      exact Set.DefinableFun.comp (g := fun z : Fin 2 ⊕ Fin 1 → M => ![z (.inr 0)])
        (fun j => by fin_cases j; exact Set.DefinableFun.proj LRV)
        (Set.DefinableFun.of_empty
          (@Set.DefinableFun.fun_symbol M LRV (@CanonicalStructure.normalize M sM) 1 Fn.rvMap))
    exact hr.ofPred_eq (Set.DefinableFun.proj LRV)
  have hd := FullBaseAtomicity.OverBase.exists_block
    (FullBaseAtomicity.OverBase.inter hEq (FullBaseAtomicity.OverBase.preimage_map hP hF))
  apply FullBaseAtomicity.OverBase.congr hd
  intro z
  change (∃ r : Fin 1 → M, @iRv M (@CanonicalStructure.normalize M sM) (r 0) = z 1 ∧
    Sum.elim (selfCode (z 0) (r 0)) (fun _ : Fin 1 => z 0) ∈
      (@BallPresentation.presentation M sM hM).relationPullback P) ↔ _
  exact ⟨fun ⟨r,h1,h2⟩ => ⟨r 0,h1,h2⟩,fun ⟨r,h1,h2⟩ => ⟨![r],h1,h2⟩⟩

theorem centre_change (a x : VFType (M := M)) (α : Values.Gamma (M := M))
    (hx : x.val ∈ gammaBall a α false) : gammaBall x α false = gammaBall a α false := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative α
  have hm (b u : VFType (M := M)) : u.val ∈ gammaBall b α false ↔ v (u-b) ≤ v r :=
    BallKindPredicates.gammaBall_mem_valuation_closed v hv b r α hr u
  have hxv : v (x-a) ≤ v r := (hm a x).mp hx
  ext z
  by_cases hz : iVF z
  · let zz : VFType (M := M) := ⟨z,hz⟩
    constructor
    · intro h
      apply (hm a zz).mpr
      have hzx : v (zz-x) ≤ v r := (hm x zz).mp h
      have he : (zz-x)+(x-a) = zz-a := by ring
      simpa only [he] using v.map_add_le hzx hxv
    · intro h
      apply (hm x zz).mpr
      have hza : v (zz-a) ≤ v r := (hm a zz).mp h
      have he : (zz-a)-(x-a) = zz-x := by ring
      simpa only [he] using v.map_sub_le hza hxv
  · exact ⟨fun h => (hz h.1).elim,fun h => (hz h.1).elim⟩

theorem decode_self (x r : VFType (M := M))
    (α : Values.Gamma (M := M)) (hr : Values.vfValueHom r = α.val) :
    ∃ h : selfCode x.val r.val ∈ BallPresentation.codeDomain,
      BallImaginaries.underlying (BallPresentation.decode ⟨selfCode x.val r.val,h⟩) = gammaBall x α false := by
  let q : ClosedBallCodes.Code M := ⟨![x.val,r.val,iVFOne],by
    intro j
    fin_cases j
    · exact x.property
    · exact r.property
    · exact (1 : VFType (M := M)).property⟩
  have hOne : iVFOne (M := M) ≠ iVFZero := by
    intro he
    exact (one_ne_zero : (1 : VFType (M := M)) ≠ 0) (Subtype.ext he)
  refine ⟨(BallPresentation.encodeClosed q).property,?_⟩
  change BallImaginaries.underlying (BallPresentation.decode (BallPresentation.encodeClosed q)) = _
  rw [BallPresentation.decode_encodeClosed]
  exact BallKindGeometry.closed_raw_gammaBall q hOne α hr

theorem profile_mem (P : BallImaginaries.Ball M → Set M)
    (i : BallImaginaries.Ball M) (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hi : BallImaginaries.underlying i = gammaBall a α false)
    (hr : Values.vfValueHom r = α.val)
    (x : VFType (M := M)) (hx : x.val ∈ BallImaginaries.underlying i) :
    ![x.val,iRv r.val] ∈ profile P ↔ x.val ∈ P i := by
  have hxBall : x.val ∈ gammaBall a α false := hi ▸ hx
  have hCent := centre_change a x α hxBall
  constructor
  · rintro ⟨s,hRV,hs,hPs⟩
    have hClosed : ∀ j : Fin 3, iVF (BallPresentation.closedTuple (selfCode x.val s) j) :=
      (hs.resolve_right (fun h => h.1 rfl)).2
    let ss : VFType (M := M) := ⟨s,hClosed 1⟩
    have hNorm : @iRv M (@CanonicalStructure.normalize M sM) ss.val = iRv ss.val :=
      CanonicalStructure.normalize_fun Fn.rvMap ![ss.val] (fun j => by fin_cases j; exact ss.property)
    have hRaw : iRv ss.val = iRv r.val := hNorm.symm.trans hRV
    have hsVal : Values.vfValueHom ss = α.val :=
      (congrArg Values.vrv (Subtype.ext hRaw : CanonicalRV.encodedRv ss = CanonicalRV.encodedRv r)).trans hr
    obtain ⟨hs',he⟩ := decode_self x ss α hsVal
    have hEq : BallPresentation.decode ⟨selfCode x.val ss.val,hs'⟩ = i :=
      BallImaginaries.underlying_injective (he.trans (hCent.trans hi.symm))
    change x.val ∈ P (BallPresentation.decode ⟨selfCode x.val ss.val,hs'⟩) at hPs
    rwa [hEq] at hPs
  · intro hxP
    obtain ⟨hs,he⟩ := decode_self x r α hr
    have hEq : BallPresentation.decode ⟨selfCode x.val r.val,hs⟩ = i :=
      BallImaginaries.underlying_injective (he.trans (hCent.trans hi.symm))
    refine ⟨r.val,?_,hs,?_⟩
    · exact CanonicalStructure.normalize_fun Fn.rvMap ![r.val] (fun j => by fin_cases j; exact r.property)
    · change x.val ∈ P (BallPresentation.decode ⟨selfCode x.val r.val,hs⟩)
      rwa [hEq]

end IntegrationInACVF.Section3ACVF.ClosedSelfCentredBallProfiles

