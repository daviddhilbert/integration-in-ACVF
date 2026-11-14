import Integration7.VolumeFamilyChartCodes

/-! The uniform first-order formula represents the actual residue-Jacobian
chart values. Parameters remain free; no Jacobian condition is assumed. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {π : Type} {n : ℕ}
local notation "I" => Fin (n+n)
local notation "O" => Fin 1
local notation "RV" => CanonicalRV.RVSort M
local notation "K" => ModelResidue M

theorem mem_rawVolumeFamilyChartValue (σ : VolumeChartSupport n)
    (C : Set (π ⊕ I → M)) (T : LRV.Term (I ⊕ Unit))
    (hT : ∀ (a b : Fin n → RV) (d : RV),
      T.realize (Sum.elim (rvValues (productTuple a b)) (fun _ => d.val)) =
        ((((∏ i, b i) / ∏ i, a i) * d) : RV).val)
    (p : π → M) (t : I → RV) (ω : O → RV) :
    Sum.elim p (Sum.elim (rvValues t) (rvValues ω)) ∈ rawVolumeFamilyChartValue σ C T ↔
      VolumeChartValue σ (volumeFamilyRow C p) t ω := by
  constructor
  · rintro ⟨_,_,v,hne,hcert,hmem,heval,hval,hJ⟩
    let u := v ∘ Sum.inl ∘ Sum.inl
    let q (i : I) : RV := ⟨u i,(hne i).1⟩
    let a := q ∘ productLeft n n
    let b := q ∘ productRight n n
    have hq : productTuple a b = q := by
      apply productTuple_ext
      · intro i; exact productTuple_left _ _ _
      · intro i; exact productTuple_right _ _ _
    have hu : u = rvValues (productTuple a b) := by rw [hq]; rfl
    obtain ⟨e,he,hcode⟩ := heval
    let c := e ∘ Sum.inl ∘ Sum.inl
    let z := e ∘ Sum.inl ∘ Sum.inr
    let d := e (.inr ())
    have hc' : residueRaw ∘ c = v ∘ Sum.inl ∘ Sum.inr :=
      funext fun i => congrFun hcode (.inl (.inl i))
    have hz' : residueRaw ∘ z = v ∘ Sum.inr ∘ Sum.inl :=
      funext fun i => congrFun hcode (.inl (.inr i))
    have hd' : (fun _ : Unit => residueRaw d) = v ∘ Sum.inr ∘ Sum.inr := by
      funext i
      cases i
      exact congrFun hcode (.inr ())
    have hEval : Sum.elim (residueRaw ∘ Sum.elim c z) (fun _ => residueRaw d) ∈
        rawVolumeChartEvaluation (M := M) σ := by
      refine ⟨e,he,?_⟩
      funext i
      rcases i with (i | i) | ⟨⟩ <;> rfl
    obtain ⟨hcut,hd⟩ := (mem_rawVolumeChartEvaluation_iff σ (Sum.elim c z) d).mp hEval
    have hq₀ (i : I) : q i ≠ 0 :=
      fun h₀ => (hne i).2 ((congrArg Subtype.val h₀).trans RVOperations.zero_val)
    refine ⟨a,b,c,z,fun i => hq₀ _,fun i => hq₀ _,?_,?_,hcut,?_,?_⟩
    · apply (mem_rawVolumeFamilyChart σ C p a b c).mp
      change Sum.elim (Sum.elim p u) (v ∘ Sum.inl ∘ Sum.inr) ∈ rawVolumeFamilyChart σ C at hcert
      rwa [← hu,hc']
    · apply (mem_rawVolumeFamilyNormalized C p a b z).mp
      change Sum.elim (Sum.elim p u) (v ∘ Sum.inr ∘ Sum.inl) ∈ rawVolumeFamilyNormalized C at hmem
      rwa [← hu,hz']
    · funext i
      apply Subtype.ext
      have hv : (t i).val = iRVMul (u i) ((v ∘ Sum.inr ∘ Sum.inl) i) := hval i
      refine hv.trans ?_
      rw [← hz',hu]
      exact (RVOperations.mul_val _ _).symm
    · apply Subtype.ext
      have hj : (ω 0).val = T.realize (Sum.elim u (v ∘ Sum.inr ∘ Sum.inr)) := hJ
      refine hj.trans ?_
      rw [hu,← hd']
      exact (hT a b (residueRV d)).trans
        (congrArg (fun e : K => ((((∏ i, b i) / ∏ i, a i) * residueRV e) : RV).val) hd.symm)
  · rintro ⟨a,b,c,z,ha,hb,hChart,hz,hcut,hval,hJ⟩
    let u := rvValues (productTuple a b)
    let d := volumeChartDeterminant σ (Sum.elim c z)
    let v : VolumeFamilyChartWitness σ → M := Sum.elim (Sum.elim u (residueRaw ∘ c))
      (Sum.elim (residueRaw ∘ z) (fun _ => residueRaw d))
    refine ⟨⟨t,rfl⟩,⟨ω,rfl⟩,v,?_,?_,?_,?_,?_,?_⟩
    · intro i
      obtain ⟨j | j,rfl⟩ := finSumFinEquiv.surjective i
      · change NonzeroRV (productTuple a b (productLeft n n j)).val
        rw [productTuple_left]
        exact ⟨(a j).property,fun h₀ => ha j (Subtype.ext (h₀.trans RVOperations.zero_val.symm))⟩
      · change NonzeroRV (productTuple a b (productRight n n j)).val
        rw [productTuple_right]
        exact ⟨(b j).property,fun h₀ => hb j (Subtype.ext (h₀.trans RVOperations.zero_val.symm))⟩
    · exact (mem_rawVolumeFamilyChart σ C p a b c).mpr hChart
    · exact (mem_rawVolumeFamilyNormalized C p a b z).mpr hz
    · change Sum.elim (Sum.elim (residueRaw ∘ c) (residueRaw ∘ z))
        (fun _ => residueRaw d) ∈ rawVolumeChartEvaluation σ
      have he : Sum.elim (residueRaw ∘ c) (residueRaw ∘ z) = residueRaw ∘ Sum.elim c z := by
        funext i
        cases i <;> rfl
      rw [he]
      exact (mem_rawVolumeChartEvaluation_iff σ (Sum.elim c z) d).mpr ⟨hcut,rfl⟩
    · intro i
      exact (congrArg (fun e : I → RV => (e i).val) hval).trans (RVOperations.mul_val _ _)
    · exact (congrArg Subtype.val hJ).trans (hT a b (residueRV d)).symm

end IntegrationInACVF.Section7
