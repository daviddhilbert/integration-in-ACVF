import Integration7.VolumeFamilyNormalization

/-! Finite polynomial certificates for parameterized volume correspondences.
These use the predecessor's actual residue chart tests and tangent theorem. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language MvPolynomial
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

attribute [local instance] FirstOrder.Ring.compatibleRingOfRing
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {π : Type} {n : ℕ} {S : Set M}
local notation "I" => Fin (n+n)
local notation "RV" => CanonicalRV.RVSort M
local notation "K" => ModelResidue M

private def familyEquationsTest (σ : VolumeChartSupport n) : Set (σ.Index ⊕ I → K) :=
  {w | ∀ i, (chartEquation σ.equations (w ∘ Sum.inl) i).eval (w ∘ Sum.inr) = 0}
private def familyOpenTest (σ : VolumeChartSupport n) : Set (σ.Index ⊕ I → K) :=
  {w | (chartDerivativeBlock σ.equations (productRight n n) w).det *
    (chartExtraOpen σ.extraOpen (w ∘ Sum.inl)).eval (w ∘ Sum.inr) ≠ 0}
private def familyCutTest (σ : VolumeChartSupport n) : Set (σ.Index ⊕ I → K) :=
  {w | (chartInputCut σ.inputCut (w ∘ Sum.inl)).eval (w ∘ Sum.inr ∘ productLeft n n) ≠ 0}
private def familyInputDerivativeTest (σ : VolumeChartSupport n) : Set (σ.Index ⊕ I → K) :=
  {w | (chartDerivativeBlock σ.equations (productLeft n n) w).det ≠ 0}

def rawVolumeFamilyChart (σ : VolumeChartSupport n) (C : Set (π ⊕ I → M)) :
    Set ((π ⊕ I) ⊕ σ.Index → M) :=
  rawResidueChartCertificate (rawVolumeFamilyNormalized C) (rawResidueImage Set.univ)
    (rawResidueImage (familyEquationsTest (M := M) σ))
    (rawResidueImage (familyOpenTest (M := M) σ))
    (rawResidueImage (familyCutTest (M := M) σ))
    (rawResidueImage (familyInputDerivativeTest (M := M) σ))

theorem rawVolumeFamilyChart_definable [Finite π]
    (hc : CanonicalStructure.IsCanonical (M := M)) (σ : VolumeChartSupport n)
    {C : Set (π ⊕ I → M)} (hC : S.Definable LRV C) :
    S.Definable LRV (rawVolumeFamilyChart σ C) := by
  let E := residueDefinableField S
  obtain ⟨hP,hQ,hD,hR,_⟩ := relative_chart_arithmetic E σ.equations σ.extraOpen σ.inputCut
  apply rawResidueChartCertificate_definable (rawVolumeFamilyNormalized_definable hc hC)
  · exact residueFieldImage_indexed_definable hc E S le_rfl _ Set.definable_univ
  · exact residueFieldImage_indexed_definable hc E S le_rfl _ hP
  · exact residueFieldImage_indexed_definable hc E S le_rfl _ (hQ.eq_const 0 E.zero_mem).compl
  · exact residueFieldImage_indexed_definable hc E S le_rfl _ (hD.eq_const 0 E.zero_mem).compl
  · exact residueFieldImage_indexed_definable hc E S le_rfl _ (hR.eq_const 0 E.zero_mem).compl

private theorem rawResidueImage_family_right_witness {β γ : Type}
    {A : Set (β ⊕ γ → K)} {c : β → M} {z : γ → M}
    (h : Sum.elim c z ∈ rawResidueImage A) : ∃ y : γ → K, residueRaw ∘ y = z := by
  obtain ⟨w,_,hw⟩ := h
  exact ⟨w ∘ Sum.inr,funext fun i => congrFun hw (.inr i)⟩

theorem mem_rawVolumeFamilyChart (σ : VolumeChartSupport n) (C : Set (π ⊕ I → M))
    (p : π → M) (a b : Fin n → RV) (c : σ.Index → K) :
    Sum.elim (Sum.elim p (rvValues (productTuple a b))) (residueRaw ∘ c) ∈
      rawVolumeFamilyChart σ C ↔ IsVolumeChart σ (volumeFamilyRow C p) a b c := by
  let v := Sum.elim p (rvValues (productTuple a b))
  let u := residueRaw ∘ c
  have hTest (A : Set (σ.Index ⊕ I → K)) (z : I → K) :
      Sum.elim u (residueRaw ∘ z) ∈ rawResidueImage A ↔ Sum.elim c z ∈ A := by
    have he : Sum.elim u (residueRaw ∘ z) = residueRaw ∘ Sum.elim c z := by
      funext i
      cases i <;> rfl
    rw [he]
    exact mem_rawResidueImage_iff A _
  constructor
  · rintro ⟨_,⟨z₀,h₀⟩,h⟩
    obtain ⟨z,rfl⟩ := rawResidueImage_family_right_witness h₀
    refine ⟨⟨z,(hTest _ z).mp h₀⟩,?_,?_,?_⟩
    · intro z hz
      exact (hTest _ z).mp ((h (residueRaw ∘ z)).1
        ((mem_rawVolumeFamilyNormalized C p a b z).mpr hz)).1
    · intro z hP hQ
      exact (mem_rawVolumeFamilyNormalized C p a b z).mp
        ((h (residueRaw ∘ z)).2 ⟨(hTest _ z).mpr hP,(hTest _ z).mpr hQ⟩)
    · intro z hz hD
      obtain ⟨hQ,hR⟩ := ((h (residueRaw ∘ z)).1
        ((mem_rawVolumeFamilyNormalized C p a b z).mpr hz)).2 ((hTest _ z).mpr hD)
      exact ⟨(hTest _ z).mp hQ,(hTest _ z).mp hR⟩
  · intro h
    obtain ⟨z₀,h₀⟩ := h.cut_nonempty
    refine ⟨⟨c,Set.mem_univ _,rfl⟩,⟨residueRaw ∘ z₀,(hTest _ z₀).mpr h₀⟩,
      fun z => ⟨?_,?_⟩⟩
    · intro hz
      obtain ⟨r,_,hr⟩ := hz.2.2
      change residueRaw ∘ r = z at hr
      subst z
      have hp := (mem_rawVolumeFamilyNormalized C p a b r).mp hz
      refine ⟨(hTest _ r).mpr (h.equations r hp),fun hD => ?_⟩
      obtain ⟨hQ,hR⟩ := h.covers r hp ((hTest _ r).mp hD)
      exact ⟨(hTest _ r).mpr hQ,(hTest _ r).mpr hR⟩
    · rintro ⟨hP,hQ⟩
      obtain ⟨r,rfl⟩ := rawResidueImage_family_right_witness hP
      exact (mem_rawVolumeFamilyNormalized C p a b r).mpr
        (h.contains r ((hTest _ r).mp hP) ((hTest _ r).mp hQ))

end IntegrationInACVF.Section7
