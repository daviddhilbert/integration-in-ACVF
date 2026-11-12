import IntegrationSection6.GammaVolumeImage
import IntegrationSection6.GammaAlgebraicFiniteness
import IntegrationSection6.FiniteElementarySlices
import Section3.GammaRealRestriction

/-! Finite old-label slices over the original Gamma base. Only the real
base and the finitely many fixed labels enter the saturation bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem GammaAdmissible.finite_label_slices {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    {U : GammaRVObject B n} {i : Fin n} (h : GammaAdmissible U i)
    (t : Fin n → CanonicalRV.RVSort M) :
    {r | (∃ u : rvObjectDomain U.object, gammaVolumeValue U u = r) ∧
      ∀ j, j ≠ i → r j = t j}.Finite := by
  let H : Base (M := M) := ⟨B.real ∪ Set.range (rvValues t),B.gamma⟩
  let G : Set (Fin n → M) := {r | (∀ j, iRV (r j)) ∧ ∀ j, j ≠ i → r j = (t j).val}
  have hG : DefinableOver H.real (fun _ : Fin n => .rv) G := by
    apply (definableOver_iff_normalized_raw H.real (fun _ : Fin n => .rv) G).mpr
    have hguard := ((definableOver_iff_normalized_raw H.real (fun _ : Fin n => .rv) _).mp
      (sortedUniverse_definable H.real (fun _ : Fin n => .rv))).1
    have hEq : @Set.Definable M H.real LRV N (Fin n)
        {r | ∀ j, j ≠ i → r j = (t j).val} := by
      have hJ (j : Fin n) : @Set.Definable M H.real LRV N (Fin n)
          {r | j ≠ i → r j = (t j).val} := by
        by_cases hj : j = i
        · subst j
          simpa using
            (@Set.definable_univ M H.real LRV N (Fin n))
        · have hc : @Set.DefinableFun M LRV N (Fin n) H.real (fun _ => (t j).val) := by
            letI := N
            exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self j))
          simpa [hj] using
            (@Set.DefinableFun.ofPred_eq M LRV N (Fin n) H.real _ _ (@Set.DefinableFun.proj M LRV N (Fin n) H.real j) hc)
      letI := N
      have hall := Set.definable_iInter_of_finite hJ
      convert hall using 1
      ext r
      simp only [Set.mem_setOf_eq,Set.mem_iInter]
    letI := N
    exact ⟨hguard.inter hEq,fun _ h => h.1⟩
  have hImage : DefinableOverBase H (fun _ : Fin n => .rv) (gammaVolumeImage U) :=
    (gammaVolumeImage_definable U).mono Set.subset_union_left (Set.Subset.refl _)
  let C := {r | r ∈ gammaVolumeImage U ∧ r ∈ G}
  have hC : DefinableOverBase H (fun _ : Fin n => .rv) C :=
    hImage.inter_real_preimage (fun _ : Fin n => .rv) G hG id
  have hHsmall : Cardinal.mk H.real < κ := small_union_range hκ B.real hsmall (rvValues t)
  have hfinite : C.Finite := by
    apply gammaRV_set_finite_of_algebraic hκ hs h00 H hHsmall C hC
    intro r hr j
    obtain ⟨u,hu⟩ := hr.1
    by_cases hj : j = i
    · subst j
      have ha := h.algebraic u
      have hm : coordinateBase B.real i (gammaVolumeValue U u) ⊆ H.real := by
        rintro b (hb | ⟨j,hj,hb⟩)
        · exact Or.inl hb
        · have he : (gammaVolumeValue U u j).val = (t j).val := (congrFun hu j).trans (hr.2.2 j hj)
          exact Or.inr ⟨j,he.symm.trans hb⟩
      have haH := ha.mono hm (Set.Subset.refl _)
      exact (congrFun hu i) ▸ haH
    · have hjmem : r j ∈ H.real := Or.inr ⟨j,(hr.2.2 j hj).symm⟩
      have hd := definableClosureAt_of_mem (σ := .rv) hjmem (hr.2.1 j)
      exact ⟨{r j},real_definableAtBase H .rv _ hd,Set.finite_singleton _,Set.mem_singleton _⟩
  apply hfinite.of_injOn (f := rvValues)
  · rintro r ⟨⟨u,hu⟩,hr⟩
    refine ⟨⟨u,congrArg rvValues hu⟩,fun j => (r j).property,?_⟩
    intro j hj
    exact congrArg Subtype.val (hr j hj)
  · exact rvValues_injective.injOn

end IntegrationInACVF.Section6
