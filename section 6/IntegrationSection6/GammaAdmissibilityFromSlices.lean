import IntegrationSection6.GammaFiniteSlices

/-! Finite coordinate slices imply admissibility over the original Gamma base.
The active coordinate is isolated using only the other volume labels. -/
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

theorem gammaAdmissible_of_finite_label_slices {U : GammaRVObject B n} {i : Fin n}
    (hnz : ∀ u : rvObjectDomain U.object, (gammaVolumeValue U u i).val ≠ iRVZero)
    (hfinite : ∀ t : Fin n → CanonicalRV.RVSort M,
      {r | (∃ u : rvObjectDomain U.object, gammaVolumeValue U u = r) ∧
        ∀ j, j ≠ i → r j = t j}.Finite) : GammaAdmissible U i := by
  refine ⟨hnz,?_⟩
  intro u
  let t := gammaVolumeValue U u
  let H : Base (M := M) := ⟨coordinateBase B.real i t,B.gamma⟩
  let G : Set (Fin n → M) := {r | (∀ j, iRV (r j)) ∧ ∀ j, j ≠ i → r j = (t j).val}
  have hG : DefinableOver H.real (fun _ : Fin n => .rv) G := by
    apply (definableOver_iff_normalized_raw H.real (fun _ : Fin n => .rv) G).mpr
    have hguard := ((definableOver_iff_normalized_raw H.real (fun _ : Fin n => .rv) _).mp
      (sortedUniverse_definable H.real (fun _ : Fin n => .rv))).1
    have hJ (j : Fin n) : @Set.Definable M H.real LRV N (Fin n)
        {r | j ≠ i → r j = (t j).val} := by
      by_cases hj : j = i
      · subst j
        simpa using (@Set.definable_univ M H.real LRV N (Fin n))
      · have hc : @Set.DefinableFun M LRV N (Fin n) H.real (fun _ => (t j).val) := by
          letI := N
          exact LRV.definableFun_const _ (Or.inr ⟨j,hj,rfl⟩)
        simpa [hj] using
          (@Set.DefinableFun.ofPred_eq M LRV N (Fin n) H.real _ _
            (@Set.DefinableFun.proj M LRV N (Fin n) H.real j) hc)
    have hEq : @Set.Definable M H.real LRV N (Fin n)
        {r | ∀ j, j ≠ i → r j = (t j).val} := by
      letI := N
      have hall := Set.definable_iInter_of_finite hJ
      convert hall using 1
      ext r
      simp only [Set.mem_ofPred_eq,Set.mem_iInter]
    letI := N
    exact ⟨hguard.inter hEq,fun _ h => h.1⟩
  have hImage : DefinableOverBase H (fun _ : Fin n => .rv) (gammaVolumeImage U) :=
    (gammaVolumeImage_definable U).mono (fun _ h => Or.inl h) (Set.Subset.refl _)
  let C := {r | r ∈ gammaVolumeImage U ∧ r ∈ G}
  have hC : DefinableOverBase H (fun _ : Fin n => .rv) C :=
    hImage.inter_real_preimage (fun _ : Fin n => .rv) G hG id
  have hCf : C.Finite := by
    apply ((hfinite t).image rvValues).subset
    rintro r ⟨⟨v,hv⟩,hr⟩
    refine ⟨gammaVolumeValue U v,⟨⟨v,rfl⟩,?_⟩,hv⟩
    intro j hj
    apply Subtype.ext
    exact (congrFun hv j).trans (hr.2 j hj)
  let A : Set M := (fun r : Fin n → M => r i) '' C
  have hA : DefinableAtBase H .rv A := by
    change DefinableOverBase H (fun _ : Fin 1 => .rv) {z | z 0 ∈ A}
    have hp := hC.image_real (fun _ : Fin 1 => i)
    change DefinableOverBase H (fun _ : Fin 1 => .rv)
      ((fun x : Fin n → M => fun _ : Fin 1 => x i) '' C) at hp
    have he : {z : Fin 1 → M | z 0 ∈ A} =
        ((fun x : Fin n → M => fun _ : Fin 1 => x i) '' C) := by
      apply Set.ext
      intro z
      constructor
      · rintro ⟨r,hr,he⟩
        exact ⟨r,hr,funext (fun j => by fin_cases j; exact he)⟩
      · rintro ⟨r,hr,he⟩
        exact ⟨r,hr,congrFun he 0⟩
    rw [he]
    exact hp
  exact ⟨A,hA,hCf.image _,⟨rvValues t,⟨⟨u,rfl⟩,fun j => (t j).property,
    fun _ _ => rfl⟩,rfl⟩⟩

end IntegrationInACVF.Section6
