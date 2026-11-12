import IntegrationSection6.GammaIndexedFiniteObjects
import IntegrationSection6.GammaAdmissibilityFromSlices

/-! An admissible fibre coordinate remains admissible after gluing over
an RV[k] base: fixing the other global labels leaves only finitely many
index rows. No index tuple is silently added to the original base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {Y : Type*} {b a d n : ℕ}

theorem indexedVolume_finite_label_slices
    (T : Set (Fin b → Y)) (D : (Fin b → Y) → Set (Fin a → Y))
    (f : (Fin b → Y) → (Fin d → Y))
    (g : (Fin b → Y) → (Fin a → Y) → (Fin n → Y)) (i : Fin n)
    (hf : ∀ v, {t | t ∈ T ∧ f t = v}.Finite)
    (hg : ∀ t ∈ T, ∀ z : Fin n → Y,
      {r | (∃ u ∈ D t, g t u = r) ∧ ∀ j, j ≠ i → r j = z j}.Finite)
    (z : Fin (d+n) → Y) :
    {r | (∃ w ∈ indexedDomain T D, indexedVolume f g w = r) ∧
      ∀ j, j ≠ Fin.natAdd d i → r j = z j}.Finite := by
  have h := finite_indexed_pair_coordinate_slice T D f g i hf hg (indexedLeft z) (indexedRight z)
  apply (h.image (Fin.append (indexedLeft z))).subset
  rintro r ⟨⟨w,hw,hwr⟩,hr⟩
  have hb : f (indexedLeft w) = indexedLeft z := by
    funext j
    have hne : Fin.castAdd n j ≠ Fin.natAdd d i := by
      intro he
      have hval := congrArg Fin.val he
      simp only [Fin.val_castAdd,Fin.val_natAdd] at hval
      omega
    have hv := (congrFun hwr (Fin.castAdd n j)).trans (hr _ hne)
    simpa only [indexedVolume,indexedLeft,Function.comp_apply,Fin.append_left] using hv
  have hg' : ∀ j, j ≠ i → indexedRight r j = indexedRight z j := by
    intro j hji
    exact hr (Fin.natAdd d j) (fun he => hji (by
      apply Fin.ext
      have hv := congrArg Fin.val he
      simp only [Fin.val_natAdd] at hv
      omega))
  refine ⟨indexedRight r,⟨⟨indexedLeft w,hw.1,hb,indexedRight w,hw.2,?_⟩,hg'⟩,?_⟩
  · funext j
    simpa only [indexedVolume,indexedRight,Function.comp_apply,Fin.append_right] using
      congrFun hwr (Fin.natAdd d j)
  · have hl : indexedLeft r = indexedLeft z := by
      funext j
      exact hr (Fin.castAdd n j) (by
        intro he
        have hval := congrArg Fin.val he
        simp only [Fin.val_castAdd,Fin.val_natAdd] at hval
        omega)
    rw [← hl]
    exact Fin.append_castAdd_natAdd

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)}

theorem gammaIndexed_admissible
    (T : Set (Fin b → RV (M := M)))
    (D : (Fin b → RV (M := M)) → Set (Fin a → RV (M := M)))
    (f : (Fin b → RV (M := M)) → (Fin d → RV (M := M)))
    (g : (Fin b → RV (M := M)) → (Fin a → RV (M := M)) → (Fin n → RV (M := M)))
    (P : GammaFiniteGraphPresentation B (b+a) (d+n) (indexedDomain T D)
      (fun w z => w ∈ indexedDomain T D ∧ indexedVolume f g w = z)) (i : Fin n)
    (hf : ∀ v, {t | t ∈ T ∧ f t = v}.Finite)
    (hg : ∀ t ∈ T, ∀ z : Fin n → RV (M := M),
      {r | (∃ u ∈ D t, g t u = r) ∧ ∀ j, j ≠ i → r j = z j}.Finite)
    (hnz : ∀ t ∈ T, ∀ u ∈ D t, (g t u i).val ≠ iRVZero) :
    GammaAdmissible P.toGamma.toGammaRVObject (Fin.natAdd d i) := by
  have hvol (w : P.domain) :
      indexedVolume f g w.val = (P.volume w).val := by
    exact ((P.graph_iff w.val (P.volume w).val).mp ⟨w,rfl,rfl⟩).2.2
  have hdom (w : P.domain) : w.val ∈ indexedDomain T D :=
    ((P.graph_iff w.val (P.volume w).val).mp ⟨w,rfl,rfl⟩).1
  apply gammaAdmissible_of_finite_label_slices
  · intro w
    change ((P.volume w).val (Fin.natAdd d i)).val ≠ iRVZero
    rw [← hvol]
    simpa only [indexedVolume,Fin.append_right] using
      hnz (indexedLeft w.val) (hdom w).1 (indexedRight w.val) (hdom w).2
  · intro z
    apply (indexedVolume_finite_label_slices T D f g i hf hg z).subset
    rintro r ⟨⟨w,hw⟩,hr⟩
    exact ⟨⟨w.val,hdom w,(hvol w).trans hw⟩,hr⟩

end IntegrationInACVF.Section6
