import IntegrationSection6.GammaVolumeImageFamilies
import Section3.GammaRealRestriction

/-! Fixed finite bounds on coordinate slices of volume-image families
have original-Gamma definable validity loci. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ}
local notation "NStr" => (@CanonicalStructure.normalize M sM)

def sliceVolumeCoordinates (p k : ℕ) : Fin (p+k) → Fin ((p+k)+k) :=
  Fin.addCases (fun j => Fin.castAdd k (Fin.castAdd k j)) (Fin.natAdd (p+k))

def tupleLabelSlice (sp : Fin p → SortTag) (D : Set (Fin (p+k) → M)) (i : Fin k) :
    Set (Fin ((p+k)+k) → M) :=
  {w | w ∘ sliceVolumeCoordinates p k ∈ D ∧
    w ∈ sortedUniverse (Fin.append (Fin.append sp (fun _ : Fin k => .rv)) (fun _ : Fin k => .rv)) ∧
    ∀ j, j ≠ i → w (Fin.natAdd (p+k) j) = w (Fin.castAdd k (Fin.natAdd p j))}

theorem gamma_tuple_label_slice_definable (sp : Fin p → SortTag)
    {D : Set (Fin (p+k) → M)} (hD : DefinableOverBase B (Fin.append sp (fun _ : Fin k => .rv)) D)
    (i : Fin k) : DefinableOverBase B
      (Fin.append (Fin.append sp (fun _ : Fin k => .rv)) (fun _ : Fin k => .rv)) (tupleLabelSlice sp D i) := by
  let S := B.real
  let st := Fin.append (Fin.append sp (fun _ : Fin k => SortTag.rv)) (fun _ : Fin k => SortTag.rv)
  let E : Set (Fin ((p+k)+k) → M) :=
    {w | ∀ j, j ≠ i → w (Fin.natAdd (p+k) j) = w (Fin.castAdd k (Fin.natAdd p j))}
  have hE : @Set.Definable M S LRV NStr (Fin ((p+k)+k)) E := by
    have hj (j : Fin k) : @Set.Definable M S LRV NStr (Fin ((p+k)+k))
        {w | j ≠ i → w (Fin.natAdd (p+k) j) = w (Fin.castAdd k (Fin.natAdd p j))} := by
      letI := NStr
      by_cases hji : j = i
      · simp only [hji,ne_eq,not_true_eq_false,false_implies]
        exact Set.definable_univ
      · simpa only [hji,Ne,not_false_eq_true,true_implies] using
          (@Set.DefinableFun.ofPred_eq M LRV NStr (Fin ((p+k)+k)) S _ _
            (@Set.DefinableFun.proj M LRV NStr _ S (Fin.natAdd (p+k) j))
            (@Set.DefinableFun.proj M LRV NStr _ S (Fin.castAdd k (Fin.natAdd p j))))
    letI := NStr
    convert Set.definable_iInter_of_finite hj using 1
    apply Set.ext
    intro w
    simp only [E,Set.mem_ofPred_eq,Set.mem_iInter]
  have hSort := ((definableOver_iff_normalized_raw S st _).mp (sortedUniverse_definable S st)).1
  have hGuard : DefinableOver S st {w | w ∈ sortedUniverse st ∧ w ∈ E} := by
    apply (definableOver_iff_normalized_raw S st _).mpr
    letI := NStr
    exact ⟨hSort.inter hE,fun _ h => h.1⟩
  exact hD.inter_real_preimage st _ hGuard (sliceVolumeCoordinates p k)

theorem gamma_label_slice_bound_definable (sp : Fin p → SortTag) (N : ℕ)
    {D : Set (Fin (p+k) → M)} (hD : DefinableOverBase B (Fin.append sp (fun _ : Fin k => .rv)) D)
    (i : Fin k) :
    DefinableOverBase B sp {z | (∀ j, sortEval (sp j) (z j)) ∧
      ∀ t : Fin k → M, (∀ j, sortEval SortTag.rv (t j)) →
        {r | Fin.append z r ∈ D ∧ ∀ j, j ≠ i → r j = t j}.Finite ∧
        {r | Fin.append z r ∈ D ∧ ∀ j, j ≠ i → r j = t j}.ncard ≤ N} := by
  have hs := gamma_tuple_label_slice_definable sp hD i
  have hb := gamma_family_finite_bound_definable (Fin.append sp (fun _ : Fin k => .rv))
    (fun _ : Fin k => .rv) N hs
  have h := gamma_family_row_forall_definable sp (fun _ : Fin k => .rv) hb
  have hRows (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
      (t : Fin k → M) (ht : ∀ j, sortEval SortTag.rv (t j)) :
      {r | Fin.append (Fin.append z t) r ∈ tupleLabelSlice sp D i} =
      {r | Fin.append z r ∈ D ∧ ∀ j, j ≠ i → r j = t j} := by
    apply Set.ext
    intro r
    have hSel : Fin.append (Fin.append z t) r ∘ sliceVolumeCoordinates p k = Fin.append z r := by
      funext j
      refine Fin.addCases (fun l => ?_) (fun l => ?_) j <;>
        simp only [sliceVolumeCoordinates,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,
          Fin.append_left,Fin.append_right]
    change (_ ∈ D ∧ _ ∈ sortedUniverse _ ∧ _) ↔ _
    rw [hSel]
    simp only [Fin.append_left,Fin.append_right]
    constructor
    · exact fun hr => ⟨hr.1,hr.2.2⟩
    · rintro ⟨hr,he⟩
      refine ⟨hr,?_,he⟩
      have hrv (j : Fin k) : sortEval SortTag.rv (r j) := by
        simpa only [Fin.append_right] using hD.proper _ hr (Fin.natAdd p j)
      intro j
      refine Fin.addCases (fun l => ?_) (fun l => ?_) j
      · refine Fin.addCases (fun v => ?_) (fun v => ?_) l
        · simpa only [Fin.append_left] using hz v
        · simpa only [Fin.append_left,Fin.append_right] using ht v
      · simpa only [Fin.append_right] using hrv l
  convert h using 1
  apply Set.ext
  intro z
  constructor
  · rintro ⟨hz,hbound⟩
    refine ⟨hz,?_⟩
    intro t ht
    refine ⟨?_,?_⟩
    · intro j
      refine Fin.addCases (fun l => ?_) (fun l => ?_) j
      · simpa only [Fin.append_left] using hz l
      · simpa only [Fin.append_right] using ht l
    · rw [hRows z hz t ht]
      exact hbound t ht
  · rintro ⟨hz,hbound⟩
    refine ⟨hz,fun t ht => ?_⟩
    have hb := (hbound t ht).2
    rw [hRows z hz t ht] at hb
    exact hb

end IntegrationInACVF.Section6
