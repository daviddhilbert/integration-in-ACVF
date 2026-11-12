import IntegrationSection6.GammaRawLabelImages
import IntegrationSection6.GammaRawElementaryRowCoordinates

/-! Exact typed rows of relational label images. All existential raw
witnesses are decoded using the explicit proper-sort guards. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6

theorem rawLabelImageDomainSource_append {Y : Type*} {p a b : ℕ}
    (z : Fin p → Y) (w : Fin b → Y) (x : Fin a → Y) :
    Fin.append (Fin.append z w) x ∘ rawLabelImageDomainSource p a b = Fin.append z x := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp only [Function.comp_apply,rawLabelImageDomainSource,Fin.addCases_left,Fin.addCases_right,
      Fin.append_left,Fin.append_right]

theorem rawLabelImageDomainGraph_append {Y : Type*} {p a b : ℕ}
    (z : Fin p → Y) (w : Fin b → Y) (x : Fin a → Y) :
    Fin.append (Fin.append z w) x ∘ rawLabelImageDomainGraph p a b = Fin.append x w := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp only [Function.comp_apply,rawLabelImageDomainGraph,Fin.addCases_left,Fin.addCases_right,
      Fin.append_left,Fin.append_right]

theorem rawLabelImageVolumeSource_append {Y : Type*} {p a b k : ℕ}
    (z : Fin p → Y) (w : Fin b → Y) (v : Fin k → Y) (x : Fin a → Y) :
    Fin.append (Fin.append (Fin.append z w) v) x ∘ rawLabelImageVolumeSource p a b k =
      Fin.append (Fin.append z x) v := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · refine Fin.addCases (fun l => ?_) (fun l => ?_) i <;>
      simp only [Function.comp_apply,rawLabelImageVolumeSource,Fin.addCases_left,Fin.addCases_right,
        Fin.append_left,Fin.append_right]
  · simp only [Function.comp_apply,rawLabelImageVolumeSource,Fin.addCases_right,Fin.append_left,Fin.append_right]

theorem rawLabelImageVolumeGraph_append {Y : Type*} {p a b k : ℕ}
    (z : Fin p → Y) (w : Fin b → Y) (v : Fin k → Y) (x : Fin a → Y) :
    Fin.append (Fin.append (Fin.append z w) v) x ∘ rawLabelImageVolumeGraph p a b k = Fin.append x w := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp only [Function.comp_apply,rawLabelImageVolumeGraph,Fin.addCases_left,Fin.addCases_right,
      Fin.append_left,Fin.append_right]

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

theorem GammaFiniteRVSchema.labelImage_row_domain (F : GammaFiniteRVSchema B p a k sp)
    {H : Set (Fin (a+b) → M)} (hH : DefinableOverBase B (fun _ => .rv) H)
    (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j)) (w : Fin b → RV (M := M)) :
    w ∈ (F.labelImageFormula hH).rowDomain z ↔
      ∃ x : Fin a → RV (M := M), x ∈ F.rowDomain z ∧
        Fin.append (fun j => (x j).val) (fun j => (w j).val) ∈ H := by
  change (∃ x : Fin a → M, (_ ∧ _) ∧ (_ ∧ _)) ↔ _
  constructor
  · rintro ⟨x,⟨hx,hp⟩,⟨hg,_⟩⟩
    have hxs (j : Fin a) : iRV (x j) := by
      simpa only [Fin.append_right,sortEval,iRV] using hp (Fin.natAdd (p+b) j)
    refine ⟨fun j => ⟨x j,hxs j⟩,?_,?_⟩
    · change Fin.append z x ∈ F.domain
      exact rawLabelImageDomainSource_append z _ x ▸ hx
    · exact rawLabelImageDomainGraph_append z _ x ▸ hg
  · rintro ⟨x,hx,hg⟩
    have hp := sorted_append_RV _ _ (sorted_append_RV sp z hz w) x
    refine ⟨fun j => (x j).val,⟨?_,hp⟩,⟨?_,hp⟩⟩
    · rw [rawLabelImageDomainSource_append]
      exact hx
    · rw [rawLabelImageDomainGraph_append]
      exact hg

theorem GammaFiniteRVSchema.labelImage_row_volume (F : GammaFiniteRVSchema B p a k sp)
    {H : Set (Fin (a+b) → M)} (hH : DefinableOverBase B (fun _ => .rv) H)
    (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (w : Fin b → RV (M := M)) (v : Fin k → RV (M := M)) :
    (F.labelImageFormula hH).rowVolume z w v ↔
      ∃ x : Fin a → RV (M := M), F.rowVolume z x v ∧
        Fin.append (fun j => (x j).val) (fun j => (w j).val) ∈ H := by
  change (∃ x : Fin a → M, (_ ∧ _) ∧ (_ ∧ _)) ↔ _
  constructor
  · rintro ⟨x,⟨hx,hp⟩,⟨hg,_⟩⟩
    have hxs (j : Fin a) : iRV (x j) := by
      simpa only [Fin.append_right,sortEval,iRV] using hp (Fin.natAdd ((p+b)+k) j)
    refine ⟨fun j => ⟨x j,hxs j⟩,?_,?_⟩
    · change Fin.append (Fin.append z x) (fun j => (v j).val) ∈ F.volume
      exact rawLabelImageVolumeSource_append z _ _ x ▸ hx
    · exact rawLabelImageVolumeGraph_append z _ _ x ▸ hg
  · rintro ⟨x,hx,hg⟩
    have hp := sorted_append_RV _ _ (sorted_append_RV _ _ (sorted_append_RV sp z hz w) v) x
    refine ⟨fun j => (x j).val,⟨?_,hp⟩,⟨?_,hp⟩⟩
    · rw [rawLabelImageVolumeSource_append]
      exact hx
    · rw [rawLabelImageVolumeGraph_append]
      exact hg

end IntegrationInACVF.Section6
