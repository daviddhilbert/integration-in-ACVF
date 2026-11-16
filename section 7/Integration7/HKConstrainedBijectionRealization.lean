import Integration7.HKConstrainedBijectionCharts

/-! Realizing constrained row charts gives an actual definable bijection
over the base, preserving every parameter and the supplied graph relation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ}
variable {sp : Fin p → SortTag} {sx : Fin a → SortTag} {sy : Fin b → SortTag}
variable {D : Set (Fin (p+a) → M)} {E : Set (Fin (p+b) → M)} {A : Set (Fin p → M)}

theorem constrained_total_graph
    (C : GammaSortedBijectionChart B sp sx sy)
    (hA : DefinableOverBase B sp A) (hE : DefinableOverBase B (Fin.append sp sy) E)
    (hC : ∀ z ∈ A, C.valid D E z)
    (K : Set (Fin ((p+a)+b) → M)) (hCK : C.carrier ⊆ K)
    (u : rawRowTotal A D) :
    Fin.append u.val (((gammaSortedTotalIso C hA hE hC).equiv u).val ∘ Fin.natAdd p) ∈ K := by
  let v := rawRowTotalEquiv A D u
  let y := (hC v.1.val v.1.property).map v.2
  have hu : (rawRowTotalEquiv A D).symm v = u := (rawRowTotalEquiv A D).symm_apply_apply u
  have hin : Fin.append v.1.val v.2.val = u.val := congrArg Subtype.val hu
  have ht := congrArg Subtype.val (gammaSortedTotalEquiv_pack C hE hC v.1 v.2)
  have ht' := congrArg (fun q => ((gammaSortedTotalIso C hA hE hC).equiv q).val) hu
  have hout : ((gammaSortedTotalIso C hA hE hC).equiv u).val = Fin.append v.1.val y.val :=
    ht'.symm.trans ht
  rw [← hin,hout]
  simpa only [Function.comp_def,Fin.append_right] using hCK ((hC v.1.val v.1.property).map_graph v.2)

theorem fibre_bijection_within {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (hA : DefinableOverBase B sp A)
    (hD : DefinableOverBase B (Fin.append sp sx) D) (hE : DefinableOverBase B (Fin.append sp sy) E)
    (K : Set (Fin ((p+a)+b) → M))
    (hK : DefinableOverBase B (Fin.append (Fin.append sp sx) sy) K)
    (hrow : ∀ z ∈ A, ∃ e : GammaSortedIso ⟨B.real ∪ Set.range z,B.gamma⟩ sx sy
      {x : Fin a → M | Fin.append z x ∈ D} {y : Fin b → M | Fin.append z y ∈ E},
      ∀ u, Fin.append (Fin.append z u.val) (e.equiv u).val ∈ K) :
    ∃ e : GammaSortedIso B (Fin.append sp sx) (Fin.append sp sy) (rawRowTotal A D) (rawRowTotal A E),
      (∀ u, (e.equiv u).val ∘ Fin.castAdd b = u.val ∘ Fin.castAdd a) ∧
      ∀ u, Fin.append u.val ((e.equiv u).val ∘ Fin.natAdd p) ∈ K := by
  obtain ⟨C,hCK,hC⟩ := uniform_bijection_chart_within hκ hs hreal hgamma A hA hD hE K (by
    intro z hz
    obtain ⟨e,he⟩ := hrow z hz
    exact promote_row_bijection_within z (hA.proper z hz) K hK e he)
  exact ⟨gammaSortedTotalIso C hA hE hC,gammaSortedTotalEquiv_prefix C hE hC,
    constrained_total_graph C hA hE hC K hCK⟩

end IntegrationInACVF.Section7.HK
