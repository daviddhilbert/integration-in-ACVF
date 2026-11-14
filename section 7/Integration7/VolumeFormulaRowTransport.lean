import Integration7.VolumeCorrespondenceRowAgreements
import Integration7.TupleVolumeChartSemantics

/-! The supported Jacobian formulas depend only on the actual
correspondence row. Parameter recoding preserves their full raw semantics. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {p q a b d : ℕ}

theorem sortedUniverse_append_iff (sa : Fin a → SortTag) (sb : Fin b → SortTag)
    (x : Fin a → M) (y : Fin b → M) :
    Fin.append x y ∈ sortedUniverse (Fin.append sa sb) ↔
      x ∈ sortedUniverse sa ∧ y ∈ sortedUniverse sb := by
  constructor
  · intro h
    exact ⟨fun i => by simpa only [Fin.append_left] using h (Fin.castAdd b i),
      fun i => by simpa only [Fin.append_right] using h (Fin.natAdd a i)⟩
  · rintro ⟨hx,hy⟩ i
    refine Fin.addCases (m := a) (n := b) (fun i => ?_) (fun i => ?_) i
    · simpa only [Fin.append_left] using hx i
    · simpa only [Fin.append_right] using hy i

theorem tupleVolumeChartGraph_rowAgreement (σ : VolumeChartSupport d)
    {C : Set (Fin (p+(d+d)) → M)} {D : Set (Fin (q+(d+d)) → M)}
    {z : Fin p → M} {t : Fin q → M}
    (hRows : ∀ r, Fin.append z r ∈ C ↔ Fin.append t r ∈ D)
    (r : Fin (d+d) → M) (ω : Fin 1 → M) :
    Fin.append (Fin.append z r) ω ∈ tupleVolumeChartGraph σ C ↔
      Fin.append (Fin.append t r) ω ∈ tupleVolumeChartGraph σ D := by
  have hC : {u : Fin (d+d) → CanonicalRV.RVSort M | Fin.append z (rvValues u) ∈ C} =
      {u : Fin (d+d) → CanonicalRV.RVSort M | Fin.append t (rvValues u) ∈ D} :=
    Set.ext (fun u => hRows (rvValues u))
  simp only [mem_tupleVolumeChartGraph,Fin.append_left,Fin.append_right]
  rw [hC]

theorem weightedJacobianFormula_rowAgreement
    {sp : Fin p → SortTag} {sq : Fin q → SortTag}
    {J : Set (Fin ((p+(d+d))+1) → M)} {K : Set (Fin ((q+(d+d))+1) → M)}
    {z : Fin p → M} {t : Fin q → M}
    (hz : ∀ i, sortEval (sp i) (z i)) (ht : ∀ i, sortEval (sq i) (t i))
    (hRows : ∀ r ω, Fin.append (Fin.append z r) ω ∈ J ↔ Fin.append (Fin.append t r) ω ∈ K)
    (r : Fin ((d+1)+(d+1)) → M) :
    Fin.append z r ∈ weightedJacobianFormula sp J ↔
      Fin.append t r ∈ weightedJacobianFormula sq K := by
  let l := r ∘ Fin.castAdd (d+1)
  let s := r ∘ Fin.natAdd (d+1)
  let u := l ∘ Fin.castAdd 1
  let v := s ∘ Fin.castAdd 1
  let φ := l ∘ Fin.natAdd d
  let ψ := s ∘ Fin.natAdd d
  have hl : Fin.append u φ = l := Fin.append_castAdd_natAdd
  have hs : Fin.append v ψ = s := Fin.append_castAdd_natAdd
  have hr : Fin.append (Fin.append u φ) (Fin.append v ψ) = r :=
    (congrArg₂ Fin.append hl hs).trans Fin.append_castAdd_natAdd
  have hZ : Fin.append z r = weightedPairTuple z u v φ ψ := congrArg (Fin.append z) hr.symm
  have hT : Fin.append t r = weightedPairTuple t u v φ ψ := congrArg (Fin.append t) hr.symm
  have hSort (ω : Fin 1 → M) :
      Fin.append (weightedPairTuple z u v φ ψ) ω ∈ sortedUniverse
        (Fin.append (Fin.append sp (fun _ : Fin ((d+1)+(d+1)) => .rv)) (fun _ : Fin 1 => .rv)) ↔
      Fin.append (weightedPairTuple t u v φ ψ) ω ∈ sortedUniverse
        (Fin.append (Fin.append sq (fun _ : Fin ((d+1)+(d+1)) => .rv)) (fun _ : Fin 1 => .rv)) := by
    change (Fin.append (Fin.append z _) ω ∈ _) ↔ (Fin.append (Fin.append t _) ω ∈ _)
    simp only [sortedUniverse_append_iff]
    exact and_congr (and_congr (iff_of_true hz ht) Iff.rfl) Iff.rfl
  rw [hZ,hT,weightedJacobianFormula_mem,weightedJacobianFormula_mem,
    weightedPairTuple_coordinates,weightedPairTuple_coordinates,
    weightedPairTuple_densities,weightedPairTuple_densities]
  exact exists_congr (fun ω => and_congr (hRows (Fin.append u v) ω) (and_congr Iff.rfl (hSort ω)))

theorem weightedPairSourceIndices_append (z : Fin p → M) (r : Fin ((d+1)+(d+1)) → M) :
    Fin.append z r ∘ weightedPairSourceIndices p d = Fin.append z (r ∘ Fin.castAdd (d+1)) := by
  funext i
  refine Fin.addCases (m := p) (n := d+1) (fun i => ?_) (fun i => ?_) i <;>
    simp only [Function.comp_apply,weightedPairSourceIndices,Fin.addCases_left,Fin.addCases_right,
      Fin.append_left,Fin.append_right]

end IntegrationInACVF.Section7
