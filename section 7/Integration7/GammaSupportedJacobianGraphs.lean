import Integration7.GammaVolumeChartGraphs
import IntegrationSection6.GammaRawRVFormulas
import IntegrationSection6.FiniteGammaInitial

/-! Supported coordinate-Jacobian values are graphs over the same
original Gamma base as their correspondence. Finite support choices add
no real or Gamma parameters. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

theorem gamma_volume_chart_value_graph
    (hc : CanonicalStructure.IsCanonical (M := M)) (σ : VolumeChartSupport n)
    (C : Set (Fin (n+n) → CanonicalRV.RVSort M)) (R : Set (Fin (n+n) → M))
    (hR : DefinableOverBase B (fun _ => .rv) R)
    (hRC : ∀ t, rvValues t ∈ R ↔ t ∈ C) :
    GammaGraphDefinable B (fun (t : Point (M := M) 0 (n+n)) (ω : Point (M := M) 0 1) =>
      VolumeChartValue σ C t.2 ω.2) := by
  let sp : Fin 0 → SortTag := Fin.elim0
  let st := Fin.append sp (fun _ : Fin (n+n) => SortTag.rv)
  let D : Set (Fin (0+(n+n)) → M) :=
    {w | w ∘ Fin.natAdd 0 ∈ R ∧ w ∈ sortedUniverse st}
  have hD : DefinableOverBase B st D := hR.preimage_real st (Fin.natAdd 0)
  have hJ := gamma_tupleVolumeChartGraph_definable hc σ sp hD
  let e := finCongr (congrArg Nat.succ (Nat.zero_add (n+n)))
  let Q : Set (Fin ((n+n)+1) → M) :=
    {w | w ∘ e ∈ tupleVolumeChartGraph σ D ∧ w ∈ sortedUniverse (fun _ => .rv)}
  have hQ : DefinableOverBase B (fun _ => .rv) Q := hJ.preimage_real (fun _ => .rv) e
  have h := gamma_rv_graph_from_tuple_formula hQ
  apply GammaGraphDefinable.congr h
  intro t ω
  have hrow : {r : Fin (n+n) → CanonicalRV.RVSort M |
      Fin.append Fin.elim0 (rvValues r) ∈ D} = C := by
    ext r
    change ((Fin.append Fin.elim0 (rvValues r) ∘ Fin.natAdd 0 ∈ R) ∧
      Fin.append Fin.elim0 (rvValues r) ∈ sortedUniverse st) ↔ r ∈ C
    have he : Fin.append Fin.elim0 (rvValues r) ∘ Fin.natAdd 0 = rvValues r :=
      funext (Fin.append_right _ _)
    rw [he]
    exact ⟨fun hr => (hRC r).mp hr.1,fun hr => ⟨(hRC r).mpr hr,by
      intro i
      refine Fin.addCases (fun i => Fin.elim0 i) (fun i => ?_) i
      simpa only [st,Fin.append_right,rvValues,sortEval,iRV] using (r i).property⟩⟩
  change (Fin.append (rvValues t.2) (rvValues ω.2) ∘ e ∈ tupleVolumeChartGraph σ D ∧
    Fin.append (rvValues t.2) (rvValues ω.2) ∈ sortedUniverse (fun _ => .rv)) ↔ _
  have hproper : Fin.append (rvValues t.2) (rvValues ω.2) ∈ sortedUniverse (fun _ => .rv) := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [Fin.append_left,rvValues,sortEval,iRV] using (t.2 i).property
    · simpa only [Fin.append_right,rvValues,sortEval,iRV] using (ω.2 i).property
  rw [and_iff_left hproper,mem_tupleVolumeChartGraph]
  have ht : (fun i => (Fin.append (rvValues t.2) (rvValues ω.2) ∘ e) (Fin.castAdd 1 (Fin.natAdd 0 i))) =
      rvValues t.2 := by
    funext i
    have hi : e (Fin.castAdd 1 (Fin.natAdd 0 i)) = Fin.castAdd 1 i := by
      apply Fin.ext
      simp [e]
    exact (congrArg (Fin.append (rvValues t.2) (rvValues ω.2)) hi).trans (Fin.append_left _ _ i)
  have hω : (fun i => (Fin.append (rvValues t.2) (rvValues ω.2) ∘ e) (Fin.natAdd (0+(n+n)) i)) =
      rvValues ω.2 := by
    funext i
    have hi : e (Fin.natAdd (0+(n+n)) i) = Fin.natAdd (n+n) i := by
      apply Fin.ext
      simp [e]
    exact (congrArg (Fin.append (rvValues t.2) (rvValues ω.2)) hi).trans (Fin.append_right _ _ i)
  simp only [ht,hω]
  constructor
  · rintro ⟨r,v,hr,hv,hval⟩
    have hr' : r = t.2 := rvValues_injective hr
    have hv' : v = ω.2 := rvValues_injective hv
    subst r v
    simpa only [show (fun i : Fin 0 => (Fin.append (rvValues t.2) (rvValues ω.2) ∘ e)
      (Fin.castAdd 1 (Fin.castAdd (n+n) i))) = Fin.elim0 from funext (fun i => Fin.elim0 i),hrow] using hval
  · intro hv
    refine ⟨t.2,ω.2,rfl,rfl,?_⟩
    simpa only [show (fun i : Fin 0 => (Fin.append (rvValues t.2) (rvValues ω.2) ∘ e)
      (Fin.castAdd 1 (Fin.castAdd (n+n) i))) = Fin.elim0 from funext (fun i => Fin.elim0 i),hrow] using hv

theorem gamma_supported_volume_chart_value_graph
    (hc : CanonicalStructure.IsCanonical (M := M)) (A : Finset (VolumeChartSupport n))
    (C : Set (Fin (n+n) → CanonicalRV.RVSort M)) (R : Set (Fin (n+n) → M))
    (hR : DefinableOverBase B (fun _ => .rv) R)
    (hRC : ∀ t, rvValues t ∈ R ↔ t ∈ C) :
    GammaGraphDefinable B (fun (t : Point (M := M) 0 (n+n)) (ω : Point (M := M) 0 1) =>
      ∃ σ ∈ A, VolumeChartValue σ C t.2 ω.2) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    apply GammaGraphDefinable.congr (FiniteRV.gamma_empty_graph (B := B) (n+n) 1)
    intro t ω
    simp
  | insert σ A hσ ih =>
    apply GammaGraphDefinable.congr ((gammaLogicInput B).union_graph
      (gamma_volume_chart_value_graph hc σ C R hR hRC) ih)
    intro t ω
    simp only [Finset.mem_insert,or_and_right,exists_or,exists_eq_left]

end IntegrationInACVF.Section7
