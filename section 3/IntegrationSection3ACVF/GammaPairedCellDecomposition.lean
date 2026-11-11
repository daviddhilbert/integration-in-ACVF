import IntegrationSection3ACVF.GammaPairedCellSetup
import IntegrationSection3ACVF.GammaCellDecomposition
import IntegrationSection3ACVF.OrderedPairedCellGeometry

/-! Actual paired finite point/open-cell decompositions for a definable
Gamma bijection from a closed interval. Every cell, right endpoint and
point-count equality is constructed from the actual partial graph. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section3ACVF.GammaPairedCellDecomposition

open FullGammaSyntax FiniteOrderCells FiniteOrderCellPartition OrderedPairedCellGeometry

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem exists_paired {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (a b : Values.Gamma (M := M)) (hab : a ≤ b) (J : Set (Values.Gamma (M := M)))
    (hJConn : OrdConnected J) (ν : Values.Gamma (M := M)) (hGreatest : IsGreatest J ν)
    (f : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hG : Definable B (GammaFunctionSyntax.graph (Set.Icc a b) f))
    (hBij : Set.BijOn f (Set.Icc a b) J) :
    ∃ G : Finset (Values.Gamma (M := M)),
      ∃ K : OrderedCellDecomposition.Data (Set.Icc a b) (Index G J),
      ∃ L : OrderedCellDecomposition.Data J (Index G J), K.points.card = L.points.card := by
  classical
  let D := Set.Icc a b
  obtain ⟨F,G,haF,hbF,hF,hMono,hImagePoints,hGJ,hImages⟩ :=
    GammaPairedCellSetup.exists_controllers hκ hs h00 B hsmall a b J f hG hBij
  let ι := Index G J
  let T : ι → Set (Values.Gamma (M := M)) := fun c => cell G c.val
  let S : ι → Set (Values.Gamma (M := M)) := fun c => OrderedMonotonePreimages.pullback D f (T c)
  let PT := G.filter (· ∈ J)
  have hPTSub : (PT : Set (Values.Gamma (M := M))) ⊆ J := fun x hx => (Finset.mem_filter.mp hx).2
  let P : Set (Values.Gamma (M := M)) := D ∩ f ⁻¹' (PT : Set (Values.Gamma (M := M)))
  have hBijP : Set.BijOn f P (PT : Set (Values.Gamma (M := M))) := by
    refine ⟨fun x hx => hx.2,?_,?_⟩
    · intro x hx y hy he
      exact hBij.2.1 hx.1 hy.1 he
    · intro y hy
      obtain ⟨x,hx,he⟩ := hBij.2.2 (hPTSub hy)
      exact ⟨x,⟨hx,by change f x ∈ PT; rw [he]; exact hy⟩,he⟩
  have hPFinite : P.Finite := hBijP.finite_iff_finite.mpr PT.finite_toSet
  let PS := hPFinite.toFinset
  have hTCover (x : Values.Gamma (M := M)) : x ∈ J ↔ x ∈ PT ∨ ∃ c : ι, x ∈ T c := by
    constructor
    · intro hx
      rcases point_or_cell hGJ x hx with h | ⟨c,hc⟩
      · exact Or.inl (Finset.mem_filter.mpr ⟨h,hx⟩)
      · exact Or.inr ⟨c,hc⟩
    · rintro (hx | ⟨c,hc⟩)
      · exact hPTSub hx
      · exact c.property.2 hc
  have hSCover (x : Values.Gamma (M := M)) : x ∈ D ↔ x ∈ PS ∨ ∃ c : ι, x ∈ S c := by
    constructor
    · intro hx
      rcases (pullbacks_cover D J f G hGJ hBij.1 x).mp hx with h | h
      · exact Or.inl (hPFinite.mem_toFinset.mpr ⟨h.1,Finset.mem_filter.mpr ⟨h.2,hBij.1 h.1⟩⟩)
      · exact Or.inr h
    · rintro (hx | ⟨c,hc⟩)
      · exact (hPFinite.mem_toFinset.mp hx).1
      · exact hc.1
  have hSGeometry (c : ι) : (S c).Nonempty ∧ OrdConnected (S c) ∧
      (∀ x ∈ S c, ∃ y ∈ S c, y < x) ∧ (∀ x ∈ S c, ∃ y ∈ S c, x < y) := by
    obtain ⟨j,hj⟩ := target_cell_inside_image D J f F G hF hBij hImagePoints hImages c
    have hAD := j.property.2
    have hConnected := OrderedMonotonePreimages.connected D (cell F j.val) f (T c)
      hAD hBij.2.1 hj (FiniteOrderCells.connected F j.val) (FiniteOrderCells.connected G c.val) (hMono j)
    have hEnds := OrderedMonotonePreimages.no_endpoints D (cell F j.val) f (T c) hAD hBij.2.1 hj
      (hMono j) (fun x hx => (no_endpoints G c.val x hx).1) (fun x hx => (no_endpoints G c.val x hx).2)
    exact ⟨OrderedMonotonePreimages.nonempty D (cell F j.val) f (T c) hAD hj c.property.1,
      hConnected,fun x hx => (hEnds x hx).1,fun x hx => (hEnds x hx).2⟩
  have hTDef (c : ι) : ∃ C : FullBaseAtomicity.Base (M := M), Scalar C (T c) :=
    ⟨GammaTupleParameters.extend B (fun t : G => t.val),GammaOrderCellSyntax.cell_definable B G c.val⟩
  have hSDef (c : ι) : ∃ C : FullBaseAtomicity.Base (M := M), Scalar C (S c) := by
    let C := GammaTupleParameters.extend B (fun t : G => t.val)
    exact ⟨C,GammaFunctionSets.preimage_definable C D (T c) f
      (GammaTupleParameters.mono B (fun t : G => t.val) hG) (GammaOrderCellSyntax.cell_definable B G c.val)⟩
  have hTPoints (c : ι) : Disjoint (PT : Set (Values.Gamma (M := M))) (T c) := by
    apply Set.disjoint_left.mpr
    intro x hx hxc
    exact hxc.1 (Finset.mem_filter.mp hx).1
  have hSPoints (c : ι) : Disjoint (PS : Set (Values.Gamma (M := M))) (S c) := by
    apply Set.disjoint_left.mpr
    intro x hx hxc
    have hfxPT := (hPFinite.mem_toFinset.mp hx).2
    exact hxc.2.1 (Finset.mem_filter.mp hfxPT).1
  obtain ⟨K,hKP,hKC⟩ := GammaCellDecomposition.of_cells h00 D Set.ordConnected_Icc b
    ⟨⟨hab,le_rfl⟩,fun x hx => hx.2⟩ PS S hSCover hSPoints
    (pullbacks_disjoint D f G) (fun c => (hSGeometry c).1) (fun c => (hSGeometry c).2.1)
    (fun c => (hSGeometry c).2.2.1) (fun c => (hSGeometry c).2.2.2) hSDef
  obtain ⟨L,hLP,hLC⟩ := GammaCellDecomposition.of_cells h00 J hJConn ν hGreatest PT T hTCover hTPoints
    (fun c d hcd => FiniteOrderCells.disjoint G c.val d.val (fun he => hcd (Subtype.ext he)))
    (fun c => c.property.1) (fun c => FiniteOrderCells.connected G c.val)
    (fun c x hx => (no_endpoints G c.val x hx).1) (fun c x hx => (no_endpoints G c.val x hx).2) hTDef
  refine ⟨G,K,L,?_⟩
  rw [hKP,hLP]
  have hCount := hBijP.ncard_eq
  simpa only [Set.ncard_eq_toFinset_card P hPFinite,Set.ncard_coe_finset] using hCount

end IntegrationInACVF.Section3ACVF.GammaPairedCellDecomposition
