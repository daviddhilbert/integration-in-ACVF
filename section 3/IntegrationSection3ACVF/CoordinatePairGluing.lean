import IntegrationSection3ACVF.CoordinateCellGluing
import IntegrationSection3ACVF.PartitionTemplateCases

/-! Disjoint parameter cases and valid scalar templates glue to an actual
finite disjoint original-base partition for one coordinate pair. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.CoordinatePairGluing

open CoordinateSlices CoordinateFibres CoordinateFibreSyntax
open CoordinateCellGluing ParameterizedOpenImages PromotedPartitionTemplates

variable {M ι τ : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem exists_partition [Finite ι] [Finite τ] (B : FullBaseAtomicity.Base (M := M))
    (A : Set (ι → M)) (f : (ι → M) → (τ → M))
    (hf : FullBaseAtomicity.OverBase B (FiniteTupleGraphs.graph A f))
    (hinj : Set.InjOn f A) (i : ι) (j : τ)
    (K : Finset (Set (Params i j → M)))
    (hK : ∀ U ∈ K, FullBaseAtomicity.OverBase B U ∧
      ∃ T : Template M (Params i j), Definable B T ∧ U ⊆ locus (CoordinatePartitionTemplates.graph A f i j) T)
    (hDisK : (K : Set (Set (Params i j → M))).Pairwise Disjoint)
    (hCovK : ∀ p : Params i j → M, ∃ U ∈ K, p ∈ U) :
    ∃ P : Finset (Set (ι → M)),
      (∀ W ∈ P, W.Nonempty ∧ W ⊆ A ∧ FullBaseAtomicity.OverBase B W ∧ CoordinateOpenToOpen.At W f i j) ∧
      (P : Set (Set (ι → M))).Pairwise Disjoint ∧ A = {x | ∃ W ∈ P, x ∈ W} := by
  classical
  choose T hTdef hTvalid using fun U : K => (hK U.val U.property).2
  let Idx := Σ U : K, Fin (T U).size
  let Q : Idx → Set (ι → M) := fun a => piece A f i j a.1.val ((T a.1).cell a.2)
  let P := (Finset.univ.image Q).filter Set.Nonempty
  have hMem (W : Set (ι → M)) : W ∈ P ↔ (∃ a : Idx, Q a = W) ∧ W.Nonempty := by
    simp only [P,Finset.mem_filter,Finset.mem_image,Finset.mem_univ,true_and]
  have hQ (a : Idx) : Q a ⊆ A ∧ FullBaseAtomicity.OverBase B (Q a) ∧ CoordinateOpenToOpen.At (Q a) f i j := by
    exact ⟨fun _ hx => hx.1,
      piece_definable B A f hf i j (hK a.1.val a.1.property).1 (hTdef a.1 a.2),
      piece_openToOpen A f hinj i j a.1.val (T a.1) (hTvalid a.1) a.2⟩
  have hDisQ : Pairwise (fun a b : Idx => Disjoint (Q a) (Q b)) := by
    rintro ⟨U,k⟩ ⟨V,l⟩ hne
    apply Set.disjoint_left.mpr
    intro x hx hy
    change x ∈ piece A f i j U.val ((T U).cell k) at hx
    change x ∈ piece A f i j V.val ((T V).cell l) at hy
    by_cases hUV : U = V
    · subst V
      have hkl : k ≠ l := fun he => hne (he ▸ rfl)
      have hp := hTvalid U hx.2.1
      have hCells : Pairwise (fun k l => Disjoint (fibre ((T U).cell k) (context f i j x))
          (fibre ((T U).cell l) (context f i j x))) := hp.1.2
      exact Set.disjoint_left.mp (@hCells k l hkl) hx.2.2 hy.2.2
    · have hSets : U.val ≠ V.val := fun he => hUV (Subtype.ext he)
      exact Set.disjoint_left.mp (hDisK U.property V.property hSets) hx.2.1 hy.2.1
  have hCover (x : ι → M) (hx : x ∈ A) : ∃ a : Idx, x ∈ Q a := by
    let p := context f i j x
    obtain ⟨U,hUK,hpU⟩ := hCovK p
    let u : K := ⟨U,hUK⟩
    have hpValid := hTvalid u hpU
    have hxD : x i ∈ fibre (UnaryRelationFamilies.domain (CoordinatePartitionTemplates.graph A f i j)) p := by
      refine ⟨f x j,?_,?_⟩
      · change insert i (tail i x) (x i) ∈ A ∧ tail j (f (insert i (tail i x) (x i))) = tail j (f x)
        rw [insert_tail]
        exact ⟨hx,rfl⟩
      · change f x j = f (insert i (tail i x) (x i)) j
        rw [insert_tail]
    obtain ⟨k,hxk⟩ := (hpValid.1.1 (x i)).mp hxD
    exact ⟨⟨u,k⟩,hx,hpU,hxk⟩
  refine ⟨P,?_,?_,?_⟩
  · intro W hW
    obtain ⟨⟨a,rfl⟩,hne⟩ := (hMem W).mp hW
    exact ⟨hne,hQ a⟩
  · intro W hWP Z hZP hWZ
    obtain ⟨⟨a,rfl⟩,_⟩ := (hMem W).mp hWP
    obtain ⟨⟨b,rfl⟩,_⟩ := (hMem Z).mp hZP
    exact @hDisQ a b (fun he => hWZ (congrArg Q he))
  · ext x
    constructor
    · intro hx
      obtain ⟨a,hxa⟩ := hCover x hx
      exact ⟨Q a,(hMem _).mpr ⟨⟨a,rfl⟩,⟨x,hxa⟩⟩,hxa⟩
    · rintro ⟨W,hW,hx⟩
      obtain ⟨⟨a,rfl⟩,_⟩ := (hMem W).mp hW
      exact (hQ a).1 hx

end IntegrationInACVF.Section3ACVF.CoordinatePairGluing
