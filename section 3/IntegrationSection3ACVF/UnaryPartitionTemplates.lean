import IntegrationSection3ACVF.ParameterizedOpenToOpen

/-! A finite tuple of formulas is a partition template. Its validity is
an original-base definable condition on the free context labels. Empty
cells and the zero-cell template are allowed before global filtering. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.UnaryPartitionTemplates

open UnaryRelationFamilies ParameterizedOpenImages ParameterizedOpenToOpen

variable {M σ τ : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def covers (G : Set (σ ⊕ Fin 2 → M)) (T : τ → Set (σ ⊕ Fin 1 → M)) : Set (σ → M) :=
  {p | ∀ x, x ∈ fibre (domain G) p ↔ ∃ i, x ∈ fibre (T i) p}

def disjointCells (T : τ → Set (σ ⊕ Fin 1 → M)) : Set (σ → M) :=
  {p | Pairwise (fun i j => Disjoint (fibre (T i) p) (fibre (T j) p))}

def valid (G : Set (σ ⊕ Fin 2 → M)) (T : τ → Set (σ ⊕ Fin 1 → M)) : Set (σ → M) :=
  covers G T ∩ disjointCells T ∩ {p | ∀ i, p ∈ twoWay G (T i)}

theorem covers_definable [Finite σ] [Finite τ] (B : FullBaseAtomicity.Base (M := M))
    {G : Set (σ ⊕ Fin 2 → M)} (hG : FullBaseAtomicity.OverBase B G)
    {T : τ → Set (σ ⊕ Fin 1 → M)} (hT : ∀ i, FullBaseAtomicity.OverBase B (T i)) :
    FullBaseAtomicity.OverBase B (covers G T) := by
  have hd := FullBaseAtomicity.OverBase.forall_block (FullBaseLogic.equivalence B
    (domain_definable B hG) (FullBaseLogic.exists_finite B hT))
  apply FullBaseAtomicity.OverBase.congr hd
  intro p
  have he (x : Fin 1 → M) : x = ![x 0] := by funext k; fin_cases k; rfl
  change (∀ x : Fin 1 → M, Sum.elim p x ∈ domain G ↔ ∃ i, Sum.elim p x ∈ T i) ↔ _
  constructor
  · intro h x
    exact h ![x]
  · intro h x
    rw [he x]
    exact h (x 0)

theorem disjointCells_definable [Finite σ] [Finite τ] (B : FullBaseAtomicity.Base (M := M))
    {T : τ → Set (σ ⊕ Fin 1 → M)} (hT : ∀ i, FullBaseAtomicity.OverBase B (T i)) :
    FullBaseAtomicity.OverBase B (disjointCells T) := by
  have hPair (q : τ × τ) : FullBaseAtomicity.OverBase B
      {p : σ → M | q.1 ≠ q.2 → Disjoint (fibre (T q.1) p) (fibre (T q.2) p)} := by
    by_cases he : q.1 = q.2
    · have hu : FullBaseAtomicity.OverBase B (Set.univ : Set (σ → M)) := by
        apply FullBaseAtomicity.OverBase.of_real
        letI := @CanonicalStructure.normalize M sM
        exact Set.definable_univ
      apply FullBaseAtomicity.OverBase.congr hu
      intro p
      simp only [Set.mem_univ,Set.mem_ofPred_eq,he,ne_eq,not_true_eq_false,false_implies]
    · have hd := FullBaseAtomicity.OverBase.forall_block
        (FullBaseAtomicity.OverBase.compl (FullBaseAtomicity.OverBase.inter (hT q.1) (hT q.2)))
      apply FullBaseAtomicity.OverBase.congr hd
      intro p
      have hη (x : Fin 1 → M) : x = ![x 0] := by funext k; fin_cases k; rfl
      change (∀ x : Fin 1 → M, ¬ (Sum.elim p x ∈ T q.1 ∧ Sum.elim p x ∈ T q.2)) ↔ _
      constructor
      · intro h _
        exact Set.disjoint_left.mpr (fun x hx hy => h ![x] ⟨hx,hy⟩)
      · intro h x hx
        rw [hη x] at hx
        exact Set.disjoint_left.mp (h he) hx.1 hx.2
  have hd := FullBaseAtomicity.OverBase.forall_finite hPair
  apply FullBaseAtomicity.OverBase.congr hd
  intro p
  exact ⟨fun h i j hij => h (i,j) hij,fun h q => @h q.1 q.2⟩

theorem valid_definable [Finite σ] [Finite τ] (B : FullBaseAtomicity.Base (M := M))
    {G : Set (σ ⊕ Fin 2 → M)} (hG : FullBaseAtomicity.OverBase B G)
    {T : τ → Set (σ ⊕ Fin 1 → M)} (hT : ∀ i, FullBaseAtomicity.OverBase B (T i)) :
    FullBaseAtomicity.OverBase B (valid G T) :=
  FullBaseAtomicity.OverBase.inter (FullBaseAtomicity.OverBase.inter
    (covers_definable B hG hT) (disjointCells_definable B hT))
    (FullBaseAtomicity.OverBase.forall_finite (fun i => twoWay_definable B hG (hT i)))

theorem valid_iff (G : Set (σ ⊕ Fin 2 → M)) (T : τ → Set (σ ⊕ Fin 1 → M))
    (p : σ → M) (A : Set M) (f : M → M)
    (hG : ∀ x y, pair p x y ∈ G ↔ x ∈ A ∧ y = f x) (hinj : Set.InjOn f A) :
    p ∈ valid G T ↔
      (∀ x, x ∈ A ↔ ∃ i, x ∈ fibre (T i) p) ∧
      Pairwise (fun i j => Disjoint (fibre (T i) p) (fibre (T j) p)) ∧
      ∀ i, MaximalOpenClasses.OpenToOpen (fibre (T i) p) f := by
  have hDom (x : M) : x ∈ fibre (domain G) p ↔ x ∈ A := by
    change (∃ y, pair p x y ∈ G) ↔ x ∈ A
    simp_rw [hG]
    exact ⟨fun ⟨_,hx,_⟩ => hx,fun hx => ⟨f x,hx,rfl⟩⟩
  constructor
  · rintro ⟨⟨hCov,hDis⟩,hGood⟩
    have hCover (x : M) : x ∈ A ↔ ∃ i, x ∈ fibre (T i) p := (hDom x).symm.trans (hCov x)
    refine ⟨hCover,hDis,fun i => ?_⟩
    exact (twoWay_iff p A f hG (fun x hx => (hCover x).mpr ⟨i,hx⟩) hinj).mp (hGood i)
  · rintro ⟨hCov,hDis,hGood⟩
    refine ⟨⟨fun x => (hDom x).trans (hCov x),hDis⟩,fun i => ?_⟩
    exact (twoWay_iff p A f hG (fun x hx => (hCov x).mpr ⟨i,hx⟩) hinj).mpr (hGood i)

end IntegrationInACVF.Section3ACVF.UnaryPartitionTemplates
