module

public import IntegrationSection3.FiniteTupleGraphs

@[expose] public section

/-! Finite disjoint families of affine lines, encoded by an actual field
coordinate for the tag. Every finite relabelling has its complete graph
definable after naming its finite scalar labels. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language

namespace IntegrationInACVF.Section3.TaggedLineMaps

variable {K : Type*} [Field K]

def space (P : Finset K) : Set (Fin 2 → K) := {x | x 1 ∈ P}

noncomputable def transport {P Q : Finset K} (e : P ↪ Q) (x : Fin 2 → K) : Fin 2 → K :=
  ![x 0,if hx : x 1 ∈ P then (e ⟨x 1,hx⟩).val else 0]

theorem mapsTo {P Q : Finset K} (e : P ↪ Q) : (space P).MapsTo (transport e) (space Q) := by
  intro x hx
  change x 1 ∈ P at hx
  change (if h : x 1 ∈ P then (e ⟨x 1,h⟩).val else 0) ∈ Q
  rw [dif_pos hx]
  exact (e ⟨x 1,hx⟩).property

theorem injOn {P Q : Finset K} (e : P ↪ Q) : (space P).InjOn (transport e) := by
  intro x hx y hy he
  change x 1 ∈ P at hx
  change y 1 ∈ P at hy
  have h0 : x 0 = y 0 := congrFun he 0
  have h1 : (e ⟨x 1,hx⟩).val = (e ⟨y 1,hy⟩).val := by
    simpa only [transport,Matrix.cons_val_one,Matrix.cons_val_zero,dif_pos hx,dif_pos hy] using congrFun he 1
  have hl : x 1 = y 1 := congrArg Subtype.val (e.injective (Subtype.ext h1))
  funext i
  fin_cases i
  · exact h0
  · exact hl

theorem graph_definable [FirstOrder.Ring.CompatibleRing K]
    {P Q : Finset K} (e : P ↪ Q) :
    (Set.univ : Set K).Definable Language.ring (FiniteTupleGraphs.graph (space P) (transport e)) := by
  have hd (p : P) : (Set.univ : Set K).Definable Language.ring
      {z : Fin 2 ⊕ Fin 2 → K | z (.inl 1) = p.val ∧
        z (.inr 1) = (e p).val ∧ z (.inr 0) = z (.inl 0)} := by
    exact ((Set.DefinableFun.proj Language.ring).ofPred_eq
      (Language.ring.definableFun_const _ (Set.mem_univ p.val))).inter
      (((Set.DefinableFun.proj Language.ring).ofPred_eq
        (Language.ring.definableFun_const _ (Set.mem_univ (e p).val))).inter
        ((Set.DefinableFun.proj Language.ring).ofPred_eq (Set.DefinableFun.proj Language.ring)))
  have hUnion := Set.definable_iUnion_of_finite hd
  convert hUnion using 1
  ext z
  simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
  change (z (.inl 1) ∈ P ∧ z ∘ Sum.inr = transport e (z ∘ Sum.inl)) ↔
    ∃ p : P, z (.inl 1) = p.val ∧ z (.inr 1) = (e p).val ∧ z (.inr 0) = z (.inl 0)
  constructor
  · rintro ⟨hx,he⟩
    refine ⟨⟨z (.inl 1),hx⟩,rfl,?_,congrFun he 0⟩
    simpa only [transport,Matrix.cons_val_one,Matrix.cons_val_zero,Function.comp_def,dif_pos hx] using congrFun he 1
  · rintro ⟨p,hp,he1,he0⟩
    have hx : z (.inl 1) ∈ P := hp.symm ▸ p.property
    refine ⟨hx,?_⟩
    funext i
    fin_cases i
    · exact he0
    · change z (.inr 1) = if h : z (.inl 1) ∈ P then (e ⟨z (.inl 1),h⟩).val else 0
      rw [dif_pos hx]
      have he : (⟨z (.inl 1),hx⟩ : P) = p := Subtype.ext hp
      rw [he]
      exact he1

theorem missing_line_infinite [Infinite K] {P Q : Finset K} (e : P ↪ Q)
    (p : Q) (hp : p ∉ Set.range e) : (space Q \ transport e '' space P).Infinite := by
  have hInf : (Set.range (fun t : K => (![t,p.val] : Fin 2 → K))).Infinite :=
    Set.infinite_range_of_injective (fun x y he => congrFun he 0)
  apply hInf.mono
  rintro z ⟨t,rfl⟩
  refine ⟨p.property,?_⟩
  rintro ⟨x,hx,he⟩
  change x 1 ∈ P at hx
  apply hp
  refine ⟨⟨x 1,hx⟩,Subtype.ext ?_⟩
  simpa only [transport,Matrix.cons_val_one,Matrix.cons_val_zero,dif_pos hx] using congrFun he 1

theorem surjOn {P Q : Finset K} (e : P ↪ Q) (he : Function.Surjective e) :
    (space P).SurjOn (transport e) (space Q) := by
  intro y hy
  obtain ⟨p,hp⟩ := he ⟨y 1,hy⟩
  refine ⟨![y 0,p.val],p.property,?_⟩
  funext i
  fin_cases i
  · rfl
  · change (if h : p.val ∈ P then (e ⟨p.val,h⟩).val else 0) = y 1
    rw [dif_pos p.property]
    exact congrArg Subtype.val hp

end IntegrationInACVF.Section3.TaggedLineMaps
