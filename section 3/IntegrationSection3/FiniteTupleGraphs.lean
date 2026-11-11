module

public import IntegrationSection3.FiniteDefinablePatching

@[expose] public section

/-! Same-base partial tuple graphs, composition, and a proved inverse.
The output functions are totalized only outside their stated domains. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language

namespace IntegrationInACVF.Section3.FiniteTupleGraphs

def graph {K ι κ : Type*} (S : Set (ι → K)) (f : (ι → K) → (κ → K)) :
    Set (ι ⊕ κ → K) := {z | z ∘ Sum.inl ∈ S ∧ z ∘ Sum.inr = f (z ∘ Sum.inl)}

theorem comp {K ι κ τ : Type*} (L : Language) [L.Structure K]
    [Finite ι] [Finite κ] [Finite τ] (C : Set K)
    {S : Set (ι → K)} {T : Set (κ → K)}
    (f : (ι → K) → (κ → K)) (g : (κ → K) → (τ → K))
    (hf : C.Definable L (graph S f)) (hg : C.Definable L (graph T g))
    (hm : S.MapsTo f T) : C.Definable L (graph S (g ∘ f)) := by
  let fi : ι ⊕ κ → (ι ⊕ τ) ⊕ κ :=
    Sum.elim (fun i => .inl (.inl i)) (fun j => .inr j)
  let gi : κ ⊕ τ → (ι ⊕ τ) ⊕ κ :=
    Sum.elim (fun j => .inr j) (fun i => .inl (.inr i))
  have hd := ((hf.preimage_comp fi).inter (hg.preimage_comp gi)).exists_of_finite
  convert hd using 1
  ext z
  change (z ∘ Sum.inl ∈ S ∧ z ∘ Sum.inr = g (f (z ∘ Sum.inl))) ↔
    ∃ w : κ → K, (z ∘ Sum.inl ∈ S ∧ w = f (z ∘ Sum.inl)) ∧
      (w ∈ T ∧ z ∘ Sum.inr = g w)
  exact ⟨fun ⟨hx,he⟩ => ⟨f (z ∘ Sum.inl),⟨hx,rfl⟩,hm hx,he⟩,
    fun ⟨w,⟨hx,hw⟩,_,he⟩ => ⟨hx,hw ▸ he⟩⟩

theorem inverse {K ι κ : Type*} (L : Language) [L.Structure K] [Inhabited K]
    [Finite ι] [Finite κ] (C : Set K)
    {S : Set (ι → K)} {T : Set (κ → K)} (f : (ι → K) → (κ → K))
    (hf : C.Definable L (graph S f)) (hbij : Set.BijOn f S T) :
    ∃ g : (κ → K) → (ι → K), C.Definable L (graph T g) ∧ Set.BijOn g T S ∧
      (∀ x ∈ S, g (f x) = x) ∧ (∀ y ∈ T, f (g y) = y) := by
  let g : (κ → K) → (ι → K) := fun y =>
    if hy : y ∈ T then Classical.choose (hbij.2.2 hy) else default
  have hg (y : κ → K) (hy : y ∈ T) : g y ∈ S ∧ f (g y) = y := by
    dsimp only [g]
    rw [dif_pos hy]
    exact Classical.choose_spec (hbij.2.2 hy)
  have hleft (x : ι → K) (hx : x ∈ S) : g (f x) = x :=
    hbij.2.1 (hg _ (hbij.1 hx)).1 hx (hg _ (hbij.1 hx)).2
  have hGraph : C.Definable L (graph T g) := by
    convert hf.preimage_comp (Sum.swap : ι ⊕ κ → κ ⊕ ι) using 1
    ext z
    change (z ∘ Sum.inl ∈ T ∧ z ∘ Sum.inr = g (z ∘ Sum.inl)) ↔
      (z ∘ Sum.inr ∈ S ∧ z ∘ Sum.inl = f (z ∘ Sum.inr))
    constructor
    · rintro ⟨hy,he⟩
      rw [he]
      exact ⟨(hg _ hy).1,(hg _ hy).2.symm⟩
    · rintro ⟨hx,he⟩
      refine ⟨he.symm ▸ hbij.1 hx,?_⟩
      rw [he,hleft _ hx]
  refine ⟨g,hGraph,⟨fun y hy => (hg y hy).1,?_,?_⟩,hleft,fun y hy => (hg y hy).2⟩
  · intro x hx y hy he
    exact (hg x hx).2.symm.trans ((congrArg f he).trans (hg y hy).2)
  · intro x hx
    exact ⟨f x,hbij.1 hx,hleft x hx⟩

end IntegrationInACVF.Section3.FiniteTupleGraphs
