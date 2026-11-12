import IntegrationSection6.GammaRowBijectionPromotion

/-! Realize a valid sorted chart as its actual bijection, and split a
parameterized total set into its literal dependent family of fibres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ}
variable {sp : Fin p → SortTag} {sx : Fin a → SortTag} {sy : Fin b → SortTag}
variable {D : Set (Fin (p+a) → M)} {E : Set (Fin (p+b) → M)}
variable {H : Set (Fin ((p+a)+b) → M)} {z : Fin p → M}

def bijectiveMapRowValid.map (h : bijectiveMapRowValid sp sy D E H z)
    (x : {x : Fin a → M | Fin.append z x ∈ D}) : {y : Fin b → M | Fin.append z y ∈ E} :=
  ⟨(h.1.2.1 x.val x.property).exists.choose,
    (h.2 _).mpr ⟨x.val,(h.1.2.1 x.val x.property).exists.choose_spec⟩⟩

theorem bijectiveMapRowValid.map_graph (h : bijectiveMapRowValid sp sy D E H z)
    (x : {x : Fin a → M | Fin.append z x ∈ D}) :
    Fin.append (Fin.append z x.val) (h.map x).val ∈ H :=
  (h.1.2.1 x.val x.property).exists.choose_spec

def bijectiveMapRowValid.equiv (h : bijectiveMapRowValid sp sy D E H z)
    (hE : ∀ y, Fin.append z y ∈ E → ∀ j, sortEval (sy j) (y j)) :
    {x : Fin a → M | Fin.append z x ∈ D} ≃ {y : Fin b → M | Fin.append z y ∈ E} :=
  Equiv.ofBijective h.map ⟨by
    intro x x' he
    have hy := h.unique_reverse (h.map x).val (h.map x).property (hE _ (h.map x).property)
    apply Subtype.ext
    exact hy.unique (h.map_graph x) (by rw [he]; exact h.map_graph x'),by
    intro y
    obtain ⟨x,hx⟩ := (h.2 y.val).mp y.property
    have hD := h.1.2.2.1 x y.val hx
    refine ⟨⟨x,hD⟩,Subtype.ext ?_⟩
    exact (h.1.2.1 x hD).unique (h.map_graph ⟨x,hD⟩) hx⟩

theorem bijectiveMapRowValid.equiv_graph (h : bijectiveMapRowValid sp sy D E H z)
    (hE : ∀ y, Fin.append z y ∈ E → ∀ j, sortEval (sy j) (y j)) (x : Fin a → M) (y : Fin b → M) :
    Fin.append (Fin.append z x) y ∈ H ↔
      ∃ u : {x : Fin a → M | Fin.append z x ∈ D}, u.val = x ∧ (h.equiv hE u).val = y := by
  constructor
  · intro hxy
    have hx := h.1.2.2.1 x y hxy
    refine ⟨⟨x,hx⟩,rfl,?_⟩
    exact (h.1.2.1 x hx).unique (h.map_graph ⟨x,hx⟩) hxy
  · rintro ⟨u,rfl,rfl⟩
    exact h.map_graph u

def rawRowTotal (A : Set (Fin p → M)) (D : Set (Fin (p+a) → M)) : Set (Fin (p+a) → M) :=
  {w | (w ∘ Fin.castAdd a) ∈ A ∧ w ∈ D}

def rawRowTotalEquiv (A : Set (Fin p → M)) (D : Set (Fin (p+a) → M)) :
    rawRowTotal A D ≃ (z : A) × {x : Fin a → M | Fin.append z.val x ∈ D} where
  toFun w := ⟨⟨w.val ∘ Fin.castAdd a,w.property.1⟩,⟨w.val ∘ Fin.natAdd p,by
    change Fin.append (fun j => w.val (Fin.castAdd a j)) (fun j => w.val (Fin.natAdd p j)) ∈ D
    rw [Fin.append_castAdd_natAdd];exact w.property.2⟩⟩
  invFun w := ⟨Fin.append w.1.val w.2.val,by
    change (Fin.append w.1.val w.2.val ∘ Fin.castAdd a) ∈ A ∧ _
    have he : Fin.append w.1.val w.2.val ∘ Fin.castAdd a = w.1.val :=
      funext (fun j => Fin.append_left _ _ j)
    exact ⟨he.symm ▸ w.1.property,w.2.property⟩⟩
  left_inv w := Subtype.ext Fin.append_castAdd_natAdd
  right_inv w := by
    have hb : Fin.append w.1.val w.2.val ∘ Fin.castAdd a = w.1.val :=
      funext (fun j => Fin.append_left _ _ j)
    apply Sigma.ext (Subtype.ext hb)
    apply (Subtype.heq_iff_coe_eq (fun t => by
      change Fin.append (Fin.append w.1.val w.2.val ∘ Fin.castAdd a) t ∈ D ↔ Fin.append w.1.val t ∈ D
      rw [hb])).mpr
    exact funext (fun j => Fin.append_right _ _ j)

end IntegrationInACVF.Section6
