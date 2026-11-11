import IntegrationSection5.UnaryTranslations

/-! Images of raw unary polydiscs under actual subtype maps. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m l k : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
variable {C : DefSet (M := M) S 1 k}

def unaryImage (f : A → B) (E : Set (Point (M := M) 1 m)) : Set (Point (M := M) 1 l) :=
  {q | ∃ a : A, a.val ∈ E ∧ (f a).val = q}

theorem unaryImage_subset (f : A → B) (E : Set (Point (M := M) 1 m)) :
    unaryImage f E ⊆ carrier B := by
  rintro q ⟨a, ha, rfl⟩
  exact (f a).property

theorem unaryImage_comp (f : A → B) (g : B → C) (E : Set (Point (M := M) 1 m)) :
    unaryImage (g ∘ f) E = unaryImage g (unaryImage f E) := by
  ext q
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨f a, ⟨a, ha, rfl⟩, rfl⟩
  · rintro ⟨b, ⟨a, ha, he⟩, hq⟩
    have hab : f a = b := Subtype.ext he
    exact ⟨a, ha, (congrArg (fun b : B => (g b).val) hab).trans hq⟩

theorem unaryImage_congr (f g : A → B) {E : Set (Point (M := M) 1 m)}
    (he : ∀ a : A, a.val ∈ E → f a = g a) : unaryImage f E = unaryImage g E := by
  ext q
  constructor <;> rintro ⟨a, ha, hq⟩
  · exact ⟨a, ha, (congrArg Subtype.val (he a ha)).symm.trans hq⟩
  · exact ⟨a, ha, (congrArg Subtype.val (he a ha)).trans hq⟩

def CellwiseOpenMap (f : A → B) : Prop :=
  ∀ E : Set (Point (M := M) 1 m), IsUnaryOpenPolydisc E → E ⊆ carrier A →
    (∃ a : A, ∀ p ∈ E, SameRV p a.val) → IsUnaryOpenPolydisc (unaryImage f E)

theorem cellwiseOpenMap_comp (f : A → B) (g : B → C) (hc : Contractible f)
    (hf : CellwiseOpenMap f) (hg : CellwiseOpenMap g) : CellwiseOpenMap (g ∘ f) := by
  intro E hE hEA hcell
  obtain ⟨a, ha⟩ := hcell
  rw [unaryImage_comp]
  apply hg _ (hf E hE hEA ⟨a, ha⟩) (unaryImage_subset f E)
  refine ⟨f a, ?_⟩
  rintro q ⟨b, hb, rfl⟩
  exact hc b a (ha b.val hb)

/-- Replace the RV label tuple while translating the VF coordinate. The
target label arity may differ from the source label arity. -/
def unaryReframe (c : VF (M := M)) (t : Fin l → RV (M := M))
    (p : Point (M := M) 1 m) : Point (M := M) 1 l :=
  (fun i => p.1 i - c, t)

theorem unaryReframe_open_polydisc (c : VF (M := M)) (t : Fin l → RV (M := M))
    {E : Set (Point (M := M) 1 m)} (hE : IsUnaryOpenPolydisc E) :
    IsUnaryOpenPolydisc (unaryReframe c t '' E) := by
  obtain ⟨a, r, hr, s, rfl⟩ := hE
  refine ⟨a - c, r, hr, t, ?_⟩
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    have he : (vfAt p 0 - c) - (a - c) = vfAt p 0 - a := by abel
    change (¬ iLe (rv ((vfAt p 0 - c) - (a - c))).val (rv r).val) ∧ t = t
    rw [he]
    exact ⟨hp.1, rfl⟩
  · intro hq
    let p : Point (M := M) 1 m := (fun i => q.1 i + c, s)
    refine ⟨p, ?_, ?_⟩
    · have he : vfAt p 0 - a = vfAt q 0 - (a - c) := by
        change (q.1 0 + c) - a = q.1 0 - (a - c)
        abel
      change (¬ iLe (rv (vfAt p 0 - a)).val (rv r).val) ∧ s = s
      rw [he]
      exact ⟨hq.1, rfl⟩
    · refine Prod.ext ?_ hq.2.symm
      funext i
      exact add_sub_cancel_right _ _

theorem unaryReframe_open_iff (c : VF (M := M)) (t : Fin l → RV (M := M))
    (s : Fin m → RV (M := M)) (E : Set (Point (M := M) 1 m))
    (hlabel : ∀ p ∈ E, p.2 = s) :
    IsUnaryOpenPolydisc E ↔ IsUnaryOpenPolydisc (unaryReframe c t '' E) := by
  have hcomp (p : Point (M := M) 1 m) (hp : p ∈ E) :
      unaryReframe (-c) s (unaryReframe c t p) = p := by
    refine Prod.ext ?_ (hlabel p hp).symm
    funext i
    change (p.1 i - c) - (-c) = p.1 i
    abel
  have hback : unaryReframe (-c) s '' (unaryReframe c t '' E) = E := by
    ext p
    constructor
    · rintro ⟨q, ⟨r, hr, rfl⟩, he⟩
      rw [hcomp r hr] at he
      exact he ▸ hr
    · intro hp
      exact ⟨unaryReframe c t p, ⟨p, hp, rfl⟩, hcomp p hp⟩
  refine ⟨unaryReframe_open_polydisc c t, ?_⟩
  intro h
  have hb := unaryReframe_open_polydisc (-c) s h
  exact hback ▸ hb

end IntegrationInACVF.Section5
