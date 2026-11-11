import IntegrationSection5.UnaryPaperBallBridge
import IntegrationSection5.UnaryConjugationGeometry
import IntegrationSection3ACVF.CoordinateOpenToOpen
import Section5.VerticalConstruction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

theorem pointValues_injective {n m : ℕ} :
    Function.Injective (pointValues (M := M) (n := n) (m := m)) := by
  intro p q he
  apply Prod.ext
  · funext i; exact Subtype.ext (congrFun he (.inl i))
  · funext i; exact Subtype.ext (congrFun he (.inr i))

def unaryTupleMap (f : A → B) (x : Fin 1 ⊕ Fin m → M) : Fin 1 ⊕ Fin l → M :=
  if h : ∃ a : A, pointValues a.val = x then pointValues (f h.choose).val
  else pointValues (unaryInsert (fun _ => rv (0 : VF (M := M))) 0)

theorem unaryTupleMap_apply (f : A → B) (a : A) :
    unaryTupleMap f (pointValues a.val) = pointValues (f a).val := by
  have h : ∃ b : A, pointValues b.val = pointValues a.val := ⟨a,rfl⟩
  rw [unaryTupleMap,dite_eq_left h]
  have he : h.choose = a := Subtype.ext (pointValues_injective h.choose_spec)
  rw [he]

theorem pointValues_tail_eq {p q : Point (M := M) 1 m} (h : p.2 = q.2) :
    CoordinateSlices.tail (.inl 0) (pointValues p) =
      CoordinateSlices.tail (.inl 0) (pointValues q) := by
  funext j
  rcases j with ⟨i,hi⟩
  cases i with
  | inl i => exact (hi (congrArg Sum.inl (Subsingleton.elim _ _))).elim
  | inr i => exact congrArg Subtype.val (congrFun h i)

theorem unaryTuple_insert (p a : Point (M := M) 1 m) (h : p.2 = a.2) :
    CoordinateSlices.insert (.inl 0) (CoordinateSlices.tail (.inl 0) (pointValues a))
      (vfAt p 0).val = pointValues p := by
  rw [← pointValues_tail_eq h]
  exact CoordinateSlices.insert_tail _ _

theorem coordinate_shadow_image (f : A → B) (E : Set (Point (M := M) 1 m))
    (hEA : E ⊆ carrier A) (a : Point (M := M) 1 m) (hlabel : ∀ p ∈ E, p.2 = a.2) :
    CoordinateFibres.map (unaryTupleMap f) (.inl 0) (.inl 0)
      (CoordinateSlices.tail (.inl 0) (pointValues a)) '' vfShadow E = vfShadow (unaryImage f E) := by
  ext y
  constructor
  · rintro ⟨x,⟨p,hp,rfl⟩,rfl⟩
    let b : A := ⟨p,hEA hp⟩
    have he : CoordinateFibres.map (unaryTupleMap f) (.inl 0) (.inl 0)
        (CoordinateSlices.tail (.inl 0) (pointValues a)) (vfAt p 0).val =
        (vfAt (f b).val 0).val := by
      unfold CoordinateFibres.map
      rw [unaryTuple_insert p a (hlabel p hp),unaryTupleMap_apply f b]
      rfl
    exact ⟨(f b).val,⟨b,hp,rfl⟩,he.symm⟩
  · rintro ⟨q,⟨b,hb,rfl⟩,rfl⟩
    refine ⟨(vfAt b.val 0).val,⟨b.val,hb,rfl⟩,?_⟩
    unfold CoordinateFibres.map
    rw [unaryTuple_insert b.val a (hlabel b.val hb),unaryTupleMap_apply]
    rfl

theorem coordinate_piece_open_iff (f : A → B)
    (W : Set (Fin 1 ⊕ Fin m → M))
    (h : CoordinateOpenToOpen.At W (unaryTupleMap f) (.inl 0) (.inl 0))
    (E : Set (Point (M := M) 1 m)) (hEA : E ⊆ carrier A)
    (hEW : ∀ p ∈ E, pointValues p ∈ W)
    (hcell : ∃ a : A, ∀ p ∈ E, SameRV p a.val)
    (himage : ∃ b : B, ∀ q ∈ unaryImage f E, SameRV q b.val) :
    IsUnaryOpenPolydisc E ↔ IsUnaryOpenPolydisc (unaryImage f E) := by
  obtain ⟨a,ha⟩ := hcell
  obtain ⟨b,hb⟩ := himage
  have hlabel : ∀ p ∈ E, p.2 = a.val.2 := fun p hp => ((sameRV_iff _ _).mp (ha p hp)).2
  have hlabel' : ∀ q ∈ unaryImage f E, q.2 = b.val.2 := fun q hq => ((sameRV_iff _ _).mp (hb q hq)).2
  rw [vfShadow_polydisc_iff E a.val.2 hlabel (vfShadow_ne_whole_of_cell E a.val ha),
    vfShadow_polydisc_iff (unaryImage f E) b.val.2 hlabel'
      (vfShadow_ne_whole_of_cell (unaryImage f E) b.val hb)]
  have hsub : vfShadow E ⊆ CoordinateFibres.source W (unaryTupleMap f)
      (.inl 0) (.inl 0) (CoordinateSlices.tail (.inl 0) (pointValues a.val))
      (CoordinateSlices.tail (.inl 0) (pointValues b.val)) := by
    rintro x ⟨p,hp,rfl⟩
    let c : A := ⟨p,hEA hp⟩
    have hout := hlabel' (f c).val ⟨c,hp,rfl⟩
    constructor
    · rw [unaryTuple_insert p a.val (hlabel p hp)]
      exact hEW p hp
    · rw [unaryTuple_insert p a.val (hlabel p hp),unaryTupleMap_apply f c]
      exact pointValues_tail_eq hout
  have ho := h (CoordinateSlices.tail (.inl 0) (pointValues a.val))
    (CoordinateSlices.tail (.inl 0) (pointValues b.val)) (vfShadow E) hsub
  rw [coordinate_shadow_image f E hEA a.val hlabel] at ho
  exact ho
theorem coordinate_open_to_cellwise (f : A → B)
    (h : CoordinateOpenToOpen.At (pointValues '' carrier A) (unaryTupleMap f) (.inl 0) (.inl 0)) :
    CellwiseOpenEquivalence f := by
  intro E hEA hcell himage
  exact coordinate_piece_open_iff f _ h E hEA (fun p hp => ⟨p,hEA hp,rfl⟩) hcell himage

end IntegrationInACVF.Section5

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m l r : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
variable {A' : DefSet (M := M) S 1 r}

theorem refined_coordinate_open_to_cellwise (f : Map A B) (T : SpecialBijection A A')
    (P : Finset (Set (Fin 1 ⊕ Fin m → M)))
    (hP : ∀ W ∈ P, CoordinateOpenToOpen.At W (unaryTupleMap f) (.inl 0) (.inl 0))
    (hPure : ∀ a : A', ∃ W ∈ P, ∀ b : A', SameRV b.val a.val →
      pointValues (T.inverseMap b).val ∈ W) :
    CellwiseOpenEquivalence (Map.comp f T.inverseMap) := by
  intro E hEA hcell hImage
  obtain ⟨a,ha⟩ := hcell
  obtain ⟨W,hWP,hW⟩ := hPure a
  have hlabel : ∀ p ∈ E, p.2 = a.val.2 := fun p hp => ((sameRV_iff _ _).mp (ha p hp)).2
  have hEq : unaryImage (Map.comp f T.inverseMap) E = unaryImage f (unaryImage T.inverseMap E) :=
    unaryImage_comp T.inverseMap f E
  have hOldCell : ∃ a : A, ∀ p ∈ unaryImage T.inverseMap E, SameRV p a.val := by
    refine ⟨T.inverseMap a,?_⟩
    rintro p ⟨b,hb,rfl⟩
    exact T.inverse_contractible b a (ha b.val hb)
  have hOldPiece : ∀ p ∈ unaryImage T.inverseMap E, pointValues p ∈ W := by
    rintro p ⟨b,hb,rfl⟩
    exact hW b (ha b.val hb)
  have hh := coordinate_piece_open_iff f W (hP W hWP) (unaryImage T.inverseMap E)
    (unaryImage_subset T.inverseMap E) hOldPiece hOldCell (hEq ▸ hImage)
  exact (inverse_special_open_iff T a E hEA hlabel).trans (hEq.symm ▸ hh)

end IntegrationInACVF.Section5

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m l r s : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
variable {A' : DefSet (M := M) S 1 r} {B' : DefSet (M := M) S 1 s}

theorem refined_conjugate_coordinate_geometry (f : Map A B)
    (T : SpecialBijection A A') (V : SpecialBijection B B')
    (P : Finset (Set (Fin 1 ⊕ Fin m → M)))
    (hP : ∀ W ∈ P, CoordinateOpenToOpen.At W (unaryTupleMap f) (.inl 0) (.inl 0))
    (hPure : ∀ a : A', ∃ W ∈ P, ∀ b : A', SameRV b.val a.val →
      pointValues (T.inverseMap b).val ∈ W) :
    CellwiseOpenEquivalence (unaryConjugate T V f) := by
  intro E hEA hcell hImage
  obtain ⟨a,ha⟩ := hcell
  obtain ⟨b,hb⟩ := hImage
  obtain ⟨W,hWP,hW⟩ := hPure a
  let D := unaryImage T.inverseMap E
  let F := unaryImage (unaryConjugate T V f) E
  have hDcell : ∃ a : A, ∀ p ∈ D, SameRV p a.val := by
    refine ⟨T.inverseMap a,?_⟩
    rintro p ⟨c,hc,rfl⟩
    exact T.inverse_contractible c a (ha c.val hc)
  have hFcell : ∃ b : B, ∀ q ∈ unaryImage f D, SameRV q b.val := by
    refine ⟨V.inverseMap b,?_⟩
    rw [unaryConjugate_image T V f E]
    rintro p ⟨c,hc,rfl⟩
    exact V.inverse_contractible c b (hb c.val hc)
  have hDpiece : ∀ p ∈ D, pointValues p ∈ W := by
    rintro p ⟨c,hc,rfl⟩
    exact hW c (ha c.val hc)
  have hOld := coordinate_piece_open_iff f W (hP W hWP) D
    (unaryImage_subset T.inverseMap E) hDpiece hDcell hFcell
  have hSrc := inverse_special_open_iff T a E hEA
    (fun p hp => ((sameRV_iff _ _).mp (ha p hp)).2)
  have hTar := inverse_special_open_iff V b F (unaryImage_subset (unaryConjugate T V f) E)
    (fun p hp => ((sameRV_iff _ _).mp (hb p hp)).2)
  rw [unaryConjugate_image T V f E] at hOld
  exact (hSrc.trans hOld).trans hTar.symm

end IntegrationInACVF.Section5
