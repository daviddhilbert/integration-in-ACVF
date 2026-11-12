import IntegrationSection6.GammaSortedBijectionRealization

/-! A uniform family of sorted bijections gives an actual original-base
bijection of total sets, preserving every parameter coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ}
variable {sp : Fin p → SortTag} {sx : Fin a → SortTag} {sy : Fin b → SortTag}
variable {D : Set (Fin (p+a) → M)} {E : Set (Fin (p+b) → M)} {A : Set (Fin p → M)}

structure GammaSortedIso (B : Base (M := M)) (sa : Fin a → SortTag) (sb : Fin b → SortTag)
    (D : Set (Fin a → M)) (E : Set (Fin b → M)) where
  equiv : D ≃ E
  graph : DefinableOverBase B (Fin.append sa sb)
    {w | ∃ u : D, Fin.append u.val (equiv u).val = w}

def repeatBaseCoordinates (p a b : ℕ) : Fin ((p+a)+(p+b)) → Fin ((p+a)+b) :=
  Fin.addCases (Fin.castAdd b)
    (Fin.addCases (fun j => Fin.castAdd b (Fin.castAdd a j)) (Fin.natAdd (p+a)))

theorem repeatBaseCoordinates_append (z : Fin p → M) (x : Fin a → M) (y : Fin b → M) :
    Fin.append (Fin.append z x) y ∘ repeatBaseCoordinates p a b =
      Fin.append (Fin.append z x) (Fin.append z y) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [repeatBaseCoordinates,Function.comp_apply,Fin.addCases_left,Fin.append_left]
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      simp only [repeatBaseCoordinates,Function.comp_apply,Fin.addCases_right,Fin.addCases_left,
        Fin.append_left,Fin.append_right]

def gammaSortedTotalEquiv (C : GammaSortedBijectionChart B sp sx sy)
    (hE : DefinableOverBase B (Fin.append sp sy) E) (hC : ∀ z ∈ A, C.valid D E z) :
    rawRowTotal A D ≃ rawRowTotal A E :=
  (rawRowTotalEquiv A D).trans ((Equiv.sigmaCongrRight (fun z : A =>
    (hC z.val z.property).equiv (fun y hy j => by
      simpa only [Fin.append_right] using hE.proper _ hy (Fin.natAdd p j)))).trans
        (rawRowTotalEquiv A E).symm)

theorem gammaSortedTotalEquiv_pack (C : GammaSortedBijectionChart B sp sx sy)
    (hE : DefinableOverBase B (Fin.append sp sy) E) (hC : ∀ z ∈ A, C.valid D E z)
    (z : A) (x : {x : Fin a → M | Fin.append z.val x ∈ D}) :
    gammaSortedTotalEquiv C hE hC ((rawRowTotalEquiv A D).symm ⟨z,x⟩) =
      (rawRowTotalEquiv A E).symm ⟨z,(hC z.val z.property).equiv
        (fun y hy j => by simpa only [Fin.append_right] using hE.proper _ hy (Fin.natAdd p j)) x⟩ := by
  change (rawRowTotalEquiv A E).symm
    ((Equiv.sigmaCongrRight _) ((rawRowTotalEquiv A D) ((rawRowTotalEquiv A D).symm ⟨z,x⟩))) = _
  rw [Equiv.apply_symm_apply]
  rfl

def gammaSortedTotalIso (C : GammaSortedBijectionChart B sp sx sy)
    (hA : DefinableOverBase B sp A) (hE : DefinableOverBase B (Fin.append sp sy) E)
    (hC : ∀ z ∈ A, C.valid D E z) :
    GammaSortedIso B (Fin.append sp sx) (Fin.append sp sy) (rawRowTotal A D) (rawRowTotal A E) := by
  let st := Fin.append (Fin.append sp sx) sy
  let idx : Fin p → Fin ((p+a)+b) := fun j => Fin.castAdd b (Fin.castAdd a j)
  let V := {r : Fin ((p+a)+b) → M | (r ∘ idx) ∈ A ∧ r ∈ sortedUniverse st}
  have hV : DefinableOverBase B st V := hA.preimage_real st idx
  have hI := (C.definable.inter hV).image_real (repeatBaseCoordinates p a b)
  have hsort : st ∘ repeatBaseCoordinates p a b = Fin.append (Fin.append sp sx) (Fin.append sp sy) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [st,repeatBaseCoordinates,Function.comp_apply,Fin.addCases_left,Fin.append_left]
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
        simp only [st,repeatBaseCoordinates,Function.comp_apply,Fin.addCases_right,Fin.addCases_left,
          Fin.append_left,Fin.append_right]
  rw [hsort] at hI
  refine ⟨gammaSortedTotalEquiv C hE hC,?_⟩
  convert hI using 1
  ext w
  constructor
  · rintro ⟨u,rfl⟩
    let q := rawRowTotalEquiv A D u
    let z := q.1
    let x := q.2
    let y := (hC z.val z.property).map x
    let r := Fin.append (Fin.append z.val x.val) y.val
    have hr : r ∈ C.carrier := (hC z.val z.property).map_graph x
    refine ⟨r,⟨hr,?_,C.definable.proper _ hr⟩,?_⟩
    · have he : r ∘ idx = z.val := by
        funext j
        simp only [r,idx,Function.comp_apply,Fin.append_left]
      exact he.symm ▸ z.property
    · change Fin.append (Fin.append z.val x.val) y.val ∘ repeatBaseCoordinates p a b = _
      rw [repeatBaseCoordinates_append]
      have hu : ((rawRowTotalEquiv A D).symm ⟨z,x⟩).val = u.val :=
        congrArg Subtype.val ((rawRowTotalEquiv A D).symm_apply_apply u)
      have hv := congrArg Subtype.val (gammaSortedTotalEquiv_pack C hE hC z x)
      change Fin.append (Fin.append z.val x.val) (Fin.append z.val y.val) = _
      exact congrArg₂ Fin.append hu ((congrArg (fun t => (gammaSortedTotalEquiv C hE hC t).val)
        ((rawRowTotalEquiv A D).symm_apply_apply u)).symm.trans hv).symm
  · rintro ⟨r,⟨hr,hz,_⟩,hw⟩
    let z : A := ⟨r ∘ idx,hz⟩
    let x : Fin a → M := fun j => r (Fin.castAdd b (Fin.natAdd p j))
    let y : Fin b → M := r ∘ Fin.natAdd (p+a)
    have hrpack : Fin.append (Fin.append z.val x) y = r := by
      change Fin.append (Fin.append (fun j => r (Fin.castAdd b (Fin.castAdd a j)))
        (fun j => r (Fin.castAdd b (Fin.natAdd p j)))) (fun j => r (Fin.natAdd (p+a) j)) = r
      have hl := Fin.append_castAdd_natAdd (f := fun j : Fin (p+a) => r (Fin.castAdd b j))
      exact (congrArg (fun v => Fin.append v (fun j => r (Fin.natAdd (p+a) j))) hl).trans
        (Fin.append_castAdd_natAdd (f := r))
    have hxy : Fin.append (Fin.append z.val x) y ∈ C.carrier := hrpack.symm ▸ hr
    have hx := (hC z.val z.property).1.2.2.1 x y hxy
    let u := (rawRowTotalEquiv A D).symm ⟨z,⟨x,hx⟩⟩
    have hy : ((hC z.val z.property).map ⟨x,hx⟩).val = y :=
      (hC z.val z.property).1.2.1 x hx |>.unique ((hC z.val z.property).map_graph ⟨x,hx⟩) hxy
    refine ⟨u,?_⟩
    have hv := congrArg Subtype.val (gammaSortedTotalEquiv_pack C hE hC z ⟨x,hx⟩)
    change (gammaSortedTotalEquiv C hE hC u).val = Fin.append z.val ((hC z.val z.property).map ⟨x,hx⟩).val at hv
    rw [hy] at hv
    change r ∘ repeatBaseCoordinates p a b = w at hw
    rw [← hrpack,repeatBaseCoordinates_append] at hw
    exact (congrArg (Fin.append u.val) hv).trans hw

end IntegrationInACVF.Section6
