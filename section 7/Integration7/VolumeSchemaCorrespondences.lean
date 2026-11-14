import Integration7.GammaTupleRelationInverse

/-! The volume correspondence is derived by composing the inverse source
coordinate graph, the comparison chart and the target coordinate graph. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d : ℕ} {sp : Fin p → SortTag}

def schemaVolumePairRelation (F : GammaFiniteRVSchema B p a d sp)
    (G : GammaFiniteRVSchema B p b d sp) (H : Set (Fin ((p+a)+b) → M)) :
    Set (Fin ((p+d)+d) → M) :=
  familyRelationCompose (familyRelationCompose (familyRelationInverse F.volume) H) G.volume

theorem schemaVolumePairRelation_definable (F : GammaFiniteRVSchema B p a d sp)
    (G : GammaFiniteRVSchema B p b d sp) {H : Set (Fin ((p+a)+b) → M)}
    (hH : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) H) :
    DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin d => .rv)) (fun _ : Fin d => .rv))
      (schemaVolumePairRelation F G H) :=
  familyRelationCompose_definable sp
    (familyRelationCompose_definable sp (familyRelationInverse_definable sp F.volume_definable) hH)
    G.volume_definable

theorem schemaVolumePairRelation_append (F : GammaFiniteRVSchema B p a d sp)
    (G : GammaFiniteRVSchema B p b d sp) (H : Set (Fin ((p+a)+b) → M))
    (z : Fin p → M) (u v : Fin d → M) :
    Fin.append (Fin.append z u) v ∈ schemaVolumePairRelation F G H ↔
      ∃ (x : Fin a → M) (y : Fin b → M),
        Fin.append (Fin.append z x) u ∈ F.volume ∧ Fin.append (Fin.append z x) y ∈ H ∧
        Fin.append (Fin.append z y) v ∈ G.volume := by
  unfold schemaVolumePairRelation
  rw [familyRelationCompose_append]
  constructor
  · rintro ⟨y,hxy,hyv⟩
    obtain ⟨x,hux,hxy⟩ := (familyRelationCompose_append _ _ z u y).mp hxy
    exact ⟨x,y,(familyRelationInverse_append _ z x u).mp hux,hxy,hyv⟩
  · rintro ⟨x,y,hxu,hxy,hyv⟩
    exact ⟨y,(familyRelationCompose_append _ _ z u y).mpr
      ⟨x,(familyRelationInverse_append _ z x u).mpr hxu,hxy⟩,hyv⟩

def schemaVolumeCorrespondence (F : GammaFiniteRVSchema B p a d sp)
    (G : GammaFiniteRVSchema B p b d sp) (H : Set (Fin ((p+a)+b) → M)) :
    Set (Fin (p+(d+d)) → M) :=
  {w | w ∘ Fin.cast (Nat.add_assoc p d d) ∈ schemaVolumePairRelation F G H ∧
    w ∈ sortedUniverse (Fin.append sp (fun _ : Fin (d+d) => .rv))}

theorem schemaVolumeCorrespondence_definable (F : GammaFiniteRVSchema B p a d sp)
    (G : GammaFiniteRVSchema B p b d sp) {H : Set (Fin ((p+a)+b) → M)}
    (hH : DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) H) :
    DefinableOverBase B (Fin.append sp (fun _ : Fin (d+d) => .rv)) (schemaVolumeCorrespondence F G H) :=
  (schemaVolumePairRelation_definable F G hH).preimage_real _ (Fin.cast (Nat.add_assoc p d d))

theorem schemaVolumeCorrespondence_append (F : GammaFiniteRVSchema B p a d sp)
    (G : GammaFiniteRVSchema B p b d sp) (H : Set (Fin ((p+a)+b) → M))
    (z : Fin p → M) (u v : Fin d → M)
    (hz : ∀ i, sortEval (sp i) (z i)) (hu : ∀ i, iRV (u i)) (hv : ∀ i, iRV (v i)) :
    Fin.append z (Fin.append u v) ∈ schemaVolumeCorrespondence F G H ↔
      ∃ (x : Fin a → M) (y : Fin b → M),
        Fin.append (Fin.append z x) u ∈ F.volume ∧ Fin.append (Fin.append z x) y ∈ H ∧
        Fin.append (Fin.append z y) v ∈ G.volume := by
  change (_ ∧ _) ↔ _
  rw [← Fin.append_assoc,schemaVolumePairRelation_append]
  have hs : Fin.append z (Fin.append u v) ∈ sortedUniverse
      (Fin.append sp (fun _ : Fin (d+d) => .rv)) := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [Fin.append_left] using hz i
    · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_right,Fin.append_left,sortEval,iRV] using hu i
      · simpa only [Fin.append_right,sortEval,iRV] using hv i
  exact and_iff_left hs

end IntegrationInACVF.Section7
