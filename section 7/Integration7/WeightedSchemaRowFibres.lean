import Integration7.VolumeSchemaValiditySemantics

/-! Exact weighted correspondence fibres of an actual essential chart.
Functionality of the source and target volume schemata determines every
coordinate-and-density label from its underlying point. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}
variable {U V : PositiveRVVolumeObject (M := M) S k}
variable {F : GammaRVVolumeSchema B p U.underlying.obj.arity k sp}
variable {G : GammaRVVolumeSchema B p V.underlying.obj.arity k sp} {z : Fin p → M}

theorem RVVolumeSchemaRow.weighted_unique (P : RVVolumeSchemaRow U F z)
    (hF : F.valid z) (u : U.essential.obj.domain) (w : Fin ((k+1)+1) → M)
    (hw : Fin.append (Fin.append z (rvValues u.val)) w ∈ weightedVolumeGraph F) :
    w = rvValues (volumeGammaWeightTuple U u) := by
  have hx := hF.1.2.2.1 _ _ (P.volume_at u)
  exact ((weightedVolumeSchema_valid F z hF).2.1 _ hx).unique hw (P.weighted_at u)

theorem RVVolumeSchemaRow.weighted_correspondence_iff (P : RVVolumeSchemaRow U F z)
    (Q : RVVolumeSchemaRow V G z) (hF : F.valid z) (hG : G.valid z)
    (e : U.essential ≅ V.essential)
    (H : Set (Fin ((p+U.underlying.obj.arity)+V.underlying.obj.arity) → M))
    (hH : ∀ x y, Fin.append (Fin.append z x) y ∈ H ↔
      ∃ u : U.essential.obj.domain, rvValues u.val = x ∧ rvValues (finiteIsoMap e u).val = y)
    (r : Fin (((k+1)+1)+((k+1)+1)) → M) :
    Fin.append z r ∈ schemaVolumeCorrespondence (weightedVolumeSchema F) (weightedVolumeSchema G) H ↔
      ∃ u : U.essential.obj.domain, Fin.append (rvValues (volumeGammaWeightTuple U u))
        (rvValues (volumeGammaWeightTuple V (finiteIsoMap e u))) = r := by
  constructor
  · intro hr
    let l := r ∘ Fin.castAdd ((k+1)+1)
    let s := r ∘ Fin.natAdd ((k+1)+1)
    have he : Fin.append l s = r := Fin.append_castAdd_natAdd
    have hrRV (i) : iRV (r i) := by
      simpa only [Fin.append_right,sortEval,iRV] using hr.2 (Fin.natAdd p i)
    have hc : Fin.append z (Fin.append l s) ∈
        schemaVolumeCorrespondence (weightedVolumeSchema F) (weightedVolumeSchema G) H := he.symm ▸ hr
    obtain ⟨x,y,hx,hxy,hy⟩ := (schemaVolumeCorrespondence_append (weightedVolumeSchema F)
      (weightedVolumeSchema G) H z l s hF.1.1 (fun i => hrRV _) (fun i => hrRV _)).mp hc
    obtain ⟨u,rfl,rfl⟩ := (hH x y).mp hxy
    exact ⟨u,(congrArg₂ Fin.append (P.weighted_unique hF u l hx)
      (Q.weighted_unique hG (finiteIsoMap e u) s hy)).symm.trans he⟩
  · rintro ⟨u,hu⟩
    rw [← hu]
    exact (schemaVolumeCorrespondence_append (weightedVolumeSchema F) (weightedVolumeSchema G) H z _ _
      hF.1.1 (fun i => (volumeGammaWeightTuple U u i).property)
      (fun i => (volumeGammaWeightTuple V (finiteIsoMap e u) i).property)).mpr
      ⟨rvValues u.val,rvValues (finiteIsoMap e u).val,P.weighted_at u,
        (hH _ _).mpr ⟨u,rfl,rfl⟩,Q.weighted_at (finiteIsoMap e u)⟩

theorem RVVolumeSchemaRow.gammaRowValid_of_iso (P : RVVolumeSchemaRow U F z)
    (Q : RVVolumeSchemaRow V G z) (hF : F.valid z) (hG : G.valid z)
    (e : RVVolumeIso U V)
    (H : Set (Fin ((p+U.underlying.obj.arity)+V.underlying.obj.arity) → M))
    (hH : ∀ x y, Fin.append (Fin.append z x) y ∈ H ↔
      ∃ u : U.essential.obj.domain, rvValues u.val = x ∧ rvValues (finiteIsoMap e.iso u).val = y) :
    volumeChartGammaRowValid F G H z := by
  refine ⟨hF.1.1,?_⟩
  intro r hr
  obtain ⟨u,rfl⟩ := (P.weighted_correspondence_iff Q hF hG e.iso H hH r).mp hr
  exact (volumeGammaWeightTuple_balance_iff U V u (finiteIsoMap e.iso u)).mpr (e.essentialGammaWeight u)

end IntegrationInACVF.Section7
