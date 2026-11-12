import IntegrationSection6.GammaPreparedWitnessCover
import IntegrationSection6.GammaCrossParameterFiniteRows
import IntegrationSection6.GammaIndexedFiniteWitnessGluing

/-! A prepared finite witness cover glues to an actual common blowup over
any finite-volume RV presentation of the prepared key set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p l a b d k : ℕ}
variable {A : DefSet (M := M) S p 0} {C : DefSet (M := M) S p l}
open FiniteRV

theorem gamma_prepared_witness_gluing {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ)
    (F : GammaFiniteRVSchema B p a k (fun _ => .vf)) (G : GammaFiniteRVSchema B p b k (fun _ => .vf))
    (J : Finset (GammaFiniteCommonSchema F G))
    (T : SpecialBijection A C) (hT : GammaChainDefinable B T.chain)
    (hF : ∀ x : A, F.finiteRow (rawVFParameter x.val))
    (hG : ∀ x : A, G.finiteRow (rawVFParameter x.val))
    (hFA : ∀ x : C, (GammaParameterRecode.prepared T hT).ObjectAgreement F
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val))
    (hGA : ∀ x : C, (GammaParameterRecode.prepared T hT).ObjectAgreement G
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val))
    (hCover : ∀ x : C, ∃ W ∈ J, ((GammaParameterRecode.prepared T hT).common W).valid (rawPreparedKey x.val))
    {K : Set (Fin (p+l) → RV (M := M))}
    {R : (Fin (p+l) → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
    (BP : GammaFiniteGraphPresentation B (p+l) d K R)
    (hK : ∀ t ∈ K, ∃ x : C, (flatKey x.val).2 = t)
    (P : ((GammaParameterRecode.prepared T hT).object F).IndexedPresentation BP)
    (Q : ((GammaParameterRecode.prepared T hT).object G).IndexedPresentation BP) :
    GammaIspAt hκ hs h00 hreal (gammaUniversalObject P.toGamma) (gammaUniversalObject Q.toGamma) := by
  let D := GammaParameterRecode.prepared T hT
  let J' := J.image (fun W => D.common W)
  have hDF : ∀ t ∈ K, (D.object F).finiteRow (fun j => (t j).val) := by
    intro t ht
    obtain ⟨x,rfl⟩ := hK t ht
    exact (hFA x).finiteRows.mp (hF (T.inverseMap x))
  have hDG : ∀ t ∈ K, (D.object G).finiteRow (fun j => (t j).val) := by
    intro t ht
    obtain ⟨x,rfl⟩ := hK t ht
    exact (hGA x).finiteRows.mp (hG (T.inverseMap x))
  apply gamma_common_finite_indexed_glue hκ hs h00 hreal (D.object F) (D.object G) J' BP hDF hDG ?_ P Q
  intro t ht
  obtain ⟨x,rfl⟩ := hK t ht
  obtain ⟨W,hW,hvalid⟩ := hCover x
  exact ⟨D.common W,Finset.mem_image.mpr ⟨W,hW,rfl⟩,hvalid⟩

end IntegrationInACVF.Section6
