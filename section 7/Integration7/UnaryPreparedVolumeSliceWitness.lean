module

public import Integration7.GammaUnaryCommonFromLiftCharts
public import Integration7.GammaSelectedSliceContexts
public import Integration7.UnarySliceVFModels
public import Integration7.GammaLabelDensityCoordinateRows
public import IntegrationSection6.GammaRVParameterFieldBase

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A selected slice of an arbitrary unary standard contraction and the
corresponding prepared family slice have a finite common-volume-blowup
witness. Both moving VF charts and their actual density are verified. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a l k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

set_option maxHeartbeats 2400000 in
theorem gamma_unary_prepared_volume_slice_witness {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C C₁ : BaseContext M)
    (hCC₁ : (C.base : Set M) ⊆ (C₁.base : Set M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ) (FBase : VFFieldBase B.real)
    (hBC : B.real ⊆ (C.base : Set M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 0)
    (Z : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 l)
    (K : SpecialBijection A Z) (hK : GammaChainDefinable B K.chain)
    (hA : GammaSetDefinable B (carrier A)) (hZ : IsRVPullback (carrier Z))
    (F : GammaFiniteRVSchema B 1 a (k+1)) (G : GammaFiniteRVSchema B (1+l) a (k+1) (fun _ => .rv))
    (ρ : Fin (k+1) → Fin a)
    (hRows : ∀ q : Z, GammaSchemaRowAgreement F (rawVFParameter (K.inverseMap q).val) G (rawPreparedKey q.val))
    (BP : PreparedIndexPresentation B Z)
    (hG : ∀ s ∈ preparedKeyDomain Z, G.finiteRow (rvValues s))
    (hLabels : ∀ s ∈ preparedKeyDomain Z, ∀ r y, G.rowVolume (rvValues s) r y ↔
      r ∈ G.rowDomain (rvValues s) ∧ r ∘ ρ = y)
    (J : G.IndexedPresentation BP)
    (U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a)
    (hU : GammaSetDefinable B (carrier U)) (hSource : carrier U = vfSchemaSource (carrier A) F)
    (hfin : ∀ (x : Fin 1 → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    {σ : Equiv.Perm (Fin 1)} (T : StandardContraction U σ) (hT : GammaProgramDefinable B T.program)
    (δ : Fin a) (ω : VolumeForm (rawSpecialSet hc U)) (hDensity : ∀ q, ω.value q = q.val.2 δ)
    (t : Fin (k+1) → RV (M := M))
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (rvValues t),B.gamma⟩ (1+T.arity) 1
      ((gammaVolumeSliceSchema (FiniteRV.gammaPrependSelectedContraction hκ hs hreal hBC hU ρ hfin T hT)).rowDomain (rvValues t))
      ((gammaVolumeSliceSchema (FiniteRV.gammaPrependSelectedContraction hκ hs hreal hBC hU ρ hfin T hT)).rowVolume (rvValues t)))
    (Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (rvValues t),B.gamma⟩ ((1+l)+a) 1
      ((gammaVolumeSliceSchema (gammaSwapVolumeBlocks J.toGamma)).rowDomain (rvValues t))
      ((gammaVolumeSliceSchema (gammaSwapVolumeBlocks J.toGamma)).rowVolume (rvValues t)))
    (hP : P.codes ⊆ (C₁.base : Set M)) (hQ : Q.codes ⊆ (C₁.base : Set M))
    (hPδ : ∀ u : P.domain, (u.val (FiniteRV.contractionOldLabelIndex T δ)).val ≠ iRVZero)
    (hQδ : ∀ u : Q.domain, (u.val (Fin.natAdd (1+l) δ)).val ≠ iRVZero)
    (LF : GammaRVVolumeSchema B (k+1) (1+T.arity) 0 (fun _ => .rv))
    (RF : GammaRVVolumeSchema B (k+1) ((1+l)+a) 0 (fun _ => .rv))
    (hLF : LF.valid (rvValues t)) (hRF : RF.valid (rvValues t))
    (PL : RVVolumeSchemaRow
      (gammaCoordinateDensityObject (e := 0) (k := 0) hc C₁ P.toGamma hP
        (FiniteRV.contractionOldLabelIndex T δ) hPδ) LF (rvValues t))
    (PR : RVVolumeSchemaRow
      (gammaCoordinateDensityObject (e := 0) (k := 0) hc C₁ Q.toGamma hQ
        (Fin.natAdd (1+l) δ) hQδ) RF (rvValues t)) :
    ∃ H : GammaVolumeCommonSchema LF RF, H.valid (rvValues t) := by
  let eK : GammaIso B (carrier A) (carrier Z) :=
    ⟨K.equiv,GammaChainDefinable.graph (gammaLogicInput B) K.chain hK⟩
  obtain ⟨D,hC₁D,hBD,L,hL⟩ := gamma_selected_slice_context C₁ (hBC.trans hCC₁)
    (extendBase U hCC₁) hU ρ t
  let hCD := hCC₁.trans hC₁D
  have hLU : carrier L ⊆ carrier U := fun q hq => ((Set.ext_iff.mp hL q).mp hq).1
  have hBase : ∀ q : L, (q.val.1,Fin.elim0) ∈ carrier A := by
    intro q
    exact ((Set.ext_iff.mp hSource q.val).mp (hLU q.property)).1
  have hLfin := selected_slice_presentation_finite U L ρ t hL hfin
  let e₁ := FiniteRV.gammaSelectedContractionSliceLiftIso hκ hs hreal hBC hU ρ hfin T hT t P
  let eU := e₁.congr hL.symm rfl
  have hSrc : carrier L = vfSchemaSource (carrier A) F ∩ {q | q.2 ∘ ρ = t} :=
    hL.trans (congrArg (fun E : Set (Point (M := M) 1 a) => E ∩ {q | q.2 ∘ ρ = t}) hSource)
  let e₂ := gammaPreparedSelectedSliceLiftIso Z eK hA hZ F G ρ hRows BP hG hLabels J t Q
  let eV := e₂.congr hSrc.symm rfl
  let gU := unarySliceContractionVFModel T hCD L hLU
  let gV := unarySlicePreparedVFModel K hCD L hBase
  have hvU (q : L) : (eU.equiv q).val =
      (T.normalizedNaturalLiftMap ⟨q.val,hLU q.property⟩).val := by
    change ((e₁.congr hL.symm rfl).equiv q).val = _
    rw [gammaIso_congr_value]
    exact gammaSelectedContractionSliceLiftIso_value hκ hs hreal hBC hU ρ hfin T hT t P _
  have hvV (q : L) : (eV.equiv q).val =
      ((gammaPreparedFamilyIso eK hA F).equiv
        ⟨q.val,(Set.ext_iff.mp hSource q.val).mp (hLU q.property)⟩).val := by
    change ((e₂.congr hSrc.symm rfl).equiv q).val = _
    rw [gammaIso_congr_value]
    exact gammaPreparedSelectedSliceLiftIso_value Z eK hA hZ F G ρ hRows BP hG hLabels J t Q _
  have hVFU : ∀ q : L, (eU.equiv q).val.1 = (gU q).val.1 := by
    intro q
    exact (congrArg Prod.fst (hvU q)).trans
      (congrArg Prod.fst (unarySliceContractionVFModel_value T hCD L hLU q)).symm
  have hVFV : ∀ q : L, (eV.equiv q).val.1 = (gV q).val.1 := by
    intro q
    rw [hvV,gammaPreparedFamilyIso_value]
    exact (congrArg Prod.fst (unarySlicePreparedVFModel_value K hCD L hBase q)).symm
  have hLabelU : ∀ q : L, (eU.equiv q).val.2 (FiniteRV.contractionOldLabelIndex T δ) = q.val.2 δ := by
    intro q
    exact (congrArg (fun x => x.2 (FiniteRV.contractionOldLabelIndex T δ)) (hvU q)).trans
      ((congrArg (fun r => r (FiniteRV.contractionOldLabelIndex T δ))
        (T.normalizedNaturalLiftMap_square ⟨q.val,hLU q.property⟩)).trans
          (FiniteRV.contraction_oldLabels T ⟨q.val,hLU q.property⟩ δ))
  have hLabelV : ∀ q : L, (eV.equiv q).val.2 (Fin.natAdd (1+l) δ) = q.val.2 δ := by
    intro q
    exact (congrArg (fun x => x.2 (Fin.natAdd (1+l) δ)) (hvV q)).trans
      (congrFun (gammaPreparedFamilyIso_oldLabels eK hA F
        ⟨q.val,(Set.ext_iff.mp hSource q.val).mp (hLU q.property)⟩) δ)
  let ωL : VolumeForm (rawSpecialSet hc L) := (ω.extend hCD).restrict hLU
  have hDensityL : ∀ q, ωL.value q = q.val.2 δ := fun q => hDensity ⟨q.val,hLU q.property⟩
  exact gamma_unary_common_from_lift_charts (sp := fun _ => .rv) hc D hκ hs hreal hgamma (rvValues t)
    (fun j => (t j).property) hBD γ hγ hγ1
    (VFFieldBase.withRVParameters FBase (rvValues t) (fun j => (t j).property))
    P.toGamma Q.toGamma (hP.trans hC₁D) (hQ.trans hC₁D) eU eV gU gV
    (unarySliceContractionVFModel_jacobian_one hc C D T hCD L hLU)
    (unarySlicePreparedVFModel_jacobian_one hc C D K hCD L hBase hLfin) hVFU hVFV
    δ (FiniteRV.contractionOldLabelIndex T δ) (Fin.natAdd (1+l) δ) hPδ hQδ hLabelU hLabelV
    ωL hDensityL LF RF hLF hRF (PL.extend hC₁D) (PR.extend hC₁D)

end IntegrationInACVF.Section7
