module

public import Integration7.GammaIndexedOrdinaryCoordinateIsomorphisms
public import Integration7.GammaUnitVolumeIsoRealization
public import IntegrationSection6.FiniteGammaIsomorphisms

@[expose] public section

/-! Indexed ordinary row isomorphisms give genuine unit-density volume
isomorphisms. All index coordinates and original-Gamma graphs are kept. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

def indexedOrdinaryGammaIso
    (BP : GammaFiniteGraphPresentation B p d T R)
    (F : GammaFiniteRVSchema B p a 0 (fun _ => .rv))
    (G : GammaFiniteRVSchema B p b 0 (fun _ => .rv))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (e : GammaIso B
      {q : Point (M := M) 0 (p+a) | q.2 ∈ indexedDomain T (fun t => F.rowDomain (rvValues t))}
      {q : Point (M := M) 0 (p+b) | q.2 ∈ indexedDomain T (fun t => G.rowDomain (rvValues t))})
    (hPrefix : ∀ q, (e.equiv q).val.2 ∘ Fin.castAdd b = q.val.2 ∘ Fin.castAdd a) :
    GammaRVIso P.toGamma.toGammaRVObject Q.toGamma.toGammaRVObject :=
  FiniteRV.gammaIsoOfFiniteEquiv P.toGamma Q.toGamma (indexedOrdinaryLabelEquiv BP F G P Q e)
    (indexed_ordinary_label_equiv_graph BP F G P Q e) (fun u =>
      congrArg (fun t : Fin (d+0) → RV (M := M) => rawWeight (rvValues t))
        (indexed_ordinary_label_equiv_volume BP F G P Q e hPrefix u).symm)

theorem indexed_ordinary_gamma_iso_volume
    (BP : GammaFiniteGraphPresentation B p d T R)
    (F : GammaFiniteRVSchema B p a 0 (fun _ => .rv))
    (G : GammaFiniteRVSchema B p b 0 (fun _ => .rv))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (e : GammaIso B
      {q : Point (M := M) 0 (p+a) | q.2 ∈ indexedDomain T (fun t => F.rowDomain (rvValues t))}
      {q : Point (M := M) 0 (p+b) | q.2 ∈ indexedDomain T (fun t => G.rowDomain (rvValues t))})
    (hPrefix : ∀ q, (e.equiv q).val.2 ∘ Fin.castAdd b = q.val.2 ∘ Fin.castAdd a)
    (u : P.domain) :
    gammaVolumeValue Q.toGamma.toGammaRVObject ((indexedOrdinaryGammaIso BP F G P Q e hPrefix).equiv u) =
      gammaVolumeValue P.toGamma.toGammaRVObject u :=
  indexed_ordinary_label_equiv_volume BP F G P Q e hPrefix u

theorem gamma_indexed_ordinary_unit_volume_comparison {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    {T : Set (Fin p → RV (M := M))}
    {R : (Fin p → RV (M := M)) → (Fin 1 → RV (M := M)) → Prop}
    (BP : GammaFiniteGraphPresentation B p 1 T R)
    (F : GammaFiniteRVSchema B p a 0 (fun _ => .rv))
    (G : GammaFiniteRVSchema B p b 0 (fun _ => .rv))
    (hWitness : ∀ t ∈ T, ∃ H : GammaRelationFormula B p a b (fun _ => .rv),
      (gammaFiniteRowChartSchema F G H).valid (rvValues t))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (hPC : P.codes ⊆ (C.base : Set M)) (hQC : Q.codes ⊆ (C.base : Set M)) :
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
    ∃ f : RVVolumeIso ((gammaUnitVolumeObject hc C P.toGamma hPC).extend hCD)
      ((gammaUnitVolumeObject hc C Q.toGamma hQC).extend hCD), f.GammaDefinable B := by
  obtain ⟨e,hPrefix⟩ := gamma_indexed_ordinary_row_bijection hκ hs hreal hgamma BP F G hWitness
  exact gamma_unit_volume_iso_realization hc C P.toGamma Q.toGamma hPC hQC
    (indexedOrdinaryGammaIso BP F G P Q e hPrefix)
    (indexed_ordinary_gamma_iso_volume BP F G P Q e hPrefix)

end IntegrationInACVF.Section7
