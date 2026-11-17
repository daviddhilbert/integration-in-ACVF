module

public import Integration7.HKIndexedWeightedRowBijections
public import Integration7.GammaIndexedOrdinaryUnitComparisons
public import Integration7.GammaCoordinateDensityEquivalences

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Indexed finite-row comparison preserves arbitrary retained nonzero
densities, giving actual volume isomorphisms over the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin 1 → RV (M := M)) → Prop}

theorem indexed_weighted_label_equiv_density
    (BP : GammaFiniteGraphPresentation B p 1 T R)
    (F : GammaFiniteRVSchema B p a 0 (fun _ => .rv))
    (G : GammaFiniteRVSchema B p b 0 (fun _ => .rv))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (δ : Fin a) (ε : Fin b)
    (e : GammaIso B
      {q : Point (M := M) 0 (p+a) | q.2 ∈ indexedDomain T (fun t => F.rowDomain (rvValues t))}
      {q : Point (M := M) 0 (p+b) | q.2 ∈ indexedDomain T (fun t => G.rowDomain (rvValues t))})
    (he : ∀ q, (e.equiv q).val.2 (Fin.natAdd p ε) = q.val.2 (Fin.natAdd p δ))
    (u : P.domain) :
    (indexedOrdinaryLabelEquiv BP F G P Q e u).val (Fin.natAdd p ε) = u.val (Fin.natAdd p δ) :=
  he ((pureRVLabelPointEquiv _) (P.domainEquiv u))

theorem indexed_weighted_volume_comparison {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
    (BP : GammaFiniteGraphPresentation B p 1 T R)
    (F : GammaFiniteRVSchema B p a 0 (fun _ => .rv))
    (G : GammaFiniteRVSchema B p b 0 (fun _ => .rv))
    (δ : Fin a) (ε : Fin b)
    (hrow : ∀ t ∈ T, ∃ H : GammaRelationFormula B p a b (fun _ => .rv),
      H.val ⊆ densityLabelConstraint (fun _ => .rv) δ ε ∧
        (gammaFiniteRowChartSchema F G H).valid (rvValues t))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (hPC : P.codes ⊆ (C.base : Set M)) (hQC : Q.codes ⊆ (C.base : Set M))
    (hδ : ∀ u : P.domain, (u.val (Fin.natAdd p δ)).val ≠ iRVZero)
    (hε : ∀ v : Q.domain, (v.val (Fin.natAdd p ε)).val ≠ iRVZero) :
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
    ∃ f : RVVolumeIso
      ((gammaCoordinateDensityObject (e := 0) (k := 0) hc C P.toGamma hPC (Fin.natAdd p δ) hδ).extend hCD)
      ((gammaCoordinateDensityObject (e := 0) (k := 0) hc C Q.toGamma hQC (Fin.natAdd p ε) hε).extend hCD),
      f.GammaDefinable B := by
  obtain ⟨e,hP,hD⟩ := indexed_weighted_row_bijection hκ hs hr hg BP F G δ ε hrow
  exact gamma_coordinate_density_equivalence_realize hc C P.toGamma Q.toGamma hPC hQC
    (Fin.natAdd p δ) (Fin.natAdd p ε) hδ hε
    (indexedOrdinaryGammaIso BP F G P Q e hP)
    (indexed_ordinary_gamma_iso_volume BP F G P Q e hP)
    (indexed_weighted_label_equiv_density BP F G P Q δ ε e hD)

end IntegrationInACVF.Section7.HK
