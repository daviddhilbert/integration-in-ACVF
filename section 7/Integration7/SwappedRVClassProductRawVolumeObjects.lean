module

public import Integration7.SwappedRVClassProductContractions
public import Integration7.ConstantTailCoordinateVolumeIsomorphisms
public import Integration7.GammaRVLabelIdentity
public import Integration7.GammaVolumeDensityRescaling
public import IntegrationSection6.GammaRawStandardContractions

@[expose] public section

/-! The exact raw RV object of a constructed opposite-order two-coordinate product
contraction is volume-isomorphic to its unary product object, at every
common constant density, with a complete original-Gamma graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {b d : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M))
variable (Z : DefSet (M := M) S 2 0) (B : DefSet (M := M) S 1 0)
variable (B' : DefSet (M := M) S 1 b) (T : SpecialBijection B B')
variable (hSat : HeadSaturated (carrier (vfPermutationImage Z (Equiv.swap 0 1)))) (r : RV (M := M)) (hr : r.val ∈ S)
variable (t : Fin d → RV (M := M)) (ht : ∀ i, (t i).val ∈ S)
variable (L : ConstantRVLabelSpecialPreparation T (headImage (fixedRVLabelDomain (vfPermutationImage Z (Equiv.swap 0 1)) t ht))
  (Fin.append (fun _ : Fin 1 => r) (Fin.append (Fin.elim0 : Fin 0 → RV (M := M)) t)) P)
variable (hLF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
  (@CanonicalStructure.normalize M sM) _ _ S _ _ (rvObjectVolume (pullbackObject L.target)))

def swappedRVClassProductRawFiniteRVObject : RVFiniteObject (M := M) S 2 :=
  ⟨canonicalRVObject hc (swappedRVClassProductStandardContraction Z B B' T hSat r t ht L).contractionObject,
    (finite_volume_iso (swappedRVClassProductRawRVIso Z B B' T hSat r t ht L hc hr hLF)).mpr
      (appendFixedRVCoordinate (canonicalFiniteRVObject hc ⟨pullbackObject L.target,hLF⟩) r hr).property⟩

def swappedRVClassProductRawVolumeObject : PositiveRVVolumeObject (M := M) S 1 :=
  ⟨swappedRVClassProductRawFiniteRVObject hc Z B B' T hSat r hr t ht L hLF,VolumeForm.one _⟩

def swappedRVClassProductRawVolumeIso : RVVolumeIso
    (swappedRVClassProductRawVolumeObject hc Z B B' T hSat r hr t ht L hLF)
    (appendFixedRVVolume (canonicalFiniteRVObject hc ⟨pullbackObject L.target,hLF⟩) r hr (VolumeForm.one _)) := by
  let e : swappedRVClassProductRawFiniteRVObject hc Z B B' T hSat r hr t ht L hLF ≅
      appendFixedRVCoordinate (canonicalFiniteRVObject hc ⟨pullbackObject L.target,hLF⟩) r hr :=
    rvFiniteIsoOfAmbient (swappedRVClassProductRawRVIso Z B B' T hSat r t ht L hc hr hLF)
  apply constantTailCoordinateVolumeIso e r
  · intro u
    exact (congrFun (swapped_rv_class_product_raw_projection_volume Z B B' T hSat r t ht L hc hr hLF u) 1).symm
  · exact swapped_rv_class_product_raw_projection_volume Z B B' T hSat r t ht L hc hr hLF
  · intro u
    rfl

theorem swapped_rv_class_product_raw_volume_iso_gamma (hPS : P.real ⊆ S) :
    (swappedRVClassProductRawVolumeIso hc Z B B' T hSat r hr t ht L hLF).GammaDefinable P := by
  let C := swappedRVClassProductStandardContraction Z B B' T hSat r t ht L
  let U := swappedRVClassProductRawVolumeObject hc Z B B' T hSat r hr t ht L hLF
  have hFinal : GammaSetDefinable P (carrier C.target) :=
    gamma_headImage L.target (GammaChainDefinable.target P L.special.chain L.gamma)
  have hCoord : GammaGraphDefinable P (fun (p : Point (M := M) 0 U.underlying.obj.arity)
      (q : Point (M := M) 0 2) => U.underlying.obj.volume.graph p.2 q.2) := by
    apply GammaGraphDefinable.congr (gammaRawContractionObject C hPS hFinal).volume_graph
    intro p q
    exact ⟨fun ⟨u,hu,hq⟩ => ⟨⟨u.val,u.property⟩,hu,hq⟩,
      fun ⟨u,hu,hq⟩ => ⟨⟨u.val,u.property⟩,hu,hq⟩⟩
  have hDomain : GammaSetDefinable P {p : Point (M := M) 0 U.underlying.obj.arity |
      p.2 ∈ U.underlying.obj.domain.carrier} := gamma_raw_contraction_domain C hFinal
  have hGraph : GammaGraphDefinable P (fun (p q : Point (M := M) 0 U.underlying.obj.arity) =>
      ∃ u : U.underlying.obj.domain, u.val = p.2 ∧
        (rvClassProductRawProjection hc (vfPermutationImage Z (Equiv.swap 0 1)) B B' T hSat r t ht L hLF u).val = q.2) := by
    apply GammaGraphDefinable.congr (gamma_rv_restricted_label_identity P _ hDomain)
    intro p q
    constructor
    · rintro ⟨hp,he⟩
      exact ⟨⟨p.2,hp⟩,rfl,he⟩
    · rintro ⟨u,hu,hq⟩
      have hp : p.2 ∈ U.underlying.obj.domain.carrier := hu ▸ u.property
      exact ⟨hp,hu.symm.trans hq⟩
  exact gamma_volume_iso_of_full_map _ (rvClassProductRawProjection hc (vfPermutationImage Z (Equiv.swap 0 1)) B B' T hSat r t ht L hLF)
    (gamma_essential_volume_domain U hCoord) hGraph (fun _ => rfl)

theorem swapped_rv_class_product_raw_volume_comparison (hPS : P.real ⊆ S)
    (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) :
    ∃ e : RVVolumeIso
      ((swappedRVClassProductRawVolumeObject hc Z B B' T hSat r hr t ht L hLF).rescale η hη hη0)
      ((appendFixedRVVolume (canonicalFiniteRVObject hc ⟨pullbackObject L.target,hLF⟩) r hr
        (VolumeForm.one _)).rescale η hη hη0), e.GammaDefinable P :=
  ⟨(swappedRVClassProductRawVolumeIso hc Z B B' T hSat r hr t ht L hLF).rescale η hη hη0,
    (swapped_rv_class_product_raw_volume_iso_gamma hc Z B B' T hSat r hr t ht L hLF hPS).rescale η hη hη0⟩

end IntegrationInACVF.Section7
