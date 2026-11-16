module

public import Integration7.NativeUnaryProductPreparations
public import Integration7.GammaNativeUnaryProductMaps
public import Integration7.NativeUnaryProductHeadGeometry
public import IntegrationSection6.StandardProgramPresentations

@[expose] public section

/-! Two actual unary special chains give a genuine ordered standard
contraction of their rectangle, carrying the entire first contraction
as RV parameters through the second preparation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {m r b : ℕ}
variable {A : DefSet (M := M) S 1 m} {D : DefSet (M := M) S 1 r}
variable {B : DefSet (M := M) S 1 0} {E : DefSet (M := M) S 1 b}

theorem gamma_native_rectangle_tail_preparation_exists
    (T : SpecialBijection A D) (hT : GammaChainDefinable P T.chain)
    (W : SpecialBijection B E) (hW : GammaChainDefinable P W.chain)
    (hE : IsRVPullback (carrier E)) :
    Nonempty (RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain D B)) (headImage D) P) := by
  apply gamma_rv_parameter_special_preparation_exists W hW hE _
    (gamma_headImage _ (gamma_native_unary_product D B (hT.target P T.chain) (hW.source P W.chain))) _
    (native_unary_product_head_carrier D B)

def nativeUnaryRectangleProgram (T : SpecialBijection A D) (hD : IsRVPullback (carrier D))
    {W : SpecialBijection B E}
    (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain D B)) (headImage D) P) :
    OrderedContractionProgram S (nativeUnaryProductDomain A B) L.head.contractedSet :=
  .step (nativeUnaryProductHeadPreparation T B hD) L.program

theorem gamma_native_unary_rectangle_program (T : SpecialBijection A D)
    (hT : GammaChainDefinable P T.chain) (hD : IsRVPullback (carrier D))
    {W : SpecialBijection B E} (hW : GammaChainDefinable P W.chain)
    (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain D B)) (headImage D) P) :
    GammaProgramDefinable P (nativeUnaryRectangleProgram T hD L) :=
  ⟨gamma_native_unary_product_map T.toMap B (hT.source P T.chain) (hW.source P W.chain)
      (GammaChainDefinable.graph (gammaLogicInput P) T.chain hT),
    gamma_native_unary_product D B (hT.target P T.chain) (hW.source P W.chain),L.program_gamma⟩

def nativeUnaryRectangleContraction (T : SpecialBijection A D) (hD : IsRVPullback (carrier D))
    {W : SpecialBijection B E}
    (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain D B)) (headImage D) P) :
    StandardContraction (nativeUnaryProductDomain A B) (Equiv.refl _) :=
  standardFromProgram _ _ (nativeUnaryRectangleProgram T hD L) (vfPermutationImage_id_eq _).symm

theorem gamma_native_unary_rectangle_contraction (T : SpecialBijection A D)
    (hT : GammaChainDefinable P T.chain) (hD : IsRVPullback (carrier D))
    {W : SpecialBijection B E} (hW : GammaChainDefinable P W.chain)
    (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain D B)) (headImage D) P) :
    GammaProgramDefinable P (nativeUnaryRectangleContraction T hD L).program :=
  gamma_standardFromProgram _ _ _ _ (gamma_native_unary_rectangle_program T hT hD hW L)

end IntegrationInACVF.Section7
