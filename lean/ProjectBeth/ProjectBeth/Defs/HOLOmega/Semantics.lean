import ProjectBeth.Defs.Carrier
import ProjectBeth.Defs.HOLOmega.Syntax
import ProjectBeth.Defs.STLC.Core

universe u v

namespace ProjectBeth.HOLOmega

def Kind.denote (Ω : Type v) : Kind → Type v
  | .star => Set Ω
  | .arr K L => Kind.denote Ω K → Kind.denote Ω L

def KindEnv (Ω : Type v) : List Kind → Type v
  | [] => PUnit
  | K :: Δ => Kind.denote Ω K × KindEnv Ω Δ

structure DirectModel (Base : Type u) (Ω : Type v) where
  ty : ∀ {Δ : List Kind} {A : Ty Base} {K : Kind},
    Kinded Δ A K → KindEnv Ω Δ → Kind.denote Ω K
  tm : ∀ {Δ : List Kind} {Γ : List (Ty Base)} {t : Tm Base} {A : Ty Base},
    HasType Δ Γ t A → KindEnv Ω Δ →
    STLC.Env (fun _ => Ω) Γ → Ω

structure ShapeModel (Base : Type u) (Ω : Type v) where
  ty : Ty Base → Type v
  tm : ∀ {Δ : List Kind} {Γ : List (Ty Base)} {t : Tm Base} {A : Ty Base},
    HasType Δ Γ t A → KindEnv Ω Δ →
    STLC.Env ty Γ → ty A

structure CodedModel (Base : Type u) (Ω : Type v) extends ShapeModel Base Ω where
  kindCode : ∀ K, _root_.Code (Kind.denote Ω K) KindOmega
  termCode : ∀ A, _root_.Code (toShapeModel.ty A) Ω

abbrev KindCarrier := KindOmega

end ProjectBeth.HOLOmega
