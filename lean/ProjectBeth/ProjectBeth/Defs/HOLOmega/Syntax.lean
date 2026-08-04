universe u

namespace ProjectBeth.HOLOmega

inductive Kind : Type
  | star : Kind
  | arr : Kind → Kind → Kind

mutual
  inductive Ty (Base : Type u) : Type u
    | base : Base → Ty Base
    | var : Nat → Ty Base
    | lam : Kind → Ty Base → Ty Base
    | app : Ty Base → Ty Base → Ty Base
    | bool : Ty Base
    | arr : Ty Base → Ty Base → Ty Base
    | sub : Ty Base → Tm Base → Ty Base

  inductive Tm (Base : Type u) : Type u
    | var : Nat → Tm Base
    | app : Tm Base → Tm Base → Tm Base
    | lam : Ty Base → Tm Base → Tm Base
    | tyApp : Tm Base → Ty Base → Tm Base
    | tyLam : Kind → Tm Base → Tm Base
    | bool : Bool → Tm Base
    | eq : Ty Base → Tm Base → Tm Base → Tm Base
    | epsilon : Ty Base → Tm Base → Tm Base
    | abs : Ty Base → Tm Base → Tm Base → Tm Base
    | rep : Ty Base → Tm Base → Tm Base → Tm Base
end

mutual
  inductive Kinded {Base : Type u} : List Kind → Ty Base → Kind → Prop
    | base : Kinded Δ (.base A) .star
    | var : Δ[n]? = some K → Kinded Δ (.var n) K
    | lam : Kinded (K :: Δ) t L → Kinded Δ (.lam K t) (.arr K L)
    | app : Kinded Δ f (.arr K L) → Kinded Δ x K → Kinded Δ (.app f x) L
    | bool : Kinded Δ .bool .star
    | arr : Kinded Δ A .star → Kinded Δ B .star → Kinded Δ (.arr A B) .star
    | sub : Kinded Δ A .star → HasType Δ [A] p .bool → Kinded Δ (.sub A p) .star

  inductive HasType {Base : Type u} :
      List Kind → List (Ty Base) → Tm Base → Ty Base → Prop
    | var : Γ[n]? = some A → HasType Δ Γ (.var n) A
    | app : HasType Δ Γ f (.arr A B) → HasType Δ Γ x A →
        HasType Δ Γ (.app f x) B
    | lam : Kinded Δ A .star → HasType Δ (A :: Γ) t B →
        HasType Δ Γ (.lam A t) (.arr A B)
    | tyApp : HasType Δ Γ f (.app F X) → Kinded Δ A K →
        HasType Δ Γ (.tyApp f A) (.app F A)
    | tyLam : HasType (K :: Δ) Γ t A →
        HasType Δ Γ (.tyLam K t) (.lam K A)
    | bool : HasType Δ Γ (.bool b) .bool
    | eq : Kinded Δ A .star → HasType Δ Γ x A → HasType Δ Γ y A →
        HasType Δ Γ (.eq A x y) .bool
    | epsilon : Kinded Δ A .star → HasType Δ Γ p (.arr A .bool) →
        HasType Δ Γ (.epsilon A p) A
    | abs : Kinded Δ A .star → HasType Δ [A] p .bool → HasType Δ Γ x A →
        HasType Δ Γ (.abs A p x) (.sub A p)
    | rep : Kinded Δ A .star → HasType Δ [A] p .bool →
        HasType Δ Γ x (.sub A p) → HasType Δ Γ (.rep A p x) A
end

end ProjectBeth.HOLOmega
