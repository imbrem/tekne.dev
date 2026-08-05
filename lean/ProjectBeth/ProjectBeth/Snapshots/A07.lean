import ProjectBeth.Defs.Carrier
import ProjectBeth.Snapshots.A06

universe u v

namespace ProjectBeth.Snapshots.A07

abbrev Carrier (BaseTy : Type u) (El : BaseTy → Type v) :=
  TypeCarrier BaseTy El

def base {BaseTy : Type u} (El : BaseTy → Type v) (A : BaseTy) :
    El A ↪ Carrier BaseTy El :=
  TypeCarrier.ofBase El A

abbrev BethOmega := PowerTower Nat
abbrev KindOmega := PowerTower BethOmega

def nat : Nat ↪ BethOmega := PowerTower.base
def kindBase : BethOmega ↪ KindOmega := PowerTower.base

def levelCode {Base : Type u} (n : Nat) : _root_.Code (PowerLevel Base n) (PowerTower Base) :=
  _root_.Code.emb (PowerTower.ofLevel n)

theorem levelCode_decode {Base : Type u} (n : Nat) (x : PowerLevel Base n) :
    ProjectBeth.Code.decode (levelCode n)
      ⟨levelCode n |>.code x, by simp⟩ = x :=
  ProjectBeth.Code.decode_code (levelCode n) x

end ProjectBeth.Snapshots.A07
