import PricingABD.TTExchange
namespace PricingC.MixedUT
open Ramsey61 Ramsey61.CEncodingCore
abbrev mPalette:=PricingABD.TTExchange.mPalette
abbrev xPalette:=PricingABD.TTExchange.xPalette
abbrev qPalette:=PricingABD.TTExchange.qPalette
/-- Actual same-host mixedU/T frame; only the left template differs fromTT. -/
structure Frame (c : Host) (k : Nat) (qtype : Bool) where
  root : Fin 61
  free : Fin k ↪ Fin 61
  left : Fin 15 ↪ Fin 61
  right : Fin 15 ↪ Fin 61
  marked : Fin 16 ↪ Fin 61
  free_mem : ∀ i, free i ∈ colorNeighborhood c (palette 0) root
  left_mem : ∀ i, left i ∈ colorNeighborhood c (palette 1) root
  right_mem : ∀ i, right i ∈ colorNeighborhood c (palette 2) root
  marked_mem : ∀ i, marked i ∈ colorNeighborhood c (palette 3) root
  left_edges : ∀ a b, a ≠ b → c (left a) (left b) = mPalette (R4333.k15Untwisted a b)
  right_edges : ∀ a b, a ≠ b → c (right a) (right b) = xPalette (R4333.k15Twisted a b)
  marked_edges : ∀ a b, a ≠ b → c (marked a) (marked b) = qPalette (R4333.k16Template qtype a b)


end PricingC.MixedUT
