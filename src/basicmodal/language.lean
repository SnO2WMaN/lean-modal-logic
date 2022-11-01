universe u

namespace basicmodal
variables (A : Type u)
 
inductive Formula : Type u
  | falso : Formula
  | imply : Formula → Formula → Formula
  | box : Formula → Formula

notation (name := Formula.falso) `⊥'` : 85 := Formula.falso

infixr (name := Formula.imply) `→'`: 55 := Formula.imply
notation (name := Formula.neg) `¬'` φ: 60 := φ →' ⊥' 
notation (name := Formula.disj) φ `∨'` ψ:50 := (¬'φ →' ψ)
notation (name := Formula.conj) φ `∧'` ψ:50 := ¬'(¬'φ ∨' ¬'ψ)
notation (name := Formula.equiv) φ `↔'` ψ:45 := (φ →' ψ) ∧' (ψ →' φ)

prefix (name := Formula.box) `□` :60 := Formula.box
notation (name := Formula.dia) `◇` φ:60 := ¬(□(¬φ))

end basicmodal