import tactic data.set

universe u

namespace prop
inductive Formula : Type u
  | falso : Formula
  | imply : Formula → Formula → Formula
  -- | conj : Formula → Formula → Formula

notation (name := Formula.falso) `⊥'` : 85 := Formula.falso
infixr (name := Formula.imply) `→'`: 55 := Formula.imply
notation (name := Formula.neg) `¬'` φ: 60 := φ →' ⊥' 
notation (name := Formula.disj) φ `∨'` ψ:50 := (¬'φ →' ψ)
notation (name := Formula.conj) φ `∧'` ψ:50 := ¬'(¬'φ ∨' ¬'ψ)
notation (name := Formula.equiv) φ `↔'` ψ:45 := (φ →' ψ) ∧' (ψ →' φ)
end prop