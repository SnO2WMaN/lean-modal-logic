universe u

namespace basicmodal
variables (A : Type u)
 
inductive Formula : Type u
  | var : ℕ → Formula
  | falso : Formula
  | imply : Formula → Formula → Formula
  | box : Formula → Formula

notation (name := Formula.falso) `⊥'` : 85 := Formula.falso
infixr (name := Formula.imply) ` →' `: 55 := Formula.imply
prefix (name := Formula.box) `□` :60 := Formula.box

def Formula.neg (φ) : Formula := φ →' ⊥' 
prefix `¬'`: 60 := Formula.neg

def Formula.disj (φ ψ) : Formula := ¬'φ →' ψ
infixl ` ∨' `:50 := Formula.disj

def Formula.conj (φ ψ) : Formula := ¬'(φ →' ¬'ψ)
infixl ` ∧' `:50 := Formula.conj

def Formula.equiv (φ ψ) : Formula := (φ →' ψ) ∧' (ψ →' φ)
infix ` ↔' `:50 := Formula.equiv

def Formula.dia (φ : Formula) : Formula := ¬'□¬'φ
prefix `◇`:60 := Formula.dia

end basicmodal