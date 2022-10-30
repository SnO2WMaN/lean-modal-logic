universe u

namespace basicmodal
variables (A : Type u)
 
inductive formula : Type u
  | atom : A → formula
  | top : formula
  | neg : formula → formula
  | imply : formula → formula → formula

-- notation (name := form.bot) `⊥` :80 := form.bot
-- prefix (name := form.var) `p` :80 := form.var
-- infix (name := form.and) `∧` :79 := form.and
-- notation (name := form.impl) `→` :80 := form.impl 
-- notation (name := form.not) `¬` φ :90 := (φ → ⊥)  
-- notation (name := form.or) φ `∨` ψ :79 := (¬φ → ψ)
-- notation (name := form.iff) φ `↔` ψ :78 := ((φ → ψ) ∧ (ψ → φ))
-- notation (name := form.top) `⊤` :80 := ¬⊥
-- notation (name := form.box) `□` :80 := form.box
-- notation (name := form.dia) `◇` :80 := λ φ, ¬(□(¬φ))

end basicmodal