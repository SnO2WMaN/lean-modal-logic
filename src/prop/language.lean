universe u

namespace prop
variables (A : Type u)
 
inductive formula : Type u
  | atom : A → formula
  | top : formula
  | neg : formula → formula
  | imply : formula → formula → formula

notation (name := formula.top) `⊤` :80 := formula.top
prefix (name := formula.neg) `¬` :80 := formula.neg
infix (name := formula.imply) `⊃` :79 := formula.imply

variables (φ : formula A) (ψ : formula A)
#check formula.imply φ (ψ.imply φ)
#check ¬φ

end prop