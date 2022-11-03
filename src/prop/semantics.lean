import tactic data.set
import prop.language
 
namespace prop
 
def satisfy (v : ℕ → Prop) : Formula → Prop
| (Formula.var p) := v p
| ⊥'              := false
| (φ →' ψ)        := satisfy φ → satisfy ψ

def models (v : ℕ → Prop) (φ : Formula) : Prop := satisfy v φ

notation `[`v`]` `⊨` φ :25 := models v φ
infix `⊨` :25 := models

end prop