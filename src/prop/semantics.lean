import tactic data.set
import prop.language
 
namespace prop
 
def val : Formula → Prop
| ⊥'        := false
| (φ →' ψ)  := ¬(val φ) ∨ (val ψ)  

def models (φ : Formula) : Prop := val φ

-- notation Γ `⊨` φ : 25 := models Γ φ
notation `⊨` φ : 25 := models φ

end prop