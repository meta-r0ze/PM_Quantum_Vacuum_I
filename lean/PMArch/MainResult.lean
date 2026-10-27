import PMArch.Selection
import PMArch.Impedance

namespace PMArch

/-- End-to-end conditional result. The schedule determines the period; all
other architectural integers and the impedance law remain model inputs. -/
theorem schedule_impedance_bounds {Δ : ℕ}
    (encode : Fin 32 → Fin Δ) (hinj : Function.Injective encode)
    (advance : Equiv.Perm (Fin Δ)) (active : Finset (Fin Δ))
    (hactive : active.card = 32) (hgap : NoAdjacentIdle advance active)
    (hc : Δ ∈ discriminantCandidates) :
    (137.035999212381397211 : ℝ) < impedance { baseline with period := Δ } ∧
    impedance { baseline with period := Δ } < (137.035999212381397213 : ℝ) := by
  have hd := schedule_selects_43 encode hinj advance active hactive hgap hc
  subst Δ
  exact geometricIndex_bounds

end PMArch
