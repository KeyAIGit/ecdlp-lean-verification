import Ecdlp.Proved.ParityFourier.StatementsC44B
import Ecdlp.Proved.ParityFourier.ProofsC44L
import Ecdlp.Proved.ParityFourier.ProofsC44d

/-!
# Proof of C44-B (balance of J)

`0 ∉ GammaJ lam B` (C44-6d), so `|J_hat(0)|^2` is one term of the mass of
`J_hat` outside `GammaJ lam B`, which C44-6x bounds.
-/

namespace Ecdlp.ParityFourier.ProofsC44B

open Finset Ecdlp.ParityFourier

theorem jBalanceBound : Ecdlp.ParityFourier.JBalanceBound := by
  intro n _ _ hn2 lam hlam B hB h3
  have h0 : (0 : ZMod n) ∉ GammaJ lam B :=
    Ecdlp.ParityFourier.ProofsC44d.zeroNotInGammaJ n hn2 lam hlam B h3
  have hBn : 2 * B + 1 ≤ n := by nlinarith
  have hmass := Ecdlp.ParityFourier.ProofsC44L.jConcentrationExplicit n hn2 lam hlam B hB hBn
  have hmem : (0 : ZMod n) ∈ (univ \ GammaJ lam B) := by simp [h0]
  calc ‖ft (JC lam) 0‖ ^ 2
      ≤ ∑ γ ∈ (univ \ GammaJ lam B), ‖ft (JC lam) γ‖ ^ 2 :=
        single_le_sum (f := fun γ => ‖ft (JC lam) γ‖ ^ 2) (fun _ _ => by positivity) hmem
    _ ≤ (3 + Real.log (2 * (B : ℝ) + 1)) ^ 2 / (B : ℝ) := hmass

end Ecdlp.ParityFourier.ProofsC44B
