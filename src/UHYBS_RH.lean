import Mathlib.Analysis.SpecialFunctions.Zeta

open Real Complex

noncomputable def zetaWeight (t : ℝ) : ℝ :=
  ‖riemannZeta (1/2 + t * Complex.I)‖^2

structure AbstractMean (α : Type*) where
  mean : ℕ → α

def altSeq : AbstractMean ℝ := {
  mean := λ n => if n = 0 then 0 else (Finset.range n).sum (λ k => (-1:ℝ)^k) / n
}

def sin2nSeq : AbstractMean ℝ := {
  mean := λ n => if n = 0 then 0 else (Finset.range n).sum (λ k => Real.sin (2^k)) / n
}

noncomputable def UHYBSZetaMixed
  (methods : List (AbstractMean ℝ)) (ts : List ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  let vals := methods.map (λ m => m.mean n)
  let ws := ts.map zetaWeight
  let S := ws.foldr (· + ·) 0
  if S = 0 then vals.head? |>.getD 0
  else (List.zip ws vals).foldl (λ acc (wv : ℝ × ℝ) => acc + (wv.1 / S) * wv.2) 0

#eval UHYBSZetaMixed [altSeq, sin2nSeq] [1.0, 3.0] 2.0 100