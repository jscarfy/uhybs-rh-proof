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


def UHYBS (n : ℕ) (t : ℝ) : ℂ :=
let s := 1/2 + t * I in
∑' (k : ℕ) in finset.range n, (1 : ℂ) / (k + 1 : ℂ) ^ s


theorem sketch_RH_proof :
  (∀ s : ℂ, nontrivial_zero s → re s = 1/2) :=
begin
  intros s hs,
  by_contradiction h,

  have h1 : re s ≠ 1/2 := h,

  by_cases hgt : re s > 1/2,
  {

    have divg : tendsto (λ n, ∑ k in finset.range n, 1 / (k+1 : ℂ) ^ s) at_top at_top,
    {

      sorry
    },

    rw ← hs.1 at divg,
    exact absurd divg (not_tendsto_const_at_top ℂ 0)
  },
  {

    have conv : tendsto (λ n, ∑ k in finset.range n, 1 / (k+1 : ℂ) ^ s) at_top 0,
    {

      sorry
    },
    rw ← hs.1 at conv,
    exact absurd conv (not_tendsto_const_at_top ℂ 0)
  }
end


open_locale big_operators
open filter finset

noncomputable theory
open_locale classical


lemma norm_nat_pow_complex (k : ℕ) (s : ℂ) (hk : k ≠ 0) :
  complex.abs ((k : ℂ) ^ s) = real.exp (real.log k * s.re) :=
begin
  rw [← complex.abs_of_real ↑k, complex.abs_cpow_eq_exp_arg_mul_log],
  simp only [complex.abs_of_real, abs_cast_nat, ne.def, hk, not_false_iff],
  exact_mod_cast hk,
end

lemma partial_zeta_tendsto (s : ℂ) (hs : 1 < s.re) :
  tendsto (λ n, ∑ k in range n, 1 / (k + 1 : ℂ) ^ s) at_top (nhds (riemann_zeta s)) :=
begin

  apply riemann_zeta_has_sum_of_re_gt_one.has_sum.tendsto_sum_nat,
  exact hs,
end


lemma partial_zeta_diverges (s : ℂ) (hs : s.re ≤ 1 ∧ s.re ≠ 1/2) :
  tendsto (λ n, ∑ k in range n, 1 / (k + 1 : ℂ) ^ s) at_top at_top :=
begin

  obtain ⟨hle, hne⟩ := hs,

  have cmp : ∀ k ≥ 1, complex.abs (1 / (k : ℂ) ^ s) ≥ 1 / k,
  {
    intros k hk,
    have : complex.abs ((k : ℂ) ^ s) = real.exp (real.log k * s.re),
      from norm_nat_pow_complex k s (nat.pos_iff_ne_zero.mp hk),
    rw [complex.abs_div, complex.abs_one, this],
    simp only [div_le_iff', real.exp_pos],
    apply le_of_lt,
    rw [← real.exp_lt_exp],
    have : real.log k * s.re < real.log k,
    { apply mul_lt_of_lt_one_right,
      { exact real.log_pos (nat.one_lt_cast.2 hk), },
      { rw [← one_mul (real.log k)],
        apply mul_lt_mul_of_pos_left,
        exact hle.lt_of_ne hne,
        exact real.log_pos (nat.one_lt_cast.2 hk), }, },
    exact this,
  },

  have harmonic_div : tendsto (λ n, ∑ k in range n, 1 / (k + 1 : ℝ)) at_top at_top :=
    tendsto_harmonic_at_top,
  apply tendsto_at_top_mono (λ n, real.of_complex_abs_le_sum_le n cmp) harmonic_div,
end


theorem RH_formalized :
  riemann_hypothesis :=
begin
  intros s hs,
  by_contradiction h,
  have h₁ : s.re ≠ 1/2 := h,
  by_cases hgt : s.re > 1/2,
  {
    have divg := partial_zeta_diverges s ⟨le_of_lt hgt, h₁⟩,
    rw hs.1 at divg,
    exact not_tendsto_const_at_top _ 0 divg,
  },
  {
    have lt : s.re < 1/2 := lt_of_le_of_ne (le_of_not_lt hgt) h₁.symm,
    have conv_to_0 : tendsto (λ n, ∑ k in range n, 1 / (k + 1 : ℂ) ^ s) at_top 0,
    {
structure UYFM (α : Type*) :=
(seq : ℕ → α)                          
(weight : ℕ → α → ℝ)                  
(normalize : ℕ → ℝ := λ n, ∑ k in finset.range n, weight k (seq k)) 
(mean : ℕ → α := λ n,
  let W := ∑ k in finset.range n, weight k (seq k) in
  if W = 0 then seq 0 
  else ∑ k in finset.range n, ((weight k (seq k)) / W : ℝ) • seq k)
    },
    rw hs.1 at conv_to_0,
    exact not_tendsto_const_at_top _ 0 conv_to_0,
  }
end


structure UHYBS (α : Type*) :=
(methods : list (UYFM α)) 
(weights : ℕ → α → list ℝ) 
(mixed_mean : ℕ → α := λ n,
  let vals := (methods.map (λ m, m.mean n)),
      ws := weights n ((methods.head'.get_or_else (⟨0, λ _, 0, 1, 0⟩ : UYFM α)).seq n),
      S : ℝ := ws.sum in
  if S = 0 then vals.head' 
  else
    (list.zip ws vals).foldl (λ acc ⟨w, v⟩, acc + (w / S) • v) 0)

def log_sin_seq : ℕ → ℂ := λ n, complex.sin (complex.log (n + 1 : ℂ))

def fractal_weight : ℕ → ℂ → ℝ := λ k s, real.exp (-(complex.norm s)^2) / (k + 1)

def log_sin_UYFM : UYFM ℂ :=
{ seq := log_sin_seq,
  weight := fractal_weight }

structure UYOS (α : Type*) :=
(seq : ℕ → α)                                     
lambda : ℕ → ℝ                                   
ω : ℕ → list ℝ                                   
α : ℕ → list ℝ                                   
(mean : ℕ → α := λ n,
  ∑ k in finset.range n,
    let decay := real.exp ( - (lambda k) * (k : ℝ) / n),
        osc_sum := list.sum (list.map₂ (λ ai wi, ai * real.cos (wi * k / n)) (α k) (ω k)) in
    (decay * osc_sum : ℝ) • seq k)

 
def alt_seq : ℕ → ℝ := λ k, (-1)^k

def lambda_decay : ℕ → ℝ := λ k, 0.5 + 1.0 / (k + 1)  
def freq_list : ℕ → list ℝ := λ k, [real.pi]          
def alpha_list : ℕ → list ℝ := λ k, [1.0]             

def alt_UYOS : UYOS ℝ :=
{ seq := alt_seq,
  lambda := lambda_decay,
  ω := freq_list,
  α := alpha_list }

#eval alt_UYOS.mean 100  

structure AbstractMean (α : Type*) :=
(mean : ℕ → α)

def UHYBS_mixed {α : Type*} (methods : list (AbstractMean α))
  (weights : list ℝ) (n : ℕ) : α :=
let vals := methods.map (λ m, m.mean n),
    S : ℝ := weights.sum in
if S = 0 then vals.head' 
else (list.zip weights vals).foldl (λ acc ⟨w, v⟩, acc + (w / S) • v) 0


def logsin_UYFM_abstract : AbstractMean ℂ :=
{ mean := log_sin_UYFM.mean }

def alt_UYOS_abstract : AbstractMean ℝ :=
{ mean := alt_UYOS.mean }

def log_star (n : ℕ) : ℕ :=
(nat.iterate (λ x, nat.log x + 1) n).find (λ j, (2 : ℕ)^j ≥ n)  

def lambda_j (n j : ℕ) : ℕ :=
n ^ (j+1) / (nat.log n + nat.log (nat.log n + 1) + j + 1)

def mu_j (seq : ℕ → ℝ) (n j : ℕ) : ℝ :=
let l0 := lambda_j n j,
    l1 := lambda_j n (j+1),
    range_j := finset.Ico l0 l1 in
if range_j.card = 0 then 0
else (1 : ℝ) / range_j.card * (∑ k in range_j, seq k)

def p_j (j n : ℕ) : ℝ := real.exp (-(j : ℝ) / (nat.log n + 1))



structure UYMM :=
(seq : ℕ → ℝ)
(mean : ℕ → ℝ := λ n,
  let J := log_star n,
      μs := list.of_fn (λ j, mu_j seq n j),
      ps := list.of_fn (λ j, p_j j n),
      total := ps.sum in
  if total = 0 then μs.head' 
  else (list.zip ps μs).foldl (λ acc ⟨w, v⟩, acc + (w / total) * v) 0)


def sin2n_seq : ℕ → ℝ := λ n, real.sin (2^n)

def sin2n_UYMM : UYMM :=
{ seq := sin2n_seq }
#eval sin2n_UYMM.mean 100  


def sin2n_UYMM_abstract : AbstractMean ℝ :=
{ mean := sin2n_UYMM.mean }
def example_mixed : ℕ → ℝ :=
  UHYBS_mixed [alt_UYOS_abstract, sin2n_UYMM_abstract]
              [0.6, 0.4]  
#eval example_mixed 100


noncomputable def zeta_weight (t : ℝ) : ℝ :=
let s := 1/2 + t * complex.I in
complex.norm (riemann_zeta s)^2

noncomputable def weight_vector (ts : list ℝ) (t : ℝ) : list ℝ :=
let numerator := zeta_weight t,
    den := (ts.map zeta_weight).sum in
if den = 0 then list.repeat (1 / ts.length) ts.length
else ts.map (λ tj, zeta_weight tj / den)

noncomputable def UHYBS_zeta_mixed {α : Type*} [has_scalar ℝ α] [has_zero α] [has_add α]
  (methods : list (AbstractMean α)) (ts : list ℝ) (t : ℝ) (n : ℕ) : α :=
let vals := methods.map (λ m, m.mean n),
    ws := weight_vector ts t,
    S : ℝ := ws.sum in
if S = 0 then vals.head'
else (list.zip ws vals).foldl (λ acc ⟨w, v⟩, acc + (w / S) • v) 0


noncomputable def RH_behavior_check (methods : list (AbstractMean ℝ)) (ts : list ℝ) (t : ℝ) :
  ℕ → ℝ :=
λ n, UHYBS_zeta_mixed methods ts t n


def example_methods : list (AbstractMean ℝ) :=
  [alt_UYOS_abstract, sin2n_UYMM_abstract]

def example_ts : list ℝ := [1.0, 3.0]  

#eval RH_behavior_check example_methods example_ts 2.0 100

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


def UHYBS (n : ℕ) (t : ℝ) : ℂ :=
let s := 1/2 + t * I in
∑' (k : ℕ) in finset.range n, (1 : ℂ) / (k + 1 : ℂ) ^ s


theorem sketch_RH_proof :
  (∀ s : ℂ, nontrivial_zero s → re s = 1/2) :=
begin
  intros s hs,
  by_contradiction h,

  have h1 : re s ≠ 1/2 := h,

  by_cases hgt : re s > 1/2,
  {

    have divg : tendsto (λ n, ∑ k in finset.range n, 1 / (k+1 : ℂ) ^ s) at_top at_top,
    {

      sorry
    },

    rw ← hs.1 at divg,
    exact absurd divg (not_tendsto_const_at_top ℂ 0)
  },
  {

    have conv : tendsto (λ n, ∑ k in finset.range n, 1 / (k+1 : ℂ) ^ s) at_top 0,
    {

      sorry
    },
    rw ← hs.1 at conv,
    exact absurd conv (not_tendsto_const_at_top ℂ 0)
  }
end


open_locale big_operators
open filter finset

noncomputable theory
open_locale classical


lemma norm_nat_pow_complex (k : ℕ) (s : ℂ) (hk : k ≠ 0) :
  complex.abs ((k : ℂ) ^ s) = real.exp (real.log k * s.re) :=
begin
  rw [← complex.abs_of_real ↑k, complex.abs_cpow_eq_exp_arg_mul_log],
  simp only [complex.abs_of_real, abs_cast_nat, ne.def, hk, not_false_iff],
  exact_mod_cast hk,
end

lemma partial_zeta_tendsto (s : ℂ) (hs : 1 < s.re) :
  tendsto (λ n, ∑ k in range n, 1 / (k + 1 : ℂ) ^ s) at_top (nhds (riemann_zeta s)) :=
begin

  apply riemann_zeta_has_sum_of_re_gt_one.has_sum.tendsto_sum_nat,
  exact hs,
end


lemma partial_zeta_diverges (s : ℂ) (hs : s.re ≤ 1 ∧ s.re ≠ 1/2) :
  tendsto (λ n, ∑ k in range n, 1 / (k + 1 : ℂ) ^ s) at_top at_top :=
begin

  obtain ⟨hle, hne⟩ := hs,

  have cmp : ∀ k ≥ 1, complex.abs (1 / (k : ℂ) ^ s) ≥ 1 / k,
  {
    intros k hk,
    have : complex.abs ((k : ℂ) ^ s) = real.exp (real.log k * s.re),
      from norm_nat_pow_complex k s (nat.pos_iff_ne_zero.mp hk),
    rw [complex.abs_div, complex.abs_one, this],
    simp only [div_le_iff', real.exp_pos],
    apply le_of_lt,
    rw [← real.exp_lt_exp],
    have : real.log k * s.re < real.log k,
    { apply mul_lt_of_lt_one_right,
      { exact real.log_pos (nat.one_lt_cast.2 hk), },
      { rw [← one_mul (real.log k)],
        apply mul_lt_mul_of_pos_left,
        exact hle.lt_of_ne hne,
        exact real.log_pos (nat.one_lt_cast.2 hk), }, },
    exact this,
  },

  have harmonic_div : tendsto (λ n, ∑ k in range n, 1 / (k + 1 : ℝ)) at_top at_top :=
    tendsto_harmonic_at_top,
  apply tendsto_at_top_mono (λ n, real.of_complex_abs_le_sum_le n cmp) harmonic_div,
end


theorem RH_formalized :
  riemann_hypothesis :=
begin
  intros s hs,
  by_contradiction h,
  have h₁ : s.re ≠ 1/2 := h,
  by_cases hgt : s.re > 1/2,
  {
    have divg := partial_zeta_diverges s ⟨le_of_lt hgt, h₁⟩,
    rw hs.1 at divg,
    exact not_tendsto_const_at_top _ 0 divg,
  },
  {
    have lt : s.re < 1/2 := lt_of_le_of_ne (le_of_not_lt hgt) h₁.symm,
    have conv_to_0 : tendsto (λ n, ∑ k in range n, 1 / (k + 1 : ℂ) ^ s) at_top 0,
    {
structure UYFM (α : Type*) :=
(seq : ℕ → α)                          
(weight : ℕ → α → ℝ)                  
(normalize : ℕ → ℝ := λ n, ∑ k in finset.range n, weight k (seq k)) 
(mean : ℕ → α := λ n,
  let W := ∑ k in finset.range n, weight k (seq k) in
  if W = 0 then seq 0 
  else ∑ k in finset.range n, ((weight k (seq k)) / W : ℝ) • seq k)
    },
    rw hs.1 at conv_to_0,
    exact not_tendsto_const_at_top _ 0 conv_to_0,
  }
end


structure UHYBS (α : Type*) :=
(methods : list (UYFM α)) 
(weights : ℕ → α → list ℝ) 
(mixed_mean : ℕ → α := λ n,
  let vals := (methods.map (λ m, m.mean n)),
      ws := weights n ((methods.head'.get_or_else (⟨0, λ _, 0, 1, 0⟩ : UYFM α)).seq n),
      S : ℝ := ws.sum in
  if S = 0 then vals.head' 
  else
    (list.zip ws vals).foldl (λ acc ⟨w, v⟩, acc + (w / S) • v) 0)

def log_sin_seq : ℕ → ℂ := λ n, complex.sin (complex.log (n + 1 : ℂ))

def fractal_weight : ℕ → ℂ → ℝ := λ k s, real.exp (-(complex.norm s)^2) / (k + 1)

def log_sin_UYFM : UYFM ℂ :=
{ seq := log_sin_seq,
  weight := fractal_weight }

structure UYOS (α : Type*) :=
(seq : ℕ → α)                                     
lambda : ℕ → ℝ                                   
ω : ℕ → list ℝ                                   
α : ℕ → list ℝ                                   
(mean : ℕ → α := λ n,
  ∑ k in finset.range n,
    let decay := real.exp ( - (lambda k) * (k : ℝ) / n),
        osc_sum := list.sum (list.map₂ (λ ai wi, ai * real.cos (wi * k / n)) (α k) (ω k)) in
    (decay * osc_sum : ℝ) • seq k)

 
def alt_seq : ℕ → ℝ := λ k, (-1)^k

def lambda_decay : ℕ → ℝ := λ k, 0.5 + 1.0 / (k + 1)  
def freq_list : ℕ → list ℝ := λ k, [real.pi]          
def alpha_list : ℕ → list ℝ := λ k, [1.0]             

def alt_UYOS : UYOS ℝ :=
{ seq := alt_seq,
  lambda := lambda_decay,
  ω := freq_list,
  α := alpha_list }

#eval alt_UYOS.mean 100  

structure AbstractMean (α : Type*) :=
(mean : ℕ → α)

def UHYBS_mixed {α : Type*} (methods : list (AbstractMean α))
  (weights : list ℝ) (n : ℕ) : α :=
let vals := methods.map (λ m, m.mean n),
    S : ℝ := weights.sum in
if S = 0 then vals.head' 
else (list.zip weights vals).foldl (λ acc ⟨w, v⟩, acc + (w / S) • v) 0


def logsin_UYFM_abstract : AbstractMean ℂ :=
{ mean := log_sin_UYFM.mean }

def alt_UYOS_abstract : AbstractMean ℝ :=
{ mean := alt_UYOS.mean }

def log_star (n : ℕ) : ℕ :=
(nat.iterate (λ x, nat.log x + 1) n).find (λ j, (2 : ℕ)^j ≥ n)  

def lambda_j (n j : ℕ) : ℕ :=
n ^ (j+1) / (nat.log n + nat.log (nat.log n + 1) + j + 1)

def mu_j (seq : ℕ → ℝ) (n j : ℕ) : ℝ :=
let l0 := lambda_j n j,
    l1 := lambda_j n (j+1),
    range_j := finset.Ico l0 l1 in
if range_j.card = 0 then 0
else (1 : ℝ) / range_j.card * (∑ k in range_j, seq k)

def p_j (j n : ℕ) : ℝ := real.exp (-(j : ℝ) / (nat.log n + 1))



structure UYMM :=
(seq : ℕ → ℝ)
(mean : ℕ → ℝ := λ n,
  let J := log_star n,
      μs := list.of_fn (λ j, mu_j seq n j),
      ps := list.of_fn (λ j, p_j j n),
      total := ps.sum in
  if total = 0 then μs.head' 
  else (list.zip ps μs).foldl (λ acc ⟨w, v⟩, acc + (w / total) * v) 0)


def sin2n_seq : ℕ → ℝ := λ n, real.sin (2^n)

def sin2n_UYMM : UYMM :=
{ seq := sin2n_seq }
#eval sin2n_UYMM.mean 100  


def sin2n_UYMM_abstract : AbstractMean ℝ :=
{ mean := sin2n_UYMM.mean }
def example_mixed : ℕ → ℝ :=
  UHYBS_mixed [alt_UYOS_abstract, sin2n_UYMM_abstract]
              [0.6, 0.4]  
#eval example_mixed 100


noncomputable def zeta_weight (t : ℝ) : ℝ :=
let s := 1/2 + t * complex.I in
complex.norm (riemann_zeta s)^2

noncomputable def weight_vector (ts : list ℝ) (t : ℝ) : list ℝ :=
let numerator := zeta_weight t,
    den := (ts.map zeta_weight).sum in
if den = 0 then list.repeat (1 / ts.length) ts.length
else ts.map (λ tj, zeta_weight tj / den)

noncomputable def UHYBS_zeta_mixed {α : Type*} [has_scalar ℝ α] [has_zero α] [has_add α]
  (methods : list (AbstractMean α)) (ts : list ℝ) (t : ℝ) (n : ℕ) : α :=
let vals := methods.map (λ m, m.mean n),
    ws := weight_vector ts t,
    S : ℝ := ws.sum in
if S = 0 then vals.head'
else (list.zip ws vals).foldl (λ acc ⟨w, v⟩, acc + (w / S) • v) 0


noncomputable def RH_behavior_check (methods : list (AbstractMean ℝ)) (ts : list ℝ) (t : ℝ) :
  ℕ → ℝ :=
λ n, UHYBS_zeta_mixed methods ts t n


def example_methods : list (AbstractMean ℝ) :=
  [alt_UYOS_abstract, sin2n_UYMM_abstract]

def example_ts : list ℝ := [1.0, 3.0]  

#eval RH_behavior_check example_methods example_ts 2.0 100

