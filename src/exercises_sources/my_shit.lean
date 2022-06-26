import data.real.basic
import tactic.field_simp
import data.real.sqrt
import tactic.unfold_cases

theorem my_strong_induction_on {p : ℕ → Prop} (h: ∀ n, (∀ m < n, p m) → p n) (n : ℕ) : p n :=
begin
apply h n,
induction n,
{ exact (λ _, not.elim (nat.not_lt_zero _)) },
{
  intro m,
  by_cases m = n_n,
  {
    subst h,
    exact (λ _, h m n_ih),
  },
  {
    intro,
    have : m < n_n := nat.lt_of_le_and_ne (nat.le_of_lt_succ H) h,
    exact n_ih m this,
  }
}
end

def from_digits : list ℕ → ℕ
| [] := 0
| (d :: ds) := d + 10 * from_digits ds

def digits : ℕ → list ℕ
| 0 := []
| n@(m + 1) :=
  have n / 10 < n, from nat.div_lt_self' _ _,
  n % 10 :: digits (n / 10)

def is_digits (l : list ℕ) : Prop := ¬[0].is_suffix l ∧ ∀ n ∈ l, n < 10

lemma digit_le_self (l : list ℕ) : ∀ n, from_digits l = n → ∀ d ∈ l, d ≤ n :=
begin
induction l,
{
  intros _ _ d h,
  exact absurd h (list.not_mem_nil d),
},
{
  intros n h₁ d h₂,
  cases h₂,
  {
    subst h₂,
    unfold from_digits at h₁,
    exact nat.le_of_add_le_left (le_of_eq h₁),
  },
  {
    have : d ≤ (n - l_hd) / 10 := begin
      apply l_ih,
      {
        unfold from_digits at h₁,
        subst h₁,
        rw nat.add_sub_cancel_left,
        rw nat.mul_div_right,
        exact nat.succ_pos',
      },
      { assumption }
    end,
    apply le_trans this,
    apply (nat.div_le_iff_le_mul_add_pred nat.succ_pos').mpr,
    apply le_trans (nat.sub_le _ _),
    apply le_trans (nat.le_mul_of_pos_left (nat.succ_pos 9)),
    rw add_comm,
    exact le_add_self,
  },
}
end

theorem digits_unique (n : ℕ) : ∀ (l : list ℕ),
  is_digits l ∧ from_digits l = n ↔ l = digits n :=
begin
apply nat.strong_induction_on n,
clear n,
intros n ih l,
split,
{
  rintro ⟨⟨h₁, h₂⟩, h₃⟩,
  cases l,
  {
    subst h₃,
    change list.nil = digits 0,
    unfold digits,
  },
  {
    cases n,
    {
      exfalso,
      apply h₁,
      have : ∀ d ∈ (l_hd :: l_tl), d = 0 := begin
        intro d,
        rw ←nat.le_zero_iff,
        exact digit_le_self (l_hd :: l_tl) 0 h₃ d,
      end,
      rw (list.eq_repeat.mpr ⟨rfl, this⟩),
      rw list.length_cons,
      rw ←list.reverse_repeat,
      rw list.repeat_succ,
      rw list.reverse_cons,
      exact list.suffix_append _ _,
    },
    unfold digits,
    unfold from_digits at h₃,
    have : n.succ / 10 = from_digits l_tl ∧ n.succ % 10 = l_hd :=
      (nat.div_mod_unique (nat.zero_lt_succ _)).mpr ⟨h₃, h₂ l_hd (list.mem_cons_self _ _)⟩,
    cases this,
    subst this_right,
    rw list.cons_inj,
    have : n.succ / 10 < n.succ := nat.div_lt_self nat.succ_pos' (nat.one_lt_succ_succ 8),
    apply (ih (n.succ / 10) this l_tl).mp,
    split,
    split,
    {
      intro h₄,
      apply h₁,
      exact (list.suffix_cons_iff.mpr (or.inr h₄)),
    },
    {
      intros,
      apply h₂,
      exact list.mem_cons_of_mem _ H,
    },
    {
      exact this_left.symm,
    }
  },
},
{
  intro h,
  cases n;
  unfold digits at h;
  subst h;
  unfold is_digits;
  unfold from_digits,
  {
    exact ⟨⟨by dec_trivial, λ n, not.elim (list.not_mem_nil n)⟩, rfl⟩,
  },
  {
    have : ((n + 1) / 10) < n + 1 := nat.div_lt_self nat.succ_pos' (by norm_num),
    have ih' := (ih ((n + 1) / 10) this (digits ((n + 1) / 10))).mpr rfl,
    split,
    split,
    {
      rw list.suffix_cons_iff,
      intro h,
      cases h,
      {
        by_cases h₁ : (n + 1) % 10 = 0,
        {
          rw h₁ at h,
          simp at h,
          by_cases h₂ : (n + 1) / 10 = 0,
          {
            have := (nat.div_mod_unique nat.succ_pos').mp ⟨h₂, h₁⟩,
            exact absurd this.left.symm (nat.succ_ne_zero n),
          },
          {
            cases (n + 1) / 10;
            unfold digits at h;
            contradiction,
          }
        },
        {
          simp only at h,
          exact absurd h.left.symm h₁,
        }
      },
      {
        exact absurd h ih'.1.1,
      }
    },
    {
      intros,
      rw list.mem_cons_iff at H,
      cases H,
      {
        subst H,
        exact nat.mod_lt _ nat.succ_pos',
      },
      {
        exact ih'.1.2 n_1 H,
      }
    },
    {
      rw ih'.2,
      refine ((nat.div_mod_unique nat.succ_pos').mp _).1,
      split; refl,
    }
  }
}
end

@[simp]
theorem from_digits_of_digits (n : ℕ) : from_digits (digits n) = n :=
begin
have := (digits_unique n (digits n)).mpr rfl,
exact this.right,
end

@[simp]
theorem digits_of_from_digits (l : list ℕ) (h : is_digits l) : digits (from_digits l) = l :=
begin
symmetry,
exact (digits_unique (from_digits l) l).mp ⟨h, rfl⟩,
end

-- def sum_digits : ℕ → ℕ
-- | 0 := 0
-- | n@(m + 1) :=
-- have n / 10 < n, from nat.div_lt_self' _ _,
-- sum_digits (n / 10) + (n % 10)

-- @[simp]
-- lemma sum_digits_of_zero : sum_digits 0 = 0 :=
-- by unfold sum_digits

-- @[simp]
-- lemma sum_digits_lt_10 (n : ℕ) (h : n < 10): sum_digits n = n :=
-- begin

-- end

-- theorem foo2 (n : ℕ) (h: n % 10 < 9) : sum_digits (n + 1) = sum_digits n + 1 := sorry
-- theorem foo3 (n : ℕ) (h : n % 10 = 9) : sum_digits (n + 1) % 9 = sum_digits n + 1 % 9 := sorry

-- theorem foo : ∀ (n : ℕ), sum_digits n % 9 = n % 9
-- | 0 := by simp
-- | 1 := sorry
-- | n@(m + 2) := sorry

-- #reduce (1 : ℕ) / 10
-- example (n: ℕ) : sum_digits n % 9 = (n % 9) :=
-- -- | 0 := sorry
-- -- | 1 := sorry
-- -- | (n + 2) : =
-- begin
-- induction n,
-- case nat.zero { unfold sum_digits, },
-- case nat.succ : a ih {
--   cases a,
--   { unfold sum_digits,
--     change (sum_digits 0 + 1) % 9 = 1,
--     unfold sum_digits,
--     refl },
--   by_cases h_lt_9 : a.succ % 10 < 9,
--   { unfold sum_digits,
--     have : (a.succ.succ) / 10 = a.succ / 10 := sorry,
--     rw this,
--     have : (a.succ.succ) % 10 = a.succ % 10 + 1 := sorry,
--     rw this,
--     unfold sum_digits at ih,
--     rw ←add_assoc,
--     rw ←nat.mod_add_mod,
--     rw ih,
--     simp,
--     },
--   have h9 : a.succ % 10 = 9 := sorry,
--   unfold sum_digits,
--   have : (a.succ + 1) / 10 = a.succ / 10 + 1 := sorry,
--   rw this,
--   unfold sum_digits at ih,
--   rw h9 at ih,
--   simp at ih,
--   unfold sum_digits,

-- }
-- end

-- theorem quadratic_rearrange (a b c x: ℝ) (h: a ≠ 0) :
--   a * x ^ 2 + b * x + c = a * (x + (b / (a * 2))) ^ 2 + (c - (b ^ 2) / (a * 4)) :=
-- begin
-- field_simp,
-- ring,
-- end

-- -- a * (x + (b / (a * 2))) ^ 2 + (c - (b ^ 2) / (a * 4)) = 0
-- -- →
-- -- a * (x + (b / (a * 2))) ^ 2 = (b ^ 2) / (a * 4) - c
-- -- (x + (b / (a * 2))) ^ 2 = (b ^ 2) / (a ^ 2 * 4) - c / a
-- -- (x + (b / (a * 2))) = sqrt((b ^ 2) / (a ^ 2 * 4) - c / a) - (b / (a * 2))
-- -- x = sqrt((b ^ 2) / (a ^ 2 * 4) - c / a) - (b / (a * 2))
-- -- x = (-b ± √(b^2 - 4ac)) / 2a

-- def big_root (a b c x : ℝ) :
--   a ≠ 0
--   → 0 ≤ ((b ^ 2) / (a ^ 2 * 4) - c / a) - (b / (a * 2))
--   → x = real.sqrt ((b ^ 2) / (a ^ 2 * 4) - c / a) - (b / (a * 2))
--   → a * x ^ 2 + b * x + c = 0 :=
-- begin
-- intros ha hnn h,
-- rw quadratic_rearrange _ _ _ _ ha,
-- rw ←add_eq_of_eq_sub,
-- end

-- def two_roots (a d e : ℝ): ∃ (s s' : ℝ), ∀ (x : ℝ), a * (x + d) ^ 2 + e = 0 → x = s ∨ x = s' :=
-- begin

-- end
