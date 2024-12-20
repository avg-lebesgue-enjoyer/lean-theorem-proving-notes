/- @file Notes/11Conv.lean
 - @src https://lean-lang.org/theorem_proving_in_lean4/conv.html
 -/

/- SECTION: I'm still amazed at `Eq`... -/
set_option pp.proofs true
#print Eq.rec
/-
  *`recursor Eq.rec.{u_tgt, u_src}              `*
  *`  : {α : Sort u_src}                        `*
  *`  → {a : α}                                 `*
  *`  → {motive : (b : α) → a = b → Sort u_tgt} `*
  *`  → motive a (Eq.refl a)                    `*
  *`  → {b : α}                                 `*
  *`  → (t : a = b) → motive b t                `*
-/
set_option pp.proofs false



/- SECTION: Basic navigation and rewriting -/
section nav
  example (a b c : Nat) : a * (b * c) = a * (c * b) := by
    conv =>
      -- 1 goal: `| a * (b * c) = a * (c * b)`
      lhs
      -- 1 goal: `| a * (b * c)`; i.e. we're "focusing on this term"
      congr
      -- 2 goals: `case a => | a` and `case a => | b * c`
      · rfl -- Focusing on the `a` term gets it to the desired `rhs`'s `a` by doing nothing
      · rw [Nat.mul_comm] -- Meanwhile, the `b * c` converts to the `c * b` by doing `rw [Nat.mul_comm]`

  example : (fun x : Nat => 0 + x) = (fun x => x) := by
    conv =>
      lhs -- Manipulating `fun x => 0 + x`
      intro x
      rw [Nat.zero_add]
      rfl
end nav



/- SECTION: Pattern Matching -/
section patmatch
  example (a b c : Nat) : a * (b * c) = a * (c * b) := by
    conv in b * c => -- Navigate by "pattern matching" to exactly where you think we're going
      rw [Nat.mul_comm]
  -- ^^ is syntactic sugar for
  example (a b c : Nat) : a * (b * c) = a * (c * b) := by
    conv =>
      pattern b * c -- does what you think it does
      rw [Nat.mul_comm]
  -- Wildcards are fine:
  example (a b c : Nat) : a * (b * c) = a * (c * b) := by
    conv in _ * c => -- Wildcard gaming
      rw [Nat.mul_comm]
end patmatch



/- SECTION: Structuring conversion tactics -/
section structure_lol
  example (a b c : Nat) : (0 + a) * (b * c) = a * (c * b) := by
    conv =>
      lhs   -- Move to the `lhs` of the top level of the syntax tree
      congr -- Split onto the arguments of the (new) top level of the syntax tree
      · rw [Nat.zero_add]
      · rw [Nat.mul_comm]
end structure_lol



/- SECTION: Other tactics inside conversion mode -/
section others
  example (a b c : Nat) : (0 + a) * (b * c) = a * (c * b) := by
    conv =>
      arg 1 -- `1`st argument (not `0`-indexed; `1`-indexed T^T) of thing at top of syntax tree
      arg 1
      rw [Nat.zero_add]
      rfl
      done
    conv =>
      arg 2
      arg 2
      rw [Nat.mul_comm]
      rfl
      done

  -- NOTE: `args` is another name for `congr`

  -- NOTE: `simp` does the same thing as in normal tactic mode. Same with `exact` and `apply`, fwiw.
  def f (x : Nat) := if x > 0 then x + 1 else x + 2
  example
    (g : Nat → Nat) (x : Nat)
    (h₁ : g x = x + 1)
    (h₂ : x > 0)
    : g x = f x
    := by
      conv =>
        rhs
        simp [f, h₂]
      exact h₁

  -- NOTE: `tactic => ⋯` goes back to normal tactic mode for a bit
  example
    (g : Nat → Nat → Nat) (x : Nat)
    (h₁ : ∀ a : Nat, a ≠ 0 → g a a = 0 + 1)
    (h₂ : x ≠ 0)
    : g x x + x = 1 + x
    := by
      have h₃ : x ≠ 0 → g x x = 0 + 1 := h₁ x -- This is a bit artificial, I know
      conv at h₃ => { -- Do some rewriting of the hypothesis `h₃`
        pattern 0 + 1
        rw [Nat.zero_add]
      }
      rw [h₃ h₂]
  example
    (g : Nat → Nat → Nat) (x : Nat)
    (h₁ : ∀ a : Nat, a ≠ 0 → g a a = 1)
    (h₂ : x ≠ 0)
    : g x x + x = 1 + x
    := by
      conv => {
        lhs ; lhs
        rw [h₁]
        · skip
        · tactic => assumption
      }
end others
