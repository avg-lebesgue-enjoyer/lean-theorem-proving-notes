/- @file Notes/5Tactics.lean
 - @src https://lean-lang.org/theorem_proving_in_lean4/tactics.html
 -/

/- SECTION: Entering Tactic Mode -/
section entering
  -- NOTE: `apply`
  theorem test
    (p q : Prop)
    (hp : p) (hq : q)
    : p ∧ q ∧ p
    := by
      apply And.intro -- `apply f` will take an implication `f`, whose conclusion is the same type as the current goal, and replace this goal by separate goals for all arguments of `f`
      · exact hp      -- `exact` is a synonym for `apply`, to be used when there are no arguments
      · apply And.intro
        · exact hq
        · exact hp
  #print test
  -- Another way to use `apply`
  theorem test'
    (p q : Prop)
    (hp : p) (hq : q)
    : p ∧ q ∧ p
    := by
      apply And.intro hp
      apply And.intro hq hp
  -- Can use a semicolon to separate tactics on a single line
  theorem test''
    (p q : Prop)
    (hp : p) (hq : q)
    : p ∧ q ∧ p
    := by
      apply And.intro hp ; apply And.intro hq hp
  -- You can switch between different cases using the `case ⋯ => ⋯` construct
  theorem test'''
    (p q : Prop)
    (hp : p) (hq : q)
    : p ∧ q ∧ p
    := by
      apply And.intro
      case right => -- they don't need to be in order...!
        apply And.intro
        case left  => exact hq
        case right => exact hp
      case left =>
        exact hp
  -- `·` (`\.` or just `.`) is a shorthand for a `case ⋯ => ⋯` expression which matches the first outstanding goal
  theorem test''''
    (p q : Prop)
    (hp : p) (hq : q)
    : p ∧ q ∧ p
    := by
      apply And.intro
      case right =>
        apply And.intro
        · exact hq
        · exact hp
      case left =>
        exact hp
end entering



/- SECTION: Basic Tactics -/
section basic_tactics
  -- NOTE: `intro`
  -- When facing a goal `(a : α) → β a`, the tactic `intro a` does the
  --  `fun (a : α) => ⋯` abstraction for us
  theorem gaming (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
    apply Iff.intro
    case mp =>
      intro h
      apply h.right.elim
      case left =>
        intro hq
        exact Or.inl ⟨h.left, hq⟩
      case right =>
        intro (hr : r) -- can chuck in a type annotation too
        apply Or.inr
        apply And.intro
        · exact h.left
        · exact hr
    case mpr =>
      intro (h : p ∧ q  ∨  p ∧ r)
      apply And.intro
      case left =>
        apply h.elim
        · exact And.left
        · exact And.left
      case right =>
        apply h.elim
        · exact Or.inl ∘ And.right
        · exact Or.inr ∘ And.right
  #print gaming
  -- `intro` can introduce terms in general, not just proofs of propositions
  example (α : Type) : α → α := by
    intro (a : α)
    exact a
  example (α : Type) : ∀ x : α, x = x := by
    intro x
    exact rfl
  -- ofc, you can introduce several thngs at once
  example : ∀ a b c : Nat, a = b → a = c → c = b := by
    intro a b c h_ab h_ac
    apply Eq.trans
    · apply Eq.symm
      exact h_ac
    · assumption -- looks up the assumption `h_ab : a = b` already in the tactic state
  -- You can implicitly pattern match too
  example (α : Type) (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
    intro ⟨x, ⟨h_px, h_qx⟩⟩
    exact ⟨x, ⟨h_qx, h_px⟩⟩
  -- You can also *actually pattern-match
  example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
    intro
    | ⟨x, Or.inl h_px⟩ =>
      exact ⟨x, Or.inr h_px⟩
    | ⟨x, Or.inr h_qx⟩ =>
      exact ⟨x, Or.inl h_qx⟩
end basic_tactics
