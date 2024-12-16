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

  -- NOTE: `intros` is a version of `intro` that introduces as much stuff as possible and gives automatically chosen names for all of them
  example : ∀ a b c : Nat, a = b → a = c → c = b := by
    intros
    apply Eq.trans
    · apply Eq.symm
      assumption
    · assumption

  -- NOTE: the `rfl` tactic is short for `exact rfl`, itself short for `exact Eq.refl _`
  example (y : Nat) : (fun _ : Nat => 0) y = 0 :=
    by rfl

  -- NOTE: The `repeat t` tactic, where `t` is a tactic, applies a tactic as many times as it may be applied, until we stop making progress
  example : ∀ a b c : Nat, a = b → a = c → c = b := by
    intros
    apply Eq.trans
    apply Eq.symm
    repeat assumption

  -- NOTE: `revert x`, where `x` is a variable name already in the tactic state, will generalise away from the specific name `x`
  example (x : Nat) : x = x := by
    revert x  -- goal is `⊢ ∀ (x : Nat), x = x`
    exact Eq.refl
  -- If you `revert` a hypothesis, then the goal becomes an implication. This is perhaps the more useful use case of `revert`
  example (x y : Nat) (h : x = y) : y = x := by
  revert h
  exact Eq.symm
  -- `revert`ing a name will revert any names that depend on it too.
  example (x y : Nat) (h : x = y) : y = x := by
    revert x -- *`⊢ ∀ (x : Nat), x = y → y = x`*
    intros
    apply Eq.symm
    assumption
  -- Ofc, you can `revert` multiple things at once
  example (x y : Nat) (h : x = y) : y = x := by
    revert x y -- *`⊢ ∀ (x y : Nat), x = y → y = x`*
    intros
    apply Eq.symm
    assumption

  -- NOTE: `generalize e = x` replaces all instances of an expression `e` in the current goal with a new variable name `x`, and asks to prove the universally quantified generalised goal.
  --       Ofc, this may result in asking one to prove something unprovable.
  example : 3 = 3 := by
    generalize 3 = x
    rfl
  -- You can record your generalisation with a proof term though, to avoid over-eager generalisations
  example : 2 + 3 = 5 := by
    generalize h : 3 = x
    rw [←h]
end basic_tactics



/- SECTION: More tactics -/
section moar
  -- NOTE: The `cases` tactic is a funny `match` construction.
  example (p q : Prop) : p ∨ q → q ∨ p := by
    intro h
    cases h with
    | inl =>  -- don't have to name the argument in the pattern match
      apply Or.inr
      assumption
    | inr hq => -- but can
      exact Or.inl hq
  -- NOTE: Leaving out the `with` makes an "unstructured" form of this
  example (p q : Prop) : p ∨ q → q ∨ p := by
    intro h; cases h
    · apply Or.inr; assumption
    · apply Or.inl; assumption
  -- ^^This unstructured variant is helpful when you can solve several subgoals using the same tactic
  example (p : Prop) : p ∨ p → p := by
    intro h; cases h
    repeat assumption -- `repeat t` applies `t` over and over until `t` stops making progress
  -- In fact, a sneaky way to write something like this is to use the `<;>` combinator.
  --  `s <;> t` applies tactic `s` and then, to each subgoal generated by `s`, applies `t`
  example (p : Prop) : p ∨ p → p := by
    intro h
    cases h <;> assumption

  -- NOTE: The `constructor` tactic `apply`s the unique constructure of a `structure`.
  --       More generally, it `apply`s the first applicable constructive of an `inductive` type.
  example
    (p q r : Prop)
    : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)
    := by
      constructor -- same as `apply Iff.intro`
      case mp =>
        intro ⟨h_p, h_qvr⟩ -- yes, you can pattern-match here :)
        cases h_qvr with
        | inl h_q =>
          apply Or.inl
          exact ⟨h_p, h_q⟩
        | inr h_r =>
          apply Or.inr
          exact ⟨h_p, h_r⟩
      case mpr =>
        intro h; cases h
        <;> constructor -- 4 goals, two of the form `h† : p ∧ _ ⊢ p`
        <;> try apply And.left ‹p ∧ _› -- solves these ^^
        repeat first | (apply Or.inl ∘ And.right $ ‹p ∧ _›) | (apply Or.inr ∘ And.right $ ‹p ∧ _›)
  -- For instance, `constructor` can be used to decompose an `∃ ⋯, ⋯` term
  example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
    intro h; cases h with
    | intro =>
    constructor
    case intro.w => assumption
    apply Or.inl
    assumption
  -- But the `exists` tactic is better suited for explicitly providing a witness to an existential quantifier.
  example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
    intro ⟨x, h⟩ -- if you decompose `h` right here, Lean is actually able to auto-complete the goal remaining after the next line!
    exists x -- says that we wish to introduce a witness to the goal `∃ x, q x ∧ p x` under the name `x`
    have ⟨h_px, h_qx⟩ := h
    constructor <;> assumption
  -- Again, Lean is somewhat good with verifying existential witnesses when stuff is properly spelled out to it
  example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
    intro ⟨x, ⟨h_px, h_qx⟩⟩
    exists x -- the proof that `x` works is by `constructor` and `assumption`, so Lean can fill this in.
  -- You can use these tactics to define functions on data, not just propositions. It's fucking weird though...
  def swap_pair {α β : Type} : α × β → β × α := by
    intro p; cases p; constructor <;> assumption
  def swap_sum  {α β : Type} : α ⊕ β → β ⊕ α := by
    intro p; cases p <;> try (constructor ; assumption)
    apply Sum.inr ; assumption

  -- Here's `Nat`-induction.
  example (p : Nat → Prop) (h₀ : p 0) (h_ind : ∀ n : Nat, p (n.succ)) : ∀ n, p n := by
    intro n; cases n <;> first | assumption | apply h_ind -- `try assumption` gets rid of the trivial `p 0` proof; `try apply h_ind` gets rid off the `p (n† + 1)` proof, with the argument `h_ind n†` autofilled by Lean

  -- NOTE: The `contradiction` tactic finds hypotheses that lead to a contradiction, thereafter exploding to prove whatever
  example (p q : Prop) : p ∧ ¬ p → q := by
    intro h; cases h; contradiction -- contradiction from applying `¬ p  :=  p → False` to the `p`

  -- NOTE: `match` is like `cases`, but instead of introducing goals, it expects solutions to them outright. I'm not gonna belabour this.
  -- You can anonymous-pattern-match on an `intro`:
  example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
    constructor
    case mp =>
      intro
      | ⟨hp, Or.inl hq⟩ => apply Or.inl; apply And.intro (by assumption) (by assumption)
      | ⟨_ , Or.inr _ ⟩ => apply Or.inr $ And.intro ‹p› ‹r›
    case mpr =>
      intro
      | Or.inl ⟨_, _⟩ => constructor; apply ‹p› ; apply Or.inl; apply ‹q›
      | Or.inr ⟨_, _⟩ => constructor; assumption; apply Or.inr; assumption
end moar



/- SECTION: Structuring Tactic Proofs -/
section structuring
  -- NOTE: `have` works exactly the same way when in tactics blocks
  example
    (p q r : Prop)
    : p ∧ (q ∨ r)
    → (p ∧ q) ∨ (p ∧ r)
    := by
      intro h
      have h_p : p := h.left
      have h_qvr : q ∨ r := h.right
      exact
        h_qvr.elim
          (fun h_q => Or.inl ⟨h_p, h_q⟩)
          (fun h_r => Or.inr $ show p ∧ r by constructor <;> assumption)
  -- Another example
  example
    (p q r : Prop)
    : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)
    := by
      constructor
      case mp =>
        intro ⟨h_p, h_qvr⟩
        cases h_qvr with
        | inl h_q => apply Or.inl ; constructor <;> assumption
        | inr h_r => apply Or.inr ; constructor <;> assumption
      case mpr =>
        intro h; cases h with
        | inl hl => exact ⟨hl.left, .inl hl.right⟩
        | inr hr => exact ⟨hr.left, .inr hr.right⟩

  -- NOTE: `show t` declares that we're trying to exhibit a term of the type `t`.
  --       You can use this to rewrite the current goal as something definitionally
  --        equivalent, or you can just use it to make the proof easier to read.
  example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
    constructor
    case mp =>
      intro ⟨h_p, h_qvr⟩
      cases h_qvr
      · apply Or.inl
        show p ∧ q
        constructor <;> assumption
      · apply Or.inr
        show p ∧ r
        constructor <;> assumption
    case mpr =>
      intro h
      cases h
      case inl h_pxq =>
        constructor
        · exact h_pxq.left
        · exact Or.inl h_pxq.right
      case inr h_pxr =>
        constructor
        · exact h_pxr.left
        · exact Or.inr h_pxr.right
  -- Here's a definitionally equivalent rewrite:
  example (n : Nat) : n + 1 = Nat.succ n := by
    show Nat.succ n = Nat.succ n
    rfl

  -- NOTE: `have` does what you think it does.
  example (p : Prop) : p ∧ q → p ∧ p := by
    intro h_pxq
    have : p := h_pxq.left -- you can even anonymise! The default label is `this` :)
    constructor <;> assumption
  -- You don't even need typing
  example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
    intro ⟨h_p, h_qvr⟩
    cases h_qvr with
    | inl h_q =>
      have := And.intro h_p h_q
      apply Or.inl ; exact this
    | inr h_r =>
      have := And.intro h_p h_r
      apply Or.inr ; assumption -- no names!

  -- NOTE: `let` tactic does what you think it does, but the definition can be unfolded in the proof
  example : ∃ x, x + 2 = 8 := by
    let a : Nat := 3 * 2
    exists a
  -- If we use `have` instead of `let` in the previous example, Lean can't use the definition of `a` to auto-prove that `a + 2 = 8`
  /-
  example : ∃ x, x + 2 = 8 := by
    have a : Nat := 3 * 2
    exists a
    -- Outstanding goal: *`a : Nat ⊢ a + 2 = 8`*
    -- The proof is now impossible T-T
  -/

  -- NOTE: You can use `·` or `{ ... }` to focus on sub-goals.
  example (p q : Prop) : p ∨ q → (p ∧ p) ∨ (q ∧ q) := by
    intro h; cases h; {
      apply Or.inl
      constructor <;> assumption
    } ; { -- whack-ass spacing
    apply Or.inr ;
    constructor <;> assumption
    }
end structuring



/- SECTION: Combinators -/
section combinators
  -- shitpost
end combinators
