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
  -- NOTE: `;`
  example (p q : Prop) (h_p : p) : p ∨ q := by
    apply Or.inl ; assumption

  -- NOTE: `<;>`
  example (p q : Prop) (h_p : p) (h_q : q) : p ∧ q := by
    constructor <;> assumption

  -- NOTE: `first | ⋯ | ⋯`
  example (p q : Prop) (hp : p) : p ∨ q := by
    first | apply Or.inl; assumption | apply Or.inr; assumption
  example (p q : Prop) (hq : q) : p ∨ q := by
    first | apply Or.inl; assumption | apply Or.inr; assumption

  -- NOTE: `try ⋯` *always succeeds*
  example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
    constructor           -- `⊢ p` and `⊢ q ∧ r`
    <;> (try constructor) -- `⊢ p` and `⊢ q` and `⊢ r`
    <;> assumption        -- no remaining goals
  -- Be careful with `repeat`...
  /-
  `example : True := by      `
  `  repeat (try assumption) `-- maximum recursion depth exceeded...!
  -/

  -- NOTE: `all_goals t` does what it says it does, and succeeds just when `t` succeeds on all of the goals
  example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
    constructor
    all_goals (try constructor)
    all_goals assumption

  -- NOTE: `any_goals t` tries `t` on all goals, and succeeds just when `t` succeeds on *some* goal
  example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
    constructor
    any_goals constructor
    all_goals assumption
  -- This is really helpful...!
  example
    {p q r : Prop}
    (hp : p) (hq : q) (hr : r)
    : p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
      repeat (any_goals constructor)
      all_goals assumption
end combinators



/- SECTION: `rewrite` (aka `rw`) -/
section rewriting
  -- NOTE: `rw`
  example (f : Nat → Nat) (k : Nat) (h₀ : f 0 = 0) (h_k : k = 0) : f k = 0 := by
    rw [h_k]
    rw [h₀]
  example (f : Nat → Nat) (k : Nat) (h_0 : f 0 = 0) (h_k : k = 0) : f k = 0 := by
    rw [h_k, h_0] -- syntactic sugar for the above
  -- `rw ⋯ at ⋯` is a rewrite of a particular hypothesis in the known list of hypotheses.
  example (f : Nat → Nat) (a : Nat) (h : a + 0 = 0) : f a = f 0 := by
    -- *`h : a + 0 = 0`*
    rw [Nat.add_zero] at h
    -- *`h : a = 0`*
    rw [h]

  -- `rw` isn't limited to propositions
  def Tuple (α : Type) (n : Nat) := { as : List α // as.length = n }
  example (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
    rw [h] at t
    exact t
end rewriting



/- SECTION: `simp` -/
section the_simp
  -- NOTE: `simp` applies lots of rewrites, and combines them with other known rules to try and simplify terms
  example (x y z : Nat) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
    simp
  example
    (x y z : Nat) (p : Nat → Prop)
    (h : p (x * y))
    : p ((x + 0) * (0 + y * 1 + z * 0))
    := by
      -- *`⊢ p ((x + 0) * (0 + y * 1 + z * 0))`*
      simp
      -- *`⊢ p (x * y)`*
      assumption

  -- Some examples with lists
  open List in
  example (xs : List Nat) : reverse (xs ++ [1, 2, 3]) == [3, 2, 1] ++ reverse xs := by
    simp
  open List in
  example (xs ys : List α) : length (reverse (xs ++ ys)) = length xs + length ys := by
    simp -- *`⊢ ys.length + xs.length = xs.length + ys.length`*
    rw [Nat.add_comm] -- this could've been a `simp` call

  -- `simp` can take a list of arguments just like `rw` does
  open List in
  example (xs ys : List α) : length (reverse (xs ++ ys)) = length xs + length ys := by
    simp [Nat.add_comm] -- Use all `@[simp]` rules and use `Nat.add_comm` while simplifying

  -- You can use the keyword `at` to simplify on some assumption
  example
    (x y z : Nat) (p : Nat → Prop)
    (h : p ((x + 0) * (0 + y * 1 + z * 0)))
    : p (x * y) := by
      -- *`(h : p ((x + 0) * (0 + y * 1 + z * 0))) ⊢ p (x * y)`*
      simp at h
      -- *`(h : p (x * y)) ⊢ p (x * y)`*
      assumption
  -- If you want to try simplifying all hypotheses and the goal, you can `simp ⋯ at *`
  section at_example
    -- For the remainder of the section (*`local`*), add `attribute simp` to `Nat.mul_comm` etc.
    attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm
    attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm
    --
    example
      (w x y z : Nat) (p : Nat → Prop)
      (h : p (x * y + z * w * x))
      : p (x * w * z + y * x)
      := by
        -- *`h : p (x * y  + z * w * x)`*
        -- *`⊢   p (x * w * z  +  y * x)`*
        simp at *
        -- *`h : p (x * y  +  w * (x * z))`*    NOTE: `simp` put the inside expression here into a *canonical form*
        -- *`⊢   p (x * y  +  w * (x * z))`*    NOTE: `simp` put the inside expression here into the *same* canonical form
        assumption
    --
    example
      (x y z : Nat) (p : Nat → Prop)
      (h_xy : p (1 * x + y))
      (h_xz : p (x * z * 1))
      : p (y + 0 + x) ∧ p (z * x)
      := by
        -- *`h_xy : p (1 * x  +  y)`*
        -- *`h_xz : p (x * z * 1)`*
        -- *`⊢ p (y + 0 + x)  ∧  p (z * x)`*
        simp at *
        -- *`h_xy : p (x + y)`*, in canonical form
        -- *`h_xz : p (x * z)`*, in canonical form
        -- *`⊢ p (x + y)  ∧  p (x * z)`*, in canonical form
        ; constructor   -- Goals *`⊢ p (x + y)`* and *`⊢ p (x * z)`*
        <;> assumption  -- Both goals are already known
  end at_example

  -- `simp` recognises the `←⋯` syntax just like `rw`
  section left_example
    def f (m n : Nat) : Nat := m + n + m
    -- The definition of `f` is a fact, so it may be used in the following
    example
      {m n : Nat}
      (h_ne1 : n = 1)
      (h_0em : 0 = m)
      : f m n = n
      := by
        simp [h_ne1, ←h_0em, f] -- The `←` on `←h_0em` is necessary because rewrites are done in the direction *left-replaced-by-right*
  end left_example

  -- To use all local hypotheses while `simp`lifying, pass `[*]` as an argument
  example
    (f : Nat → Nat)
    (k : Nat)
    (h_f0_e_0 : f 0 = 0)
    (h_k_e_0  : k   = 0)
    : f k = 0
    := by
      simp [*] -- same as `simp [h_f0_e_0, h_k_e_0]`
  -- You can pass additional stuff too
  example
    (u w x y z : Nat)
    (_ : x = y + z)
    (_ : w = u + x)
    : w = z + y + u
    := by
      simp [*, Nat.add_assoc, Nat.add_comm]

  -- `simp` is also set up to do propositional rewriting, including replacing terms by `true`.
  def propositonal_0 (p q : Prop) (_ : p) : p ∧ q ↔ q := by
    simp [*]
  #print propositonal_0
  def propositional_1 (p q : Prop) (_ : p) : p ∨ q := by
    simp [*]  -- Automatically introduces the constructor `Or.inl`
  #print propositional_1
  def propositional_2 (p q r : Prop) (h_p : p) (h_q : q) : p ∧ (q ∨ r) := by
    simp [*]
  #print propositional_2
  #print eq_true

  example
    (_ _ x x' y y' _ : Nat) (_ : Nat → Prop)
    (h_x : x + 0 = x')
    (h_y : y + 0 = y')
    : x + y + 0 = x' + y'
    := by
      simp at *
      simp [*]

  -- NOTE: The more the `simp`lifier knows about your current project, the more powerful it becomes.
  section da_powa
    def mk_symm {α : Type} (xs : List α) := xs ++ xs.reverse

    theorem reverse_mk_symm
      {α : Type}
      (xs : List α)
      : (mk_symm xs).reverse = mk_symm xs
      := by
        simp [mk_symm]
    #print reverse_mk_symm

    example
      (xs ys : List Nat)
      : (xs ++ mk_symm ys).reverse == mk_symm ys ++ xs.reverse
      := by
        simp [reverse_mk_symm]
    example
      (xs ys : List Nat)
      (p : List Nat → Prop)
      (h : p (xs ++ mk_symm ys).reverse)
      : p (mk_symm ys ++ xs.reverse)
      := by
        simp [reverse_mk_symm] at h
        assumption

    -- Since `reverse_mk_symm` is usually the right thing to do when `simp`ing, we can instruct `simp` to always do so
    -- The `local` part here says to only do so *within* the current `section`.
    attribute [local simp] reverse_mk_symm -- Could instead have `@[simp] theorem reverse_mk_symm ⋯` upon definition

    example
      (xs ys : List Nat)
      : (xs ++ mk_symm ys).reverse == mk_symm ys ++ xs.reverse
      := by
        simp
    example
      (xs ys : List Nat)
      (p : List Nat → Prop)
      (h : p (xs ++ mk_symm ys).reverse)
      : p (mk_symm ys ++ xs.reverse)
      := by
        simp at h
        assumption

    -- `simp only` and `-` do what you think they do
    theorem gamer0
      (xs ys : List Nat) (p : List Nat → Prop)
      (h : p (xs ++ mk_symm ys).reverse)
      : p (mk_symm ys ++ xs.reverse)
      := by
        simp at h; assumption
    #print gamer0 -- Uses `reverse_mk_symm`

    theorem gamer1
      (xs ys : List Nat) (p : List Nat → Prop)
      (h : p (xs ++ mk_symm ys).reverse)
      : p ((mk_symm ys).reverse ++ xs.reverse)
      := by
        simp [-reverse_mk_symm] at h; assumption
    #print gamer1 -- No reference to `reverse_mk_symm`

    theorem gamer2
      (xs ys : List Nat) (p : List Nat → Prop)
      (h : p (xs ++ mk_symm ys).reverse)
      : p ((mk_symm ys).reverse ++ xs.reverse)
      := by
        simp only [List.reverse_append] at h; assumption
    #print gamer2 -- Only uses the `List.reverse_append` rule in addition to `rewrite`ing functionality
  end da_powa

  -- NOTE: Contextual simplifications use facts in the known context to solve goals
  -- Here, this is uses the contextual fact that `x = 0` on the inside of then `then` block
  theorem sugoma0 : if x = 0 then y + x = y else x ≠ 0 := by
    simp (config := { contextual := true })
  #print sugoma0 -- Refernces `Eq.refl (x = 0)`; i.e. is indeed utilising the fact that `x = 0` in the `then` block
  -- Here, this uses the contextual fact `h : x = 0` in the body of the `∀` abstraction
  set_option linter.unusedVariables false
  theorem sugoma1 : ∀ (x : Nat) (h : x = 0), y + x = y := by
    simp (config := { contextual := true })
  set_option linter.unusedVariables true
  #print sugoma1 -- References `h`; i.e. is indeed using the context-known `h : x = 0` in the conclusion

  -- NOTE: Arithmetical simplifications use arithmetic laws lol
  def funny {x y : Nat} : 0 < 1 + x  ∧  x + y + 2 ≥ y + 1 := by
    -- Just applying `simp` doesn't cut it here
    simp (config := { arith := true }) -- This uses arithmetic facts too, like `Nat.Linear.ExprCnstr.eq_true_of_isValid`, whatever that is!
  #print funny
  -- `simp_arith` is shorthand for `simp (config := { arith := true })`
  example {x y : Nat} : 0 < 1 + x  ∧  x + y + 2 ≥ y + 1 := by
    simp_arith
end the_simp



/- SECTION: `split` -/
section the_split
  def f' (x y z : Nat) : Nat :=
    match x, y, z with
    | 5, _, _ => y
    | _, 5, _ => y
    | _, _, 5 => y
    | _, _, _ => 1

  -- `split` breaks apart functions/expressions that depend on different cases.
  example (x y z w : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f' x y w = 1 := by
    intros      -- Throw in assumptions
    simp [f']   -- Unfold definition of `f'`
    split       -- Break apart the `match` expression
    <;> try contradiction -- most of the cases pattern match `x ≠ 5` (etc.) against `5`, resulting in an assumption `: 5 ≠ 5`
    rfl         -- The remaining thing to show is `: 1 = 1`

  def g (xs ys : List Nat) : Nat :=
    match xs, ys with
    | [a, b], _       => a + b + 1
    | _,      [b, _]  => b + 1
    | _,      _       => 1

  -- Can narrow `split` into a particular hypothesis
  example (xs ys : List Nat) (h : g xs ys = 0) : False := by
    simp [g] at h     -- Unfold the definition of `g` at the assumption `h`
    split at h        -- Split into cases depending on the behaviour of `h`
    <;> contradiction -- Find contradictions using arithmetic rules
end the_split



/- SECTION: Make-your-own tactic! -/
section byo
  -- Define a new tactic called `triv`
  syntax "triv" : tactic
  -- Uses of `triv` invoke `assumption`
  macro_rules
  | `(tactic| triv) => `(tactic| assumption)

  example (_ : p) : p := by triv

  -- Uses of `triv` now invoke the previous lot of stuff that `triv` tries (i.e. just `assumption`), and also `rfl`
  macro_rules
  | `(tactic| triv) => `(tactic| rfl)

  example {α : Type} (x : α) : x = x := by triv
  example (x : α) (h : p) : x = x  ∧  p := by constructor <;> triv

  -- Recursively extend `triv`
  macro_rules | `(tactic| triv) => `(tactic| constructor <;> triv)

  example (x : α) (h : p) : x = x  ∧  p := by triv
end byo



/- EXERCISES: (2) Sweet -/
section ex_2
  def the_ex_2
    (p q r : Prop)
    (h_p : p)
    : (p ∨ q ∨ r)
    ∧ (q ∨ p ∨ r)
    ∧ (q ∨ r ∨ p)
    := by
      (apply And.intro <;> try apply And.intro) <;> first | (apply Or.inl ; assumption) | (apply Or.inr ∘ Or.inl ; assumption) | (apply Or.inr ∘ Or.inr ; assumption)
  #print the_ex_2
end ex_2



/- EXERCISES: (1) -/
section ex_1_ch_2_first
  variable (p q r : Prop)

  -- commutativity of ∧ and ∨
  example : p ∧ q ↔ q ∧ p := by
    constructor
    <;> (simp ; intros ; constructor ; repeat assumption)
  example : p ∨ q ↔ q ∨ p := by
    constructor
    <;> intros h
    <;> (first | simp [Or.comm] | simp [Or.comm] at h)
    <;> assumption
  -- associativity of ∧ and ∨
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
    constructor
    case mp =>
      intro
      | ⟨⟨hp, hq⟩, hr⟩ =>
        constructor <;> try constructor
        all_goals assumption
    case mpr =>
      intro
      | ⟨hp, ⟨hq, hr⟩⟩ =>
        constructor <;> try constructor
        all_goals assumption
  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
    constructor
    case mp =>
      intros h
      cases h with
      | inl h' =>
        cases h'
        · apply Or.inl ; assumption
        · apply Or.inr ; apply Or.inl ; assumption
      | inr h' =>
        apply Or.inr ∘ Or.inr ; assumption
    case mpr =>
      intros h
      cases h with
      | inl h' =>
        apply Or.inl ∘ Or.inl ; assumption
      | inr h' =>
        cases h' with
        | inl => apply Or.inl ; apply Or.inr ; assumption
        | inr => apply Or.inr ; assumption
  -- distributivity
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
    constructor
    case mp =>
      intro h ; match h with
      | ⟨h_p, h_qvr⟩ =>
      cases h_qvr <;> first | apply Or.inl ; (constructor <;> assumption) | apply Or.inr ; (constructor <;> assumption)
    case mpr =>
      intro h
      constructor
      · cases h
        <;> (rename_i h' ; exact h'.left)
      · cases h
        <;> first
          | apply Or.inl ; rename_i h' ; exact h'.right
          | apply Or.inr ; rename_i h' ; exact h'.right

  -- NOTE: I just don't have the motivation to do more of these...

  -- example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by

  -- -- other properties
  -- example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
  -- example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
  -- example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
  -- example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
  -- example : ¬(p ∧ ¬p) := sorry
  -- example : p ∧ ¬q → ¬(p → q) := sorry
  -- example : ¬p → (p → q) := sorry
  -- example : (¬p ∨ q) → (p → q) := sorry
  -- example : p ∨ False ↔ p := sorry
  -- example : p ∧ False ↔ False := sorry
  -- example : (p → q) → (¬q → ¬p) := sorry
end ex_1_ch_2_first



/- EXERCISES: (1) ch_3 -/
section ex_1_ch_3_ex_1
  variable (α : Type) (p q : α → Prop)

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
    constructor
    case mp =>
      intro h
      constructor <;> intros x
      · exact And.left  $ h x
      · exact And.right $ h x
    case mpr =>
      intro ; intro
      constructor <;> simp [*]
  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
    intros
    simp [*]
  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
    intro h
    cases h <;> intro <;> simp [*]
end ex_1_ch_3_ex_1
