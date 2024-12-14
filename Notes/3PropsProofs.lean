/- @file Notes/3PropsProofs.lean
 - @src https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html
 -/

/- SECTION: Propositions as Types -/
section propositions_as_types
  -- We add a type, called `Prop := Sort 0`, to capture *statements*.
  -- NOTE: For `p : Prop`, **any two terms of `p` are considered equal**.

  -- To build up more statements, we need logical connectives
  #check (· ∧ ·)                        -- *`: Prop → Prop → Prop`*
  #check (· ∨ ·)                        -- *`: Prop → Prop → Prop`*
  #check (¬ ·)                          -- *`: Prop → Prop`*
  #check ((· → ·) : Prop → Prop → Prop) -- *`: Prop → Prop → Prop`*

  -- We *could* then add, for each `p : Prop`, a type `Proof p` whose terms are proofs of `p`.
  -- *But this is redundant* -- we could just encode `p` itself such that the terms of `p` are
  --  the proofs of `p`.
  -- There are two competing views:
  --    Constructivists would say that *a statement `p` is a data type specifying the data*
  --     *needed to prove it*, and a proof of `p` is exactly something that typechecks as `: p`.
  --    Literally anyone else would say that what we're doing here is a trick of *encoding* --
  --     our types are just encodings of statements, encoded such that they have a term iff
  --     the associated statement is true.
  --    We'll apply either view as we see fit throughout the book.
end propositions_as_types



/- SECTION: Theorems -/
section theorems
  variable {p q : Prop} -- When needed for relevant polymorphism, these become implicit arguments

  theorem stupid1 : p → q → p :=
    fun hp => fun _ => hp
  #check stupid1
  #print stupid1

  theorem stupid2 : p → q → p :=
    fun hp : p =>
    fun _  : q =>
    show p from hp  -- This is a fancy way of just writing `hp`. It makes it a bit more readable ig.
  #check stupid2
  #print stupid2

  theorem stupid3 (hp : p) (_ : q) : p :=    -- btw, our naming convention `hp : p` is short for "`h`ypothesis of `p` being true"
    hp

  axiom hp : p -- This just magics up a term `hp : p`. We can't *compute* with it.
  theorem dumb1 : q → p := fun _ => show p from hp
  #check dumb1  -- different type to `stupid1`!
  #print dumb1

  theorem stupid4 : ∀ {p q : Prop}, p → q → p :=    -- `∀ ~ , ~~` is a fancy way of writing a dependent function type `~ → ~~`.
    fun {p q : Prop} (hp : p) (_ : q) => hp
  #check stupid4
  #print stupid4

  theorem implies_transitive
    {p q r : Prop}
    (h₀ : q → r) (h₁ : p → q)
    : p → r
    :=
      fun (hp : p) =>
      h₀ (h₁ hp)
end theorems



/- SECTION: Propositional Logic -/

section propositional_logic
  variable (p q : Prop)

  section conjunction
    #print And

    -- Introduction rule
    #check @And.intro -- *`: ∀ {a b : Prop}, a → b → a ∧ b`*
    example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

    -- Elimination rules
    #check @And.left  -- *`: ∀ {a b : Prop}, a ∧ b → a`*
    #check @And.right -- *`: ∀ {a b : Prop}, a ∧ b → b`*
    example (hpq : p ∧ q) : q ∧ p :=
      And.intro
        hpq.right
        hpq.left

    -- The constructor `And.intro` is a *constructor* for a `structure`, so it can be used with `⟨anonymous, constructor, notation⟩`
    def shitpost (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩
    #print shitpost

    -- Nested constructors that right-associate can be flattened. So,
    example (h : p ∧ q) : q ∧ p ∧ q :=  -- `q ∧ p ∧ q := q ∧ (p ∧ q)`
      ⟨h.right, h.left, h.right⟩        -- desugars to `⟨h.right, ⟨h.left, h.right⟩⟩`
  end conjunction

  section disjunction
    #print Or
    #print Or.inl -- *`: ∀ {a b : Prop}, a → a ∨ b`*
    #print Or.inr -- *`: ∀ {a b : Prop}, b → a ∨ b`*

    -- Introduction rules
    #print Or.intro_left  -- *`: ∀ {a b : Prop}, a → a ∨ b`*, longhand for `Or.inl`
    #print Or.intro_right -- *`: ∀ {a b : Prop}, b → a ∨ b`*, longhand for `Or.inr`

    -- Elimination rule
    #print Or.elim  -- *`: ∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c`*; the **universal property**.

    example (h : p ∨ q) : q ∨ p :=
      h.elim
        (Or.intro_right _)  -- Could replace with `Or.inl`, which takes the `_` and makes it implicit.
        (Or.intro_left  _)  -- ^^likewise
  end disjunction

  section negation
    #print False
    #print Not    -- *`Not : Prop → Prop := fun a => (a → False)`*

    def modus_tollens : (p → q)  →  ¬ q  →  ¬ p :=
      fun hp2q =>
      fun hnq  =>
        hnq ∘ hp2q

    -- (No introduction rules for `False`)
    -- Elimination rule for `False`
    #print False.elim -- *`: {a : Prop} → False → a`*, the **principle of explosion**, or **universal property of the initial object**
    -- Often used in this form:
    example (hp : p) (hnp : ¬ p) : q := False.elim (hnp hp)
    -- which has the shortcut
    #check @absurd -- *`: {a b : Prop} → a → ¬a → b`*
    example (hp : p) (hnp : ¬ p) : q := absurd hp hnp

    -- NOTE: Dually to `False`, `True ≃ 1` has a single introduction rule, `True.intro : True`; this is ofc the **universal property of the terminal object**.
  end negation

  section logical_equivalence
    #print Iff  -- exactly what you think it'd be

    -- Introduction rule
    #print Iff.intro  -- *`: ∀ {a b : Prop}, (a → b) → (b → a) → (a ↔ b)`*

    -- Elimination rules
    #print Iff.mp     -- *`: ∀ {a b : Prop}, (a ↔ b) → a → b`*; this is `m`odus `p`onens
    #print Iff.mpr    -- *`: ∀ {a b : Prop}, (a ↔ b) → b → a`*; this is `m`odus `p`onens in `r`everse.

    theorem and_swap : p ∧ q  ↔  q ∧ p :=
      Iff.intro -- can be replaced by `⟨⋯, ⋯⟩`.
        (fun hpq =>
          show q ∧ p from And.intro hpq.right hpq.left)
        (fun hqp =>
          And.intro hqp.right hqp.left)
  end logical_equivalence
end propositional_logic



/- SECTION: Introducing Auxiliary Subgoals -/
section aux_subgoals
  variable (p q : Prop)

  -- The `have` construct is pretty much a `let`.
  example (h : p ∧ q) : q ∧ p :=
    have hq : q := h.right
    have hp : p := h.left
    show q ∧ p from ⟨hq, hp⟩

  -- The `suffices` construct moddles the "it suffices to show" style of argument in normal math.
  example (h : p ∧ q) : q ∧ p :=
    have hq : q := h.right
    suffices hp : p from ⟨hq, hp⟩ -- `suffices a : α from e ; f` takes `e : α → currentGoal` and `f : α` and produces a term of type `currentGoal`.
    show p from h.left
end aux_subgoals
