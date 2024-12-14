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



/- SECTION: Classical Logic -/
section classical_logic
  variable {p q : Prop}

  #check Classical.em -- Law of the `e`xcluded `m`iddle.

  theorem Classical.dne (h : ¬¬p) : p :=  -- `d`ouble `n`egation `e`limination
    have h' : ((p → False) → False) := h
    have h_p_v_np : p ∨ ¬p := Classical.em p
    suffices h_np_2_p : (p → False) → p
    from
      Or.elim h_p_v_np
        id
        h_np_2_p
    ; fun p_2_false =>
        have bad : False := h' p_2_false
        bad.elim
  -- Cleaning up a bit...
  theorem Classical.dne' (h : ¬¬p) : p :=
    have h_p_v_np : p ∨ ¬p := Classical.em p
    h_p_v_np.elim
      id
      (absurd · h)

  -- EXERCISE: Prove `Classical.em` without using any of `Classical`, and assuming only `Classical.dne : ¬¬p → p`.
  theorem Classical.em' : p ∨ ¬p :=
    suffices h_n_n__p_v_np : ((p ∨ ¬p) → False) → False from Classical.dne h_n_n__p_v_np
    fun h_p_v_np__2_f : ((p ∨ ¬p) → False) => -- By universal property of the coproduct, this gives rise to functions `p → False` and `¬p → False`...
    have h_p_2_f  : p  → False          := h_p_v_np__2_f ∘ Or.inl -- this is one
    have h_np_2_f : (p → False) → False := h_p_v_np__2_f ∘ Or.inr -- and this is the other
    have h_nnp    : ¬¬p                 := h_np_2_f               -- the latter *is* a `¬¬p`
    have h_p      : p                   := Classical.dne h_nnp    -- but that's enough to get a `p`
    show False from h_p_2_f h_p                                   -- and ofc, the former produces a `False` from a `p`, which gives us the desired `False`.
  -- "Cleaned up"...
  theorem Classical.em'' : p ∨ ¬p :=
    Classical.dne $
      fun h_p_v_np__2_f =>
      (h_p_v_np__2_f ∘ Or.inl) (Classical.dne $ h_p_v_np__2_f ∘ Or.inr)

  -- Classical logic also allows a proof by cases
  #check @Classical.byCases  -- *`: ∀ {p q : Prop} , (p → q) → (¬p → q) → q`*
  theorem Classical.byCases' (h_p2q : p → q) (h_np2q : ¬p → q) : q :=
    (Classical.em p).elim
      h_p2q
      h_np2q
  example (h : ¬¬p) : p :=
    Classical.byCases
      (fun h_p  : p  => h_p)
      (fun h_np : ¬p => absurd h_np h)

  -- Classical logic furthermore enables a proof by contradiction
  #check @Classical.byContradiction --*`: ∀ {p : Prop}, (¬p → False) → p`*
  theorem Classical.byContradiction' (h_np_2_f : ¬p → False) : p :=
    (Classical.em p).elim     -- We have `p ∨ ¬p`. To produce `p`, notice that...
      id                      --  if we had `p`, then by doing nothing, we have `p`;
      (False.elim ∘ h_np_2_f) --  else if we had `¬p`, then we can attain `False` and explode to get `p`.
  example (h : ¬¬p) : p :=
    Classical.byContradiction h

  -- Here's one more example of needing classical logic.
  open Classical in
  example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
    -- Knowing that `¬(p ∧ q)` isn't enough to tell us any constructive information on *which* of them isn't true.
    -- So, we dip into the non-constructivism, and branch on whether or not `p` is true (could also do `q`, obviously)
    have h_p__2__np_v_nq  : p  → ¬p ∨ ¬q :=
      fun h_p =>
        byCases (p := q)
          (fun h_q => absurd ⟨h_p, h_q⟩ h)
          Or.inr
    ;
    have h_np__2__np_v_nq : ¬p → ¬p ∨ ¬q :=
      Or.inl
    ;
    byCases (p := p)
      h_p__2__np_v_nq
      h_np__2__np_v_nq
  -- The book proves it this way instead, which uses one less `Classical.em` than I do.
  open Classical in
  example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
    Or.elim (em p)
      (fun hp : p =>
        Or.inr
          (show ¬q from
            fun hq : q =>
            h ⟨hp, hq⟩))
      (fun hp : ¬p =>
        Or.inl hp)
end classical_logic



/- SECTION: Examples of Propositional Validities -/
section stuff_in_lean_stdlib_already
  #check And.comm
  #check Or.comm
  -- and there's more...
end stuff_in_lean_stdlib_already



/- EXERCISES: No classical reasoning required -/
section exercises_no_class
  variable {p q r : Prop}

  -- EXERCISE: ∧ distributes over ∨
  example : p ∧ (q ∨ r)  ↔  (p ∧ q) ∨ (p ∧ r) :=
    -- (←)
    have left  : (p ∧ q) ∨ (p ∧ r)  →  p ∧ (q ∨ r) :=
      fun h =>
        h.elim
          (fun hpq => ⟨hpq.left, Or.inl hpq.right⟩)
          (fun hpr => ⟨hpr.left, Or.inr hpr.right⟩)
    ;
    -- (→)
    have right : p ∧ (q ∨ r)        →  (p ∧ q) ∨ (p ∧ r) :=
      fun h =>
        h.right.elim
          (fun hq => Or.inl ⟨h.left , hq⟩)
          (fun hr => Or.inr ⟨h.left, hr⟩)
    ;
    -- (↔)
    Iff.intro
      right
      left
end exercises_no_class



/- EXERCISES: Requires classical reasoning -/
section classy_exercises
  open Classical

  -- EXERCISE: funny
  example : ¬(p ∧ ¬q) → p → q :=
    fun h_n_p_and_nq =>
    fun h_p =>
    byContradiction
      (fun h_nq => h_n_p_and_nq ⟨h_p, h_nq⟩)
end classy_exercises
