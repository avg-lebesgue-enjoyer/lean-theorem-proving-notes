/- @file Notes/4QuantifiersEquality.lean
 - @src https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html
 -/

/- SECTION: ∀ -/
section universal_quantifier
  -- We can encode `∀ x : α, p x` by the dependent function type `(x : α) → p x`. This is obvious if you think for a couple of seconds about it.
  -- Introduction rule is lambda abstraction; Elimination rule is application.
  example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
    fun h : (∀ x : α, p x ∧ q x) =>
    fun y : α =>  -- introduction rule used in `fun y : α => ⋯`
    (h y).left    -- elimination rule used in application `h y`
end universal_quantifier



/- SECTION: = -/
section equality
  #print Eq
  /-
    *`inductive Eq.{u_1} : {α : Sort u_1} → α → α → Prop`*
    *`number of parameters: 2`*
    *`constructors:`*
    *`Eq.refl : ∀ {α : Sort u_1} (a : α), a = a`*             -- Equality is the *freely generated reflexive relation*.
  -/

  #check @Eq.symm  -- *`: ∀ {α : Sort u_1} {a b : α}, a = b  →  b = a`*
  theorem Eq.symm'.{u} {α : Sort u} {a b : α} (h : a = b) : b = a :=
    match h with
    | .refl _ =>  -- The `_` here is doing some pretty heavy lifting.
      Eq.refl a   -- The unification it instructs Lean to do is enough to deduce that `a` and `b` are *identical* terms (of type `α`),
                  --  whence the goal `⊢ b = a` becomes simply `⊢ a = a`.

  #check @Eq.trans  -- *`: ∀ {α : Sort u_1} {a b c : α}, a = b  →  b = c  →  a = c`*
  theorem Eq.trans'.{u} {α : Sort u} {a b c : α} (h₀ : a = b) (h₁ : b = c) : a = c :=
    match h₀, h₁ with | .refl _, .refl _ => rfl -- `rfl` is short for `Eq.refl _`.

  #check @Eq.subst  -- *`: ∀ {α : Sort u} {p : α → Prop} {a b : α}, a = b  →  p a  →  p b`*
  theorem Eq.subst'.{u} {α : Sort u} {p : α → Prop} {a b : α} (h_ab : a = b) (h_pa : p a) : p b :=
    match h_ab with | .refl _ => h_pa

  -- These are the four properties that characterise equality:
  #check @Eq.refl   -- Reflexive
  #check @Eq.symm   -- Symmetric
  #check @Eq.trans  -- Transitive
  #check @Eq.subst  -- Trivial quotients

  example
    {α : Type} {a b c d : α}
    (h_ab : a = b) (h_cb : c = b) (h_cd : c = d)
    : a = d :=
      Eq.trans (Eq.trans h_ab (Eq.symm h_cb)) h_cd

  -- Because terms can *compute* in dependent type theory, reflexivity is *really* powerful.
  example : 2 + 3 = 5 := rfl

  -- NOTE: `▸` is infix shorthand for a slightly beefier `Eq.subst`.
  example
    (α : Type) (a b : α) (p : α → Prop)
    (h_ab : a = b) (h_pa : p a)
    : p b :=
      h_ab ▸ h_pa -- "use `a = b` to `▸`substitute in `p a`"

  #check @congrArg  -- *`: ∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β),  a₁ = a₂  →  f a₁ = f a₂`*
  #check @congrFun  -- *`: ∀ {α : Sort u} {β : Sort v} {f g : (x : α) → β x},  f = g  →  ∀ (a : α), f a = g a`*
  #check @congr     -- *`: ∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂  →  a₁ = a₂  →  f₁ a₁ = f₂ a₂`*

  -- Example of working with equality, particularly with `▸`.
  example (x y : Nat) :
    (x + y) * (x + y)
    = x * x  +  y * x  +  x * y  +  y * y
    :=
      have a : (x + y) * (x + y) = (x + y) * x  +  (x + y) * y
            := Nat.mul_add (x + y) x y
      have b : (x + y) * x = x * x  +  y * x
            := Nat.add_mul x y x
      have c : (x + y) * y = x * y  +  y * y
            := Nat.add_mul x y y
      have d : x * x + y * x + (x * y + y * y) = x * x + y * x + x * y + y * y
            := Nat.add_assoc (x * x + y * x) (x * y) (y * y) ▸ rfl
      a ▸ b ▸ b ▸ c ▸ d ▸ rfl
      -- NOTE: This shit is exactly what `calc` is meant to streamline, and what the `rw` and `simp` tactics are meant to automate.
      -- (it was cool to do it once though)
end equality



/- SECTION: `calc` -/
section the_calc_feature
  -- `calc` is really nice syntax for relations brought together transitively.
  theorem gamer
    (a b c d e : Nat)
    (hab : a = b)
    (hbc : b = c + 1)
    (hcd : c = d)
    (hed : e = 1 + d)
    : a = e :=
    calc a
      _ = b     := hab
      _ = c + 1 := hbc
      _ = d + 1 := congrArg (· + 1) hcd
      _ = 1 + d := Nat.add_comm d 1
      _ = e     := hed.symm
  #print gamer  -- shitload of `trans`es wrapping what you'd otherwise expect.
  -- c.f. the following, which is pretty much the same
  theorem gamer'
    (a b c d e : Nat)
    (hab : a = b)
    (hbc : b = c + 1)
    (hcd : c = d)
    (hed : e = 1 + d)
    : a = e :=
    have h_ab   : a = b     := hab
    have h_ac1  : a = c + 1 := h_ab.trans hbc
    have h_ad1  : a = d + 1 := h_ac1.trans $ congrArg (· + 1) hcd
    have h_a1d  : a = 1 + d := h_ad1.trans $ Nat.add_comm d 1
    have h_ae   : a = e     := h_a1d.trans hed.symm
    ; h_ae
  #print gamer'
  -- btw, *anonymous `have` expressions* make this easier.
  -- In the following, `this` always refers to the last term produced
  --  by an anonymous have expression. Because of variable scoping under
  --  colliding names, this is really the same as replacing each `have : ⋯`
  --  with `have this : ⋯`.
  theorem gamer''
    (a b c d e : Nat)
    (hab : a = b)
    (hbc : b = c + 1)
    (hcd : c = d)
    (hed : e = 1 + d)
    : a = e :=
    have : a = b     := hab
    have : a = c + 1 := this.trans hbc
    have : a = d + 1 := this.trans $ congrArg (· + 1) hcd
    have : a = 1 + d := this.trans $ Nat.add_comm d 1
    have : a = e     := this.trans hed.symm
    ; this
  #print gamer''

  -- The `rw = rewrite` tactic is especially useful when working with `calc` blocks.
  -- It does what you think it does, which isn't really explained until later.
  -- Essentially, it abstracts away all those `.symm`, `congrArg` and other
  --  "precise boilerplate" functions that need to be thrown in, and it's a bit
  --  more powerful than that.
  theorem gamer'''
    (a b c d e : Nat)
    (hab : a = b)
    (hbc : b = c + 1)
    (hcd : c = d)
    (hed : e = 1 + d)
    : a = e :=
    calc a
      _ = b     := by rw [hab]
      _ = c + 1 := by rw [hbc]
      _ = d + 1 := by rw [hcd] -- the `congrArg` and its precise parameters are autofilled here
      _ = 1 + d := by rw [Nat.add_comm] -- the precise parameters to `Nat.add_comm` are autofilled here
      _ = e     := by rw [hed] -- the `.symm` is autofilled here
    #print gamer'''
  -- You can add multiple things to the parameter list of `rw` to apply all of them.
  theorem gamer''''
    (a b c d e : Nat)
    (hab : a = b)
    (hbc : b = c + 1)
    (hcd : c = d)
    (hed : e = 1 + d)
    : a = e :=
    calc a
      _ = d + 1 := by rw [hab, hbc, hcd]
      _ = 1 + d := by rw [Nat.add_comm]
      _ = e     := by rw [hed]
  #print gamer''''
  -- It's powerful enough that throwing all these rules into the rewriter is enough
  --  to complete this contrived theorem's proof
  theorem gamer'''''
    (a b c d e : Nat)
    (hab : a = b)
    (hbc : b = c + 1)
    (hcd : c = d)
    (hed : e = 1 + d)
    : a = e := by
      rw [hab, hbc, hcd, Nat.add_comm, hed]
  #print gamer'''''
  -- While the `rw` tactic applies the given hypotheses sequentially, the `simp`
  --  tactic applies them in any order, and perhaps repeatedly. Because of careful
  --  rules that ensure termination of `simp` calls, it might leave you with something
  --  a little weird though.
  theorem gamer''''''
    (a b c d e : Nat)
    (hab : a = b)
    (hbc : b = c + 1)
    (hcd : c = d)
    (hed : e = 1 + d)
    : a = e := by
      simp [hab, hbc, hcd, hed, Nat.add_comm]
  #print gamer''''''

  -- `calc` can be used with any suitably compatible transitive relations. e.g.
  theorem funny
    (a b c d : Nat)
    (hab : a = b)
    (hbc : b ≤ c)
    (hcd : c + 1 < d)
    : a < d :=
    calc a
      _ = b     := hab
      _ ≤ c     := hbc
      _ ≤ c + 1 := Nat.le_succ c
      _ < d     := hcd
  #print funny
  #check trans -- Key point of the type signature: *heterogeneous* transitivity!

  -- `calc` is really a wrapper for putting in necessary `Trans.trans` calls.
  -- You can therefore extend its reach by implementing `instance : Trans ⋯` :)
  section divides_trans
    def divides (x y : Nat) : Prop :=
      ∃ d : Nat, y = d * x
    infix:50 " /|/ " => divides -- `|` is already really overloaded okay...

    def divides_trans
      {x y z : Nat}
      (h_xy : x /|/ y) (h_yz : y /|/ z)
      : x /|/ z :=
        let ⟨d_xy, pf_d_xy⟩ : ∃ (d_xy : Nat), (y = d_xy * x) := h_xy
        let ⟨d_yz, pf_d_yz⟩ : ∃ d_yz : Nat, z = d_yz * y := h_yz
        let d_xz : Nat := d_yz * d_xy
        have pf_d_xz : z = (d_yz * d_xy) * x :=
          calc z
            _ = d_yz * y          := pf_d_yz
            _ = d_yz * (d_xy * x) := congrArg (d_yz * ·) pf_d_xy
            _ = (d_yz * d_xy) * x := (Nat.mul_assoc d_yz d_xy x).symm
        show ∃ d_xz : Nat, z = d_xz * x from ⟨d_xz, pf_d_xz⟩

    def divides_mul
      (x d : Nat)
      : x /|/ (d * x) :=
      show ∃ d' : Nat, d * x = d' * x from ⟨d, rfl⟩

    instance : Trans divides divides divides where
      trans := divides_trans

    example
      {x y z : Nat}
      (h_x_d_y : x /|/ y)
      (h_y_e_z : y  =  z)
      : x /|/ (2 * z) :=
        calc x
          _ /|/ y       := h_x_d_y
          _  =  z       := h_y_e_z
          _ /|/ (2 * z) := divides_mul .. -- short for `divides_mul _ _` -- Lean can synthesise these to `divides_mul z 2`
  end divides_trans

  -- Final example
  example
    {x y : Nat}
    : (x + y) * (x + y)
      = x * x  +  y * x  +  x * y  +  y * y
    := calc (x + y) * (x + y)
      _ = (x + y) * x  +  (x + y) * y
          := Nat.mul_add ..
      _ = x * x  +  y * x  +  (x + y) * y
          := congrArg (· + (x + y) * y) $ Nat.add_mul ..
      _ = x * x  +  y * x  +  (x * y  +  y * y)
          := congrArg (x * x  +  y * x  +  ·) $ Nat.add_mul ..
      _ = (x * x  +  y * x)  +  x * y  +  y * y
          := Eq.symm $ Nat.add_assoc (x * x + y * x) (x * y) (y * y)
          -- this last line was a huge pain in the ass to figure out
  -- Simplified using `rw`
  example
    {x y : Nat}
    : (x + y) * (x + y)
      = x * x  +  y * x  +  x * y  +  y * y
    := calc (x + y) * (x + y)
      _ = (x + y) * x  +  (x + y) * y
          := by rw [Nat.mul_add]
      _ = x * x  +  y * x  +  (x + y) * y
          := by rw [Nat.add_mul]
      _ = x * x  +  y * x  +  (x * y  +  y * y)
          := by rw [Nat.add_mul]
      _ = (x * x  +  y * x)  +  x * y  +  y * y
          := by rw [←Nat.add_assoc]
          -- The `←` throws in the `Eq.symm $` for us
  -- Simplified more using `rw`
  example
    {x y : Nat}
    : (x + y) * (x + y)
      = x * x  +  y * x  +  x * y  +  y * y
    := by
      rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]
  -- Simplified further by `simp`
  example
    {x y : Nat}
    : (x + y) * (x + y)
      = x * x  +  y * x  +  x * y  +  y * y
    := by
      simp [Nat.mul_add, Nat.add_mul, ←Nat.add_assoc]
  -- And finalised by `simp`
  example
    {x y : Nat}
    : (x + y) * (x + y)
      = x * x  +  y * x  +  x * y  +  y * y
    := by
      simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]  -- `simp` doesn't need the `←`
end the_calc_feature



/- SECTION: ∃ -/
section existential_crisis
  #print Exists
  /-
    *`inductive Exists.{u} : {α : Sort u} → (α → Prop) → Prop               `*
    *`number of parameters: 2                                               `*
    *`constructors:                                                         `*
    *`Exists.intro : ∀ {α : Sort u} {p : α → Prop} (w : α), p w → Exists p  `*  -- The predicate `p` itself being quantified over is implicit. This comes to bite us sometimes.
  -/
  -- So, `∃ x : α, p x` is more-or-less `Σ x : α, p x`, up to universe differences.
  -- NOTE: `⟨·, ·⟩` notation is far more convenient than writing `Exists.intro · ·`.

  example : ∃ x : Nat, x > 0 := ⟨1, Nat.zero_lt_one⟩
  example
    {x : Nat}
    (h : x > 0)
    : ∃ y : Nat, y < x :=
      ⟨0, h⟩
  example
    {x y z : Nat}
    (h_xy : x < y) (h_yz : y < z)
    : ∃ w : Nat, x < w  ∧  w < z :=
      ⟨y, ⟨h_xy, h_yz⟩⟩

  -- The elimination rule is the **universal property of the coproduct**, and as such is implemented by pattern matching.
  #check @Exists.elim -- *`: ∀ {α : Sort u} {p : α → Prop} {q : Prop},  (∃ a : α, p a) → (∀ a : α, p a → q) → q`*
  def Exists.elim'.{u}
    {α : Sort u} {p : α → Prop} {q : Prop}
    (h_ext_p : ∃ a : α, p a)
    (h_all_p_2_q : ∀ a : α, p a → q)
    : q :=
      let ⟨a, pf_a⟩ := h_ext_p
      ; h_all_p_2_q a pf_a

  example
    {α : Type}
    (p q : α → Prop)
    (h : ∃ x : α, p x ∧ q x)
    : ∃ x, q x ∧ p x :=
      h.elim $
        fun (a : α) (h' : p a ∧ q a) =>
        ⟨a, And.intro h'.right h'.left⟩
  example
    {α : Type}
    (p q : α → Prop)
    (h : ∃ x : α, p x ∧ q x)
    : ∃ x, q x ∧ p x :=
      match h with
      | ⟨(x : α), (⟨pf_p_x, pf_q_x⟩ : p x ∧ q x)⟩ =>
        ⟨x, ⟨pf_q_x, pf_p_x⟩⟩

  section even_example
    def Nat.is_even (a : Nat) := ∃ d : Nat, a = 2 * d

    theorem even_plus_even_is_even
      {a b : Nat}
      (h_a : a.is_even) (h_b : b.is_even)
      : (a + b).is_even :=
        let ⟨(α : Nat), (pf_α : a = 2 * α)⟩ := h_a
        let ⟨(β : Nat), (pf_β : b = 2 * β)⟩ := h_b
        let σ : Nat := α + β
        suffices pf_σ : a + b = 2 * σ from ⟨σ, pf_σ⟩
        calc a + b
          _ = 2 * α + b
              := congrArg (· + b) pf_α
          _ = 2 * α + 2 * β
              := congrArg (2 * α + ·) pf_β
          _ = 2 * (α + β)
              := (Nat.mul_add 2 α β).symm
          _ = 2 * σ -- this last one isn't necessary
              := rfl
    -- Shortening the proof...
    theorem even_plus_even_is_even'
      {a b : Nat}
      (h_a : a.is_even) (h_b : b.is_even)
      : (a + b).is_even :=
        let ⟨(α : Nat), (pf_α : a = 2 * α)⟩ := h_a
        let ⟨(β : Nat), (pf_β : b = 2 * β)⟩ := h_b
        let σ : Nat := α + β
        suffices pf_σ : a + b = 2 * σ from ⟨σ, pf_σ⟩
        by rw [pf_α, pf_β, ←Nat.mul_add]
    -- Even more...
    theorem even_plus_even_is_even''
      {a b : Nat}
      (h_a : a.is_even) (h_b : b.is_even)
      : (a + b).is_even :=
        let ⟨(α : Nat), (pf_α : a = 2 * α)⟩ := h_a
        let ⟨(β : Nat), (pf_β : b = 2 * β)⟩ := h_b
        let σ : Nat := α + β
        suffices pf_σ : a + b = 2 * σ from ⟨σ, pf_σ⟩
        by
          simp [pf_α, pf_β]
          simp [←Nat.mul_add]
    -- Golf...
    theorem even_plus_even_is_even''' {a b : Nat} (h_a : a.is_even) (h_b : b.is_even) : (a + b).is_even := let ⟨α, pf_α⟩ := h_a ; let ⟨β, pf_β⟩ := h_b; ⟨α + β, by simp [pf_α, pf_β, Nat.mul_add]⟩
  end even_example

  -- Just like we don't have the `¬∧ → ∨¬` direction of DeMorgan's in constructive logic, we need classical help for the `¬∀¬ ↔ ∃` proof
  open Classical in
  example
    {α : Type}
    {p : α → Prop}
    (h : ¬ ∀ (x : α), ¬ p x)
    : ∃ (x : α), p x :=
      byContradiction $
      fun h' : (∃ x : α, p x) → False =>
      h $
      fun x : α =>
      fun h'' : p x =>
      h' $
      ⟨x, h''⟩
end existential_crisis



/- SECTION: More lean niceties -/
section hospitality
  -- NOTE: `by assumption`
  -- The `assumption` tactic looks through the list of propositions in the current context, and if it finds one that matches the current goal, it applies it.
  section gamer
    variable (f : Nat → Nat)
    variable (h : ∀ x : Nat, f x ≤ f (x + 1))

    -- Here's a use of `by assumption`
    example : f 0 ≤ f 3 :=
      have : f 0 ≤ f 1 := h 0
      have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
      have : f 0 ≤ f 3 := Nat.le_trans (by assumption) (h 2)
      this

    -- Alternative syntax `⟨p⟩` for `show p by assumption` is really nice, and more robust since type inference of `p` isn't forced onto Lean
    --  *`notation "‹" p "›" => show p by assumption`*
    example : f 0 ≤ f 3 :=
      have : f 0 ≤ f 1 := h 0
      have : f 0 ≤ f 2 := Nat.le_trans ‹f 0 ≤ f 1› (h 1)
      have : f 0 ≤ f 3 := Nat.le_trans ‹f 0 ≤ f 2› (h 2)
      ‹f 0 ≤ f 3›

    example
      : f 0 ≥ f 1
      → f 1 ≥ f 2
      → f 0 = f 2
      :=
        fun _ : f 0 ≥ f 1 =>
        fun _ : f 1 ≥ f 2 =>
        have gamer : f 0 ≤ f 2 :=
          calc f 0
            _ ≤ f 1 := h 0
            _ ≤ f 2 := h 1
        -- Could use this too:
        -- have otherGamer : f 2 ≤ f 0 :=
        --   calc f 2
        --     _ ≤ f 1 := by assumption
        --     _ ≤ f 0 := by assumption
        Nat.le_antisymm gamer (Nat.le_trans ‹f 2 ≤ f 1› ‹f 1 ≤ f 0›)
  end gamer
end hospitality



/- EXERCISES: Classical existence laws -/
section exercises_classical_existence
  open Classical

  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  -- EXERCISE: Obvious
  example : (∃ _ : α, r) → r := fun ⟨_, pf⟩ => pf
  example (a : α) : r → (∃ _ : α, r) := fun h_r => ⟨a, h_r⟩
  example
    : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
      -- (→)
      have right : (∃ x : α, p x ∧ r) → (∃ x : α, p x) ∧ r :=
        fun ⟨x, ⟨pf_px, pf_r⟩⟩ =>
        ⟨⟨x, pf_px⟩, pf_r⟩
      ;
      -- (←)
      have left  : (∃ x : α, p x) ∧ r → (∃ x : α, p x ∧ r) :=
        fun ⟨⟨x, pf_px⟩, pf_r⟩ =>
        ⟨x, ⟨pf_px, pf_r⟩⟩
      ;
      -- (↔)
      Iff.intro right left
  example
    : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
      -- (→)
      have right : (∃ x, p x ∨ q x) → (∃ x, p x) ∨ (∃ x, q x) :=
        fun ⟨x, pf_or⟩ =>
        pf_or.elim
          (fun pf_px => Or.inl ⟨x, pf_px⟩)
          (fun pf_qx => Or.inr ⟨x, pf_qx⟩)
      ;
      -- (←)
      have left : (∃ x, p x) ∨ (∃ x, q x) → (∃ x, p x ∨ q x) :=
        fun h_or =>
        h_or.elim
          (fun ⟨x, h_px⟩ => ⟨x, Or.inl h_px⟩)
          (fun ⟨x, h_qx⟩ => ⟨x, Or.inr h_qx⟩)
      ;
      -- (↔)
      ⟨right, left⟩

  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
    -- (→)
    have right : (∀ x, p x) → (∃ x, p x → False) → False :=
      fun h_all_p ⟨x, h_not_px⟩ =>
      h_not_px (h_all_p x)
    ;
    -- (←)
    have left : ¬ (∃ x, p x → False) → (∀ x, p x) :=
      fun h_not_exists_not_p (x : α) =>
      byContradiction $ -- NOTE: Nonconstructive
      fun h_not_px =>
      h_not_exists_not_p ⟨x, h_not_px⟩
    ;
    -- (↔)
    ⟨right, left⟩

  set_option linter.unusedVariables false
  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
    -- (→)
    have R : (∃ x, p x) → (∀ x, ¬ p x) → False :=
      fun (⟨x, h_px⟩ : ∃ y : α, p y) (h_all_not_p : ∀ y, ¬ p y) =>
      h_all_not_p x h_px
    ;
    -- (←)
    have L : ¬ (∀ x, ¬ p x) → (∃ x, p x) :=
      fun h_not_all_not_p =>
      byContradiction $ -- NOTE: Nonconstructive!
      fun h_not_exists_p =>
      h_not_all_not_p $
      fun x h_px =>
      h_not_exists_p ⟨x, h_px⟩
    ;
    -- (↔)
    ⟨R, L⟩
  set_option linter.unusedVariables true

  -- EXERCISE: `¬∃ ↔ ∀¬`; constructive
  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
    -- (→)
    have right (h_n_ex : ¬ ∃ x, p x) : (∀ x, ¬ p x) :=
      fun x h_px =>
      h_n_ex ⟨x, h_px⟩
    -- (←)
    have left (h_all_n : ∀ x, ¬ p x) (h_ex : ∃ x, p x) : False :=
      let ⟨x, h_px⟩ := h_ex
      h_all_n x h_px
    -- (↔)
    ⟨right, left⟩

  -- EXERCISE: `¬∀ ↔ ∃¬`; nonconstructive
  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
    -- (→) NOTE: nonconstructive
    have right (h_n_all : ¬ ∀ x, p x) : (∃ x, ¬ p x) :=
      byContradiction $
      fun h_n_ex_n =>
      h_n_all $
      fun x =>
      byContradiction $
      fun h_n_px =>
      h_n_ex_n $
      ⟨x, h_n_px⟩
    -- (←)
    have left (h_ex_n : ∃ x, ¬ p x) (h_all : ∀ x, p x) : False :=
      let ⟨x, h_n_px⟩ := h_ex_n
      h_n_px (h_all x)
    -- (↔)
    ⟨right, left⟩

  -- EXERCISE: Universal property of the coproduct
  example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
    -- (→)
    have right (h_all : ∀ x, p x → r) (h_exi : ∃ x, p x) : r :=
      let ⟨x, h_px⟩ := h_exi
      h_all x h_px
    -- (←)
    have left (h_exi_2_r : (∃ x, p x) → r) : (∀ x, p x → r) :=
      fun x h_px => h_exi_2_r ⟨x, h_px⟩
    -- (↔)
    ⟨right, left⟩

  -- EXERCISE: Weird shit
  example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
    -- (→)
    have right (h_ex : ∃ x, p x → r) (h_all : ∀ x, p x) : r :=
      let ⟨x, h_px_2_r⟩ := h_ex
      h_px_2_r (h_all x)
    -- (←)
    have left (h_all_p__2_r : (∀ x, p x) → r) : ∃ x, p x → r :=
      have pf_case_r (h_r : r) : ∃ x, p x → r :=
        ⟨a, fun _ => h_r⟩
      have pf_case_nr (h_nr : ¬r) : ∃ x, p x → r :=
        byContradiction $
        fun h_n_exi_p_2_r =>
        h_nr ∘ h_all_p__2_r $
        fun x =>
        byContradiction $
        fun h_n_px =>
        h_n_exi_p_2_r $
        ⟨x, fun h_px => absurd h_px h_n_px⟩
      byCases (p := r)
        pf_case_r
        pf_case_nr
    -- (↔)
    ⟨right, left⟩

  -- EXERCISE: Weird shit
  example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
    -- (→)
    have right (h_exi : ∃ x, r → p x) (h_r : r) : ∃ x, p x :=
      let ⟨x, h_r_2_px⟩ := h_exi
      ⟨x, h_r_2_px h_r⟩
    -- (←)
    have left (h_r_2_exi_p : r → ∃ x, p x) : ∃ x, r → p x :=
      -- (Case: r)
      have pf_case_r (h_r : r) : ∃ x, r → p x :=
        let ⟨x, h_px⟩ := h_r_2_exi_p h_r
        ⟨x, fun _ => h_px⟩
      -- (Case: ¬ r)
      have pf_case_nr (h_nr : r → False) : ∃ x, r → p x :=
        ⟨a, fun h_r => absurd h_r h_nr⟩
      -- Stitched together
      byCases (p := r)
        pf_case_r
        pf_case_nr
    -- (↔)
    ⟨right, left⟩
end exercises_classical_existence
