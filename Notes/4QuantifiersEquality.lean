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
end the_calc_feature
