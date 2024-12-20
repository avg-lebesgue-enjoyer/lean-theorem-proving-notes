/- @file Notes/06Interaction.lean
 - @src https://lean-lang.org/theorem_proving_in_lean4/interacting_with_lean.html
 -/

/- SECTION: Attributes -/
section the_attributes
  -- NOTE: The `local` modifier restricts stuff to *this section*.

  -- NOTE: `simp` allows the `simp`lifier to use the result
  def isPrefix {α : Type} (xs ys : List α) : Prop := ∃ zs : List α, xs ++ zs = ys
  @[simp] theorem List.isPrefix_self {α : Type} (xs : List α) : isPrefix xs xs :=
    ⟨[], by simp⟩
  #print List.isPrefix_self
  def simp_attr_example : isPrefix [1, 2, 3] [1, 2, 3] := by simp
  #print simp_attr_example

  -- NOTE: `instance` works by adding the `attribute [instance]`
  -- instance {α : Type} : LE (List α) where
  --   le := isPrefix
  def List.instanceLE {α : Type} : LE (List α) := { le := isPrefix } -- Remember that type`class`es are just `structure`s? This is that in action
  attribute [local instance] List.instanceLE
  -- Now `≤` can be used with `List`s
  example {α : Type} (xs : List α) : xs ≤ xs := by
    show isPrefix xs xs
    apply List.isPrefix_self
end the_attributes



/- SECTION: Notation -/
section the_notation
  infixl:65     "||||"      => HAdd.hAdd  -- Left associative,    precedence 65
  infix:50      "|||||"     => Eq         -- Nonassociative,      precedence 50; lowest of these examples
  infixr:80     "||||||"    => HPow.hPow  -- right associative,   precedence 80
  prefix:100    "|||||||"   => Neg.neg    -- prefix (duh),        precedence 100
  postfix:max   "||||||||"  => Neg.neg    -- postfix (duh),       precedence 1024; highest of these examples

  notation:10 Γ " ⊢⊢ " e:50 " ::: " τ => Γ e τ -- Mixfix. The arguments with no precedence number (i.e. `Γ` and `τ`) are allocated precedence `:0`.
end the_notation



/- SECTION: Setting Options -/
section setting_options
  set_option pp.explicit true -- Display implicit arguments
  #print And.intro
  set_option pp.explicit false

  set_option pp.universes true -- Display universes
  #print Prod
  set_option pp.universes false

  set_option pp.notation false
  #reduce (fun x => x + 2) = (fun x => x + 3)
  set_option pp.notation true
  #reduce (fun x => x + 2) = (fun x => x + 3)
end setting_options



/- SECTION: Automatically Bound Implicit Arguments -/
section evil
  -- This is super useful, but it also hides a lot of shit
  def compose (g : β → γ) (f : α → β) (x : α) : γ := g (f x)
  set_option pp.universes true
  #check @compose -- *`@compose.{u_1, u_2, u_3} : {β : Sort u_1} → {γ : Sort u_2} → {α : Sort u_3} → (β → γ) → (α → β) → α → γ`*
  -- Automatically introduced universes `u_1` etc. and automatically bound `{β : Sort u_1}` etc.
  set_option pp.universes false

  set_option autoImplicit false
  -- `def compose' (g : β → γ) (f : α → β) (x : α) : γ := g (f x)`
  -- ^^now produces `"unknown indentifier"` error messages
end evil
