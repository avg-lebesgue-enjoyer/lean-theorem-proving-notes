/- @file Notes/10TypeClasses.lean
 - @src https://lean-lang.org/theorem_proving_in_lean4/type_classes.html
 -/

/- SECTION: Type Classes -/
section type_classes
  namespace ligma
    structure Add (α : Type) where
      add : α → α → α
    #check @Add.add -- *`: {α : Type} → Add α → α → α → α`*

    def double (inst : Add α) (x : α) : α :=
      inst.add x x
    #check @double
  end ligma
  namespace ligma'
    class Add (α : Type) where
      add : α → α → α
    #check @Add.add -- *`: {α : Type} → [self : Add α] → α → α → α`*
                    -- This is like Haskell's `add :: Add α => α → α → α`

    instance : Add Nat   where add := Nat.add
    instance : Add Int   where add := Int.add
    instance : Add Float where add := Float.add

    def double [Add α] (x : α) : α :=
      Add.add x x
    set_option pp.all true
    #print double
    set_option pp.all false

    #eval double (10 : Nat)
    #eval double (7 : Float)

    instance [Add α] : Add (Array α) where
      add xs ys := Array.zipWith xs ys Add.add
    #eval Add.add #[1, 2] #[3, 4]
  end ligma'

  namespace gaming
    class Inhabited (α : Type u) where
      default : α
    #check @Inhabited.default -- *`: {α : Type u} → [self : Inhabited α] → α`*

    instance : Inhabited Bool where default := true
    instance : Inhabited Nat  where default := 0
    instance : Inhabited Unit where default := ()
    instance : Inhabited Prop where default := True

    export Inhabited (default) -- Exposes `default := Inhabited.default` henceforth in this file.
    #print default
    #eval (default : Nat)
  end gaming
end type_classes



/- SECTION: Chaining Instances -/
section chain
  namespace gaming
    instance [Inhabited α] [Inhabited β] : Inhabited (α × β) where
      default := (default, default)
    #eval (default : Nat × Bool) -- *`(0, true)`*

    instance
      {α : Type u_src} {β : Type u_tgt}
      [Inhabited β]
      : Inhabited (α → β)
    where
      default := fun _ => default

    instance : Inhabited (List α) where default := []
    instance [Inhabited α] : Inhabited (α ⊕ β) where default := .inl default
    instance [Inhabited β] : Inhabited (α ⊕ β) where default := .inr default

    #print inferInstance
    -- *`@[reducible] def inferInstance.{u} `*
    -- *` : {α : Sort u} → [i : α] → α      `*
    -- *` := fun {a} [i : α] => i           `*

    def foo : Inhabited (Nat × Nat) := inferInstance  -- Exposes an instance
    example : foo.default = (default, default) := rfl -- Theorem showing us that the instance is what you think it is
  end gaming
end chain



/- SECTION: ToString -/
section tos
  structure Person where
    name : String
    age  : Nat
  instance : ToString Person where
    toString p := s!"{p.name} (aged {p.age})"
  #eval toString { name := "Leo", age := 666 : Person } -- *`"Leo (aged 666)"`*
end tos



/- SECTION: OfNat -/
section ofn
  structure Rational where
    numerator   : Int
    denominator : Nat
    isLegal     : denominator ≠ 0
  instance : OfNat Rational n where
    ofNat := ⟨n, 1, fun h => nomatch h⟩
  instance : ToString Rational where
    toString r := s!"{r.numerator} / {r.denominator}"
  #eval (2 : Rational) -- *`2 / 1`*
  #check (nat_lit 2)
end ofn
