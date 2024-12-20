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
-- Gaming
