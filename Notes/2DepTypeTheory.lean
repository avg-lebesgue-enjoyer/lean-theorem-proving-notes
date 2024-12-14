/- @file Notes/2DepTypeTheory
 - @src https://lean-lang.org/theorem_proving_in_lean4/dependent_type_theory.html
 -/

/- SECTION: Sorts and Types -/

/- NOTE: Sorts and types
    Prop   := Sort 0
    Type   := Sort 1
    Type 1 := Sort 2
    ...
    Type n := Sort (n + 1)
-/



/- SECTION: Universes -/
section theUniverses -- opens scoped block
  -- Universes exist for the reason you think they do.

  -- In the following, `v` is a universe level, and `G` is polymorphic over it.
  def G.{v} (α : Type v) : Type v := Prod α α
  #check G

  universe u -- This declares `u` as a universe. It's now a variable in the current scope (`theUniverses`)
  -- In the following, `F` **is polymorphic over the universe level `u`**.
  -- This is because Lean is nice and will automatically chuck in polymorphism over declared
  --  `variable`s or `universe` levels.
  def F     (α : Type u) : Type u := Prod α α
  #check F
end theUniverses



/- SECTION: Variables -/
section theVariables
  variable (α β γ : Type) -- This declares variables `α β γ : Type`, and all functions etc that use
                          --  them in this scope will be polymorphic over each of them.
  def compose (g : β → γ) (f : α → β) := fun a : α => g (f a)
  #check @compose -- *`compose : (α β γ : Type) → (β → γ) → (α → β) → α → γ`*
                  -- ^^polymorphism thrown in

  variable (g : β → γ) (f : α → β)
  def compose' := fun a : α => g (f a)
  #check @compose'  -- *`compose' : (α β γ : Type) → (β → γ) → (α → β) → α → γ`*
                    -- ^^polymorphism thrown in
end theVariables

-- NOTE: `section`s can be nested.



/- SECTION: -/
