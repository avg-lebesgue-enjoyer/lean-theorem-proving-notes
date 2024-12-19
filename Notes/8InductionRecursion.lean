/- @file Notes/8InductionRecursion.lean
 - @src https://lean-lang.org/theorem_proving_in_lean4/induction_and_recursion.html
 -/

/- SECTION: Pattern Matching -/
-- Yeah it exists



/- SECTION: Wildcards and Overlapping Patterns -/
-- NOTE: Lean handles overlapping patterns the same way that Haskell does;
--        take the first match



/- SECTION: Structural Recursion and Induction -/
section structural_induction
  -- NOTE: Recursive definitions generate internal theorems presented to `simp`
  --       at the use of the definition's name
  def add : Nat → Nat → Nat
    | x, 0        => x
    | x, .succ y  => .succ (add x y)
  theorem zero_add : ∀ x, add 0 x = x
    | 0       => by simp [add]
    | .succ x => by simp [add, zero_add]
  #print zero_add
  theorem sigma : add 0 0 = 0 := by simp [add]
  #print sigma

  variable (C : Nat → Type u)
  #check @Nat.below C
  #check @Nat.below C (3 : Nat)
  #check @Nat.brecOn C
  #print Nat.below
  #print Nat.rec
  #print PUnit -- universe-`P`olymorphic `Unit`
  #print PProd -- universe-`P`olymorphic `Prod`uct, whose arguments may be propositions
end structural_induction



/- SECTION: Local Recursive Declarations -/
section the_let_rec
  --
end the_let_rec
