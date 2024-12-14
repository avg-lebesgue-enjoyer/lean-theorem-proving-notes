/- @file Notes/4QuantifiersEquality.lean
 - @src https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html
 -/

/- SECTION: ∀ -/
section universal_quantifier
  -- We can encode `∀ x : α, p x` by the dependent function type `(x : α) → p x`. This is obvious if you think for a couple of seconds about it.
  -- Introduction rule is lambda abstraction; Elimination rule is application
end universal_quantifier
