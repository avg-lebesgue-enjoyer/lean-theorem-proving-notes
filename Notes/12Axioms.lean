/- @file Notes/12Axioms.lean
 - @src https://lean-lang.org/theorem_proving_in_lean4/axioms_and_computation.html
 -/

/- SECTION: Prelude -/
section haha_prelude
  -- NOTE: Diaconescu's theorem asserts that `choice`, `propext` and `funext` are
  --        enough to derive `Classical.em`.
  #print Nonempty -- *`: Sort u → Prop`*, produces **propositions**,
                  --  thereby erasing data of a witness.
  #print Classical.choice -- *`axiom choice.{u} : {α : Sort u} → Nonempty α → α`*
                          --  From just the **proposition** that `α` is `Nonempty`,
                          --  `noncomputable`y produce a term of type `α`.
  #print propext  -- *`axiom propext : ∀ {p q : Prop}, (p ↔ q) → p = q`*;
                  --  effectively the notion of "sameness" for propositions being
                  --  extended to define equality on them.
  #print funext -- *`theorem funext.{u, u'} : ∀ {α : Sort u} {β : α → Sort u'} {f g : (x : α) → β x}, (∀ (x : α), f x = g x) → f = g`*;
                --  what you think it is
  #print axioms funext -- Depends on `axiom Quot.sound`
  #print Quot.sound -- *`axiom Quot.sound.{u} : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b`*;
                    --  the "soundness" axiom for quotients; `r`-related things should be `=` in the `Quot`ient by `r`.
  #print Quot -- *`: {α : Sort u} → (α → α → Prop) → Sort u`*; gaming

  def Set : Type → Type := (· → Prop)
  def Set.isNonempty (X : Set α) : Prop := ∃ x : α, X x
  -- NOTE: This proof relies on *exactly one* use of each of `propext` and `funext`.
  -- These calls are used to construct a proof of `p → U = V`, which we need in order to
  --  show that `p → f U ⋯ = f V ⋯`.
  -- In fact, `funext` is used to show `U = V`, *but this is really **Set** extensionality*,
  --  since we're regarding `U` and `V` as sets here.
  -- The use of `propext` is in showing the hypothesis we pass to `funext` (set-extensionality);
  --  namely, that `∀ x, U x = V x`
  theorem diaconescu
    (choice : ∀ {α : Type} (X : Set (Set α)),
                X.isNonempty → (∀ (Y : Set α) (_ : X Y), Y.isNonempty)
                → ∃ (f : (x : Set α) → X x → α),
                    ∀ (x : Set α) (h : X x), x (f x h))
    (propext : ∀ {p q : Prop}, (p ↔ q) → (p = q)) -- NOTE: Not sure where propositional extensionality got used during the proof. I *suspect* that `simp` buries such an application under the hood somewhere
    (funext : ∀ {α : Type} {β : α → Type} {f g : (x : α) → β x},
                (∀ (x : α), f x = g x) → f = g)
    (p : Prop)
    : p ∨ ¬p
    := -- As an exercise, I did the formalisation of what Wikipedia outlined the proof. This happend while I should've been sleeping. It took at least 1.5 hours, and I'm very tired...
      let U : Set Bool := fun x => (x = false) ∨ p
      let V : Set Bool := fun x => (x = true)  ∨ p
      have h_U_nonempty : ∃ x : Bool, U x := by exists false ; unfold U ; apply Or.inl ; rfl
      have h_V_nonempty : ∃ x : Bool, V x := by exists true  ; unfold V ; apply Or.inl ; rfl
      let X : Set (Set Bool) := fun x => (x = U) ∨ (x = V)
      have h_X_nonempty : ∃ x : Set Bool, X x := by exists U ; unfold X ; apply Or.inl ; rfl
      have h_U_in_X : X U := by unfold X ; apply Or.inl ; rfl
      have h_V_in_X : X V := by unfold X ; apply Or.inr ; rfl
      have h_in_X_iff_eq_U_or_V : ∀ (y : Set Bool), X y ↔ y = U ∨ y = V := by
        intro y
        unfold X
        rfl
      have h_all_in_X_nonempty : ∀ (y : Set Bool), X y → y.isNonempty := by
        intro y h_y_in_X
        have h_y_eq_U_or_V : y = U ∨ y = V := (h_in_X_iff_eq_U_or_V y).mp h_y_in_X
        cases h_y_eq_U_or_V <;> (rename_i h; rw [h] ; assumption)
      have h_yippee_choice
        : ∃ f : (x : Set Bool) → X x → Bool,
          ∀ (y : Set Bool) (h : X y), y (f y h)
        := choice X h_X_nonempty h_all_in_X_nonempty
      have h_exists_choice_function
        : ∃ f : (x : Set Bool) → X x → Bool,
          U (f U h_U_in_X) ∧ V (f V h_V_in_X)
        := by
          let ⟨f, h⟩ := h_yippee_choice
          exists f
          constructor <;> apply h
      let ⟨f, ⟨h_f_U, h_f_V⟩⟩ := h_exists_choice_function
      have h_f_U' : (f U h_U_in_X = false) ∨ p := h_f_U
      have h_f_V' : (f V h_V_in_X = true ) ∨ p := h_f_V
      have h_f_U'_V' : p ∨ (f U h_U_in_X ≠ f V h_V_in_X) :=
        match h_f_U', h_f_V' with
        | .inr h_p    , _           => .inl h_p
        | _           , .inr h_p    => .inl h_p
        | .inl h_false, .inl h_true => by
          apply Or.inr
          rw [ne_eq, h_false, h_true]
          intro a
          injection a
      have h_p_2_f_same : p → f U h_U_in_X = f V h_V_in_X := by -- NOTE: The extensionality axioms get used in constructing this function
        intro h_p
        have h_4_funext : ∀ x : Bool, U x = V x := by
          intro x
          unfold U ; unfold V
          -- NOTE: Goal `⊢ (x = false  ∨  p) = (x = true  ∨  p)` is NOT true by `rfl` since the left and right are NOT definitionally equal.
          --       That is, **propositional extensionality is necessary here**.
          --       In fact, as you can see from the lack of `propext` in the rest of the proof,
          --        **this is the only spot where it needs to get used**.
          apply propext
          constructor <;> (intro _ ; apply Or.inr ; assumption)
        have h_U_eq_V : U = V := @funext Bool (fun _ => Prop) U V h_4_funext -- NOTE: `funext` used
        have a : f V (h_U_eq_V ▸ h_U_in_X) = f V h_V_in_X := rfl
        have b : f U h_U_in_X = f V (h_U_eq_V ▸ h_U_in_X) :=
          h_U_eq_V.recOn rfl
        have := b.trans a
        assumption
      have h_not_f_same_2_p : f U h_U_in_X ≠ f V h_V_in_X → ¬p := by
        intro h h_p
        exact h (h_p_2_f_same h_p)
      show p ∨ ¬p from
        match h_f_U'_V' with
        | .inl h_p => .inl h_p
        | .inr h   => .inr $ h_not_f_same_2_p h
      /- Rough outline from Wikipedia:
        **The fact that `U` and `V` are subSETs of `2` is important here**, I think
        U := { x ∈ 2 | (x = 0) ∨ p }
        V := { x ∈ 2 | (x = 1) ∨ p }
        Observe: U and V are non-empty (obvious witnesses)
        X := { U, V }
        Observe: X is non-empty
        Let f : X → 2 be a choice function on X (i.e. f U ∈ U and f V ∈ V)
        Observe: f U ∈ U  iff  (f U = 0) ∨ p
                 f V ∈ V  iff  (f V = 1) ∨ p
        Thus, (f U ∈ U) ∧ (f V ∈ V)
              ↔ ((f U = 0) ∨ p) ∧ ((f V = 1) ∨ p)
              ↔ ((f U = 0) ∧ (f V = 1)) ∨ p
              → (f U ≠ f V) ∨ p
        So, `p ∨ (f U ≠ f V)`.
        Now, observe that if `p`, then `U = V = 2`, whence `f U = f 2 = f V`;
        Thus, `p → f U = f V`, and by the constructive direction of contraposition (`∀ (a b : Prop), (a → b) → (¬ b → ¬ a)`; applying a represented functor lol),
         we have `f U ≠ f V → ¬p`.
        Combining this with `p ∨ (f U ≠ f V)` yields `p ∨ ¬p`, as desired.
      -/
  #print axioms diaconescu -- *`'diaconescu' does not depend on any axioms`* :)

  -- NOTE: The upshot of this exposition is that **`Classical.choice`** is really the
  --  "fundamental" axiom in classical logic, at least in Lean (not `Classical.em`!).
end haha_prelude
