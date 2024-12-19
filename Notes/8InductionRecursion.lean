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
  -- NOTE: `let rec` can be used in tactic mode
  namespace List
    def replicate'.{u} {α : Type u} (n : Nat) (a : α) : List α :=
      let rec loop : Nat → List α → List α
        | 0, as       => as
        | .succ n, as => loop n (a :: as)
      ; loop n []
    theorem length_replicate'.{u}
      {α : Type u}
      (n : Nat) (a : α)
      : (replicate' n a).length = n
      := by
        let rec aux
          (n : Nat)
          (as : List α)
          : (replicate'.loop a n as).length = n + as.length
          := by
            match n with
            | 0       => simp [replicate'.loop]
            | .succ n => simp [replicate'.loop, aux] ; simp_arith
        exact aux n []
  end List

  -- NOTE: "postfix" `where` is the same as "prefix" `let rec`.
  --       Syntax is exactly the same as Haskell.
end the_let_rec



/- SECTION: Well-Founded Recursion and Induction -/
section woof
  #print Acc
  /-
    *`inductive Acc.{u} : {α : Sort u} → (α → α → Prop) → α → Prop  `*
    *`number of parameters: 2                                       `*
    *`constructors:                                                 `*
    *`Acc.intro : ∀ {α : Sort u} {r : α → α → Prop} (x : α),        `*
    *`  (∀ (y : α), r y x → Acc r y) → Acc r x                      `*
  -/
  -- If you think of `r` as an order relation, then `Acc r x` is the satement
  --  "`x` is accessible_`r` from below"; i.e. all of `x`'s predecessors are
  --  accessible.
  -- For example, if `r := Nat.lt`, then every `Nat` is accessible.

  #print WellFounded
  /-
    *`inductive WellFounded.{u} : {α : Sort u} → (α → α → Prop) → Prop  `*
    *`number of parameters: 2                                           `*
    *`constructors:                                                     `*
    *`WellFounded.intro : ∀ {α : Sort u} {r : α → α → Prop},            `*
    *`  (∀ (a : α), Acc r a) → WellFounded r                            `*
  -/
  -- A binary relation `r : α → α → Prop` is **well-founded** just when every term
  --  `a : α` is `Acc r a`essible.

  -- NOTE: `WellFounded.fix` is a way to define functions *out* of a type `α`
  --       which admits a `WellFounded` relation `r`.
  /-
    *`def WellFounded.fix.{u, v}                    `*
    *`  : {α : Sort u}                              `*
    *`  → {C : α → Sort v}                          `*  -- Where we're defining a function out to (perhaps dependent on the input, which defines a dependent function)
    *`  → {r : α → α → Prop}                        `*  -- The relation we're using
    *`  → WellFounded r                             `*  --  ^^ which must be well-founded
    *`  → ((x : α) → ((y : α) → r y x → C y) → C x) `*  -- A recursion principle:
    *`                                              `*  --  given `x : α` and a way to construct a term `C y` of each predecessor (`r y x`) of `x`,
    *`                                              `*  --  a construction of a term `C x`.
    *`  → (x : α) → C x                             `*  -- Conclusion: the (dependent) function we were after
    *`  :=                                          `*
    *`    fun {α} {C} {r} hwf F x =>                `*
    *`      WellFounded.fixF F x (WellFounded.apply hwf x)  `*
  -/
  #print WellFounded.fix
  /-
    *`def WellFounded.fixF.{u, v}                   `*
    *`  : {α : Sort u}                              `*  -- Where did we come from
    *`  → {r : α → α → Prop}                        `*
    *`  → {C : α → Sort v}                          `*  -- Where did we go *(`C`odomain)*
    *`  → ((x : α) → ((y : α) → r y x → C y) → C x) `*  -- Recursion principle
    *`  → (x : α) → Acc r x → C x                   `*  -- Conclusion: A function defined on all `r`-*accessible* elements
    *`  := fun {α} {r} {C} F x a => Acc.rec (fun x₁ h ih => F x₁ ih) a  `*
  -/
  #print WellFounded.fixF

  /- SECTION: I'm gonna implement those myself for a bit... -/
  section woof
  namespace woof
    inductive Acc.{u} {α : Sort u} (r : α → α → Prop) : α → Prop where
      | intro : (x : α) → (∀ y : α, r y x → Acc r y) → Acc r x -- `x` is `<`-accessible just when `∀ y : α . y < x, y is <-accessible`.
    inductive WellFounded.{u} {α : Sort u} (r : α → α → Prop) : Prop where
      | intro : (∀ x : α, Acc r x) → WellFounded r  -- `r` is well-founded just when `∀ x : α, x is r-accessible`.
    set_option pp.all true
    #print WellFounded.rec
    /-
    ⊢ {α : Type u}
    → {r : α → α → Prop}
    → {motive : (a : α) → @woof.Acc.{u} α r a → Sort u_1}
    → ((x : α)
        → (h : ∀ (y : α), r y x → @woof.Acc.{u} α r y)
        → ((y : α) → (h_ryx : r y x) → motive y (h y h_ryx))
        → motive x (@woof.Acc.intro.{u} α r x h))
    → {a : α}
    → (t : @woof.Acc.{u} α r a) → motive a t
    -/
    #print Acc.rec
    set_option pp.all false
    -- def WellFounded.fix.{u_src, u_tgt}
    --   {α : Type u_src}
    --   {C : α → Sort u_tgt}
    --   {r : α → α → Prop}
    --   (h_wf : WellFounded r)
    --   (recurse : (x : α) → ((y : α) → r y x → C y) → C x)
    --   : (x : α) → C x
    --   := by
    --     intro x
    --     cases h_wf with
    --     | intro h =>
    --     have h_acc_x : Acc r x := h x
    --     cases h_acc_x ; case intro.intro =>
    --       rename_i h_all_under_x_acc
    --       apply recurse
    --       intros y h_r_y_x
    --       apply WellFounded.fix
    --       case a.r =>
    --         exact r
    --       case a.h_wf =>
    --         apply WellFounded.intro
    --         assumption
    --       case a.recurse =>
    --         intro a
    --         intro gamer
    --         -- this shit's hard
    --         admit

    -- def WellFounded.fixF.{u_src, u_tgt}
    --   {α : Type u_src}
    --   {r : α → α → Prop}
    --   {C : α → Sort u_tgt}
    --   (recurse : (x : α) → (∀ y : α, Acc r y → C y) → C x)
    --   : (x : α) → Acc r x → C x
    --   | x, .intro _ h_all_under_x_acc =>
    --     recurse x $ fun y h_acc_y =>
    --     _

    -- NOTE: Yeah so I failed...

    /-
      *`def WellFounded.fixF.{u, v}                   `*
      *`  : {α : Sort u}                              `*  -- Where did we come from
      *`  → {r : α → α → Prop}                        `*
      *`  → {C : α → Sort v}                          `*  -- Where did we go *(`C`odomain)*
      *`  → ((x : α) → ((y : α) → r y x → C y) → C x) `*  -- Recursion principle
      *`  → (x : α) → Acc r x → C x                   `*  -- Conclusion: A function defined on all `r`-*accessible* elements
    -/
    -- Why the *fuck* does this have to be `noncomputable`??!
    noncomputable def WellFounded.fixF.{u_src, u_tgt}
      {α : Sort u_src}
      {r : α → α → Prop}
      {C : α → Sort u_tgt}
      (F : (x : α) → ((y : α) → r y x → C y) → C x)
      (x : α)
      : Acc r x → C x
      -- | .intro _ (h : ∀ (y : α), r y x → Acc r y) =>
      --   let ih : (y : α) → r y x → C y :=
      --     fun y h_ryx =>
      --     WellFounded.fixF F y (h y h_ryx)
      --   ; F x ih
      := Acc.rec $
        fun
          (x' : α)
          (h : ∀ (y : α), r y x' → Acc r y)
          (ih : (y : α) → r y x' → C y)
        => F x' ih
  end woof
  end woof

  -- hmm
end woof
