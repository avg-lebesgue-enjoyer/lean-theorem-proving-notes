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
          (_ : ∀ (y : α), r y x' → Acc r y)
          (ih : (y : α) → r y x' → C y)
        => F x' ih
  end woof
  end woof

  -- hmm, not sure what the theory behind `noncomputable` is...
  -- After doing a *tiny* bit of research, it seems like it's about the
  --  difference between producing "computed" bytecode (used for `#eval`
  --  and program evaluation) vs. being able to reduce λcalc expressions
  --  anyway (i.e. `#reduce`).
  -- This more-or-less stems from using principles of classical logic that
  --  don't compute, like `Classical.em : ∀ (p : Prop), p ∨ ¬p`. To alleviate
  --  my concern, **the logic done by Lean doesn't need to go to `#eval`uation**
  --  **and it's okay if a theorem or smth is `noncomputable`**; we just care
  --  that *code* is, of course, still computable.
  -- `noncomputable` stuff can still be `#reduce`d, but not always `#eval`ed.
  section woof2
    open Nat
    theorem lem_divF_decreases -- this Frankenstein's monster is me not looking at the @src and trying on my own, pestering the Lean stdlib whenever I found something useful
      {x y : Nat}
      (h : 0 < y  ∧  y ≤ x)
      : x - y < x
      := by
        induction y
        case zero => simp at h
        case succ y ih =>
        simp at h
        cases x
        case zero => contradiction
        case succ x =>
        simp at *
        cases y
        case zero => simp
        case succ y =>
        simp at *
        have : y ≤ x := calc y
          _ ≤ y + 1 := by simp
          _ ≤ x     := h
        have gaming : x - y < x + 1 := ih this
        show x - (y + 1) < x + 1
        calc x - (y + 1)
          _ = x - y - 1 := by
            cases x
            case zero => rfl
            case succ x =>
            simp [Nat.add_sub_sub_add_right x y 0 1]
          _ ≤ x - y     := by simp
          _ < x + 1     := gaming
    theorem lem_divF_decreases' -- This is what @src does. It's more clean, but I don't know the Lean stdlib inside-out, unfortunately
      {x y : Nat}
      (h : 0 < y  ∧  y ≤ x)
      : x - y < x
      := by
        apply Nat.sub_lt
        · exact Nat.lt_of_lt_of_le h.left h.right
        · exact h.left
    def div.F -- Iteration loop to use in fixed point lemma
      (x : Nat)
      (f : (x' : Nat) → x' < x → Nat → Nat)
      (y : Nat)
      : Nat
      := if h : 0 < y ∧ y ≤ x
        then f (x - y) (lem_divF_decreases h) y + 1
        else 0
    noncomputable def div := WellFounded.fix (measure id).wf div.F
      -- NOTE: `measure : {α : Sort u} → (α → Nat) → WellFoundedRelation α`
      #check measure
      -- NOTE: `WellFoundedRelation.wf : ∀ {α : Sort u} [WellFoundedRelation α], WellFounded WellFoundedRelation.rel`
      #check WellFoundedRelation.wf
    #reduce div 8 2
    -- `#eval div 8 2` -- *failed to compile definition, consider marking it as 'noncomputable' because it depends on 'div', and it does not have executable code*

    -- example (x y : Nat)
    --   : div x y = if 0 < y ∧ y ≤ x
    --               then div (x - y) y + 1
    --               else 0
    --   := by
    --     conv => lhs ; unfold div
    -- example (x y : Nat) (h : 0 < y ∧ y ≤ x)
    --   : div x y = div (x - y) y + 1
    --   := by
    --   conv => lhs ; unfold div
    --   simp [h]
  end woof2

  section nat_2_bin
    def natToBin : Nat → List Nat
      | 0 => [0]
      | 1 => [1]
      | n + 2 =>
        let rec coles (x : Nat) : (x + 2) / 2 < x + 2 -- hint to implicit `termination_by` to use this proof that the recursive call decreases. Lean is smart enough to use `gaming n` as the proof for the `decreases_by` tactic
          := by
            simp [Nat.lt_succ]
            match x with
            | 0     => show 0 ≤ 0 ; apply Nat.le_of_eq ; rfl
            | 1     => simp
            | x + 2 => apply Nat.le_of_lt ; exact coles x
        natToBin ((n + 2) / 2) ++ [n % 2]
    #eval! natToBin 1234
  end nat_2_bin

  section ack
    def ack : Nat → Nat → Nat
      | 0    , y      => y + 1
      | x + 1, 0      => ack x 1
      | x + 1, y + 1  => ack x $ ack (x + 1) y
    -- Lean infers `termination_by x y => (x, y)`; the lexicographic order on `Nat × Nat`
  end ack

  section takeWhile
    def takeWhile (p : α → Bool) (as : Array α) : Array α := go 0 #[]
    where
      go (i : Nat) (arr : Array α) : Array α :=
        if h_index_ok : i < as.size then
          let a := as.get ⟨i, h_index_ok⟩
          if p a then
            go (i + 1) (arr.push a)
          else arr
        else arr
      termination_by as.size - i -- You give actual parameters of stuff that moves! btw, Lean is smart enough to infer this one itself
  end takeWhile
end woof



/- SECTION: Mutual Recursion -/
-- This is what you think it is



/- SECTION: Dependent Pattern Matching -/
section dep_match
  -- sus
end dep_match
