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
namespace ofn
  structure Rational where
    numerator   : Int
    denominator : Nat
    isLegal     : denominator ≠ 0
  scoped instance : OfNat Rational n where
    ofNat := ⟨n, 1, fun h => nomatch h⟩
  instance : ToString Rational where
    toString r := s!"{r.numerator} / {r.denominator}"
  #eval (2 : Rational) -- *`2 / 1`*
  #check (nat_lit 2)   -- *`2 : Nat`*; NOTE: `nat_lit n` gives you the non-polymorphic "raw" `n : Nat`

  class Monoid (α : Type u) where
    unit : α
    mul  : α → α → α
  instance [inst : Monoid α] : Mul α where mul := inst.mul
  instance [inst : Monoid α] : OfNat α 1 where ofNat := inst.unit
  def getUnit [Monoid α] : α := 1 -- This gives back the instance's `unit`
end ofn
end ofn



/- SECTION: `outParam`s -/
section outp
namespace outp
  -- NOTE: The `outParam (Type u'')` here says, more-or-less, that synthesizing
  --       `γ` should be deferred until as late as possible whenever a `HMul`
  --       instance is used.
  -- To explain the mnemonic a bit, `γ` is an *`out`put* `Param`eter from the
  --  typeclass synthesizer, not an input to it.
  class HMul (α : Type u) (β : Type u') (γ : outParam (Type u'')) where
    hMul : α → β → γ
  instance [self : Mul α] : HMul α α α where hMul := self.mul
  instance [self : Mul α] : HMul α (Array α) (Array α) where hMul s xs := xs.map (self.mul s)
  #eval HMul.hMul 4 #[2, 3, 4] -- Here, the typeclass synthesizer synthesizes `γ`
                               --  to be `Nat`.
end outp
end outp



/- SECTION: Default Instances -/
section default_instances
namespace outp
  open ofn

  export HMul (hMul)
  #check hMul

  @[default_instance]
  instance : HMul Int Int Int where
    hMul := Int.mul
  -- Now, whenever the typeclass synthesizer is stuck with an instance of `HMul`,
  --  and it knows that some argument is `Int`, it'll try to fill in the other
  --  arguments as `Int`.
  def example_xs : List Int := [1, 2, 3]
  #check fun y => example_xs.map (hMul · y) -- Inferred the first and third `Int`s in `hMul : Int → Int → Int` from the second `Int`

  -- NOTE: The following are default instances:
  --    `OfNat Nat n` with priority `100`
  --      (so that when talking about `Nat`s, we can just write `0` and `1` instead of `(0 : Nat)` etc.)
  --    homogeneous operations are default instances of hetero. ones

  -- NOTE: Higher-priority default instances get used before lower-priority default
  --        instances. For example, below, we infer `2 : Rational` by default
  @[default_instance 200] -- `200` is higher than the priority of the `@[default_instance 100] instance : OfNat Nat n`
  scoped instance : OfNat Rational n where
    ofNat := { numerator := n, denominator := 1, isLegal := by simp }
  #check 2 -- *`2 : Rational`*
end outp

-- Here's how Lean does `*` under the hood
namespace shitpost
  class OfNat (α : Type u) (n : Nat) where
    ofNat : α

  @[default_instance] -- *lowest priority*
  instance (n : Nat) : OfNat Nat n where
    ofNat := n

  class HMul (α : Type u) (β : Type u') (γ : outParam (Type u'')) where
    hMul : α → β → γ

  class Mul (α : Type u) where
    mul : α → α → α

  @[default_instance 10] -- Higher priority than the lowest-priority `instance (n : Nat) : OfNat Nat n`
  instance [Mul α] : HMul α α α where
    hMul a b := Mul.mul a b

  infixl:70 " * " => HMul.hMul

  -- Because the `instance [Mul α] : HMul α α α` has higher instance than
  --  `instance (n : Nat) : OfNat Nat n`, expressions like
  def example_xs : List Int := [1, 2, 3]
  #check (example_xs.map (2 * ·) : List Int)
  --  resolve to using `2 : Int`, not the default instance `2 : Nat`.
end shitpost
end default_instances



/- SECTION: Local Instances -/
section local_instances
  structure Point where (x : Nat) (y : Nat)
  section omg
    -- NOTE: This `instance` is scoped to this `section omg` thanks to the `local`.
    local instance : Add Point where
      add p q := ⟨p.x + q.x, p.y + q.y⟩
    def double (p : Point) := p + p
  end omg
  -- The `+` in the below causes a `cannot synthesize instance` error:
  --    `#eval ({ x := 1, y := 2 : Point } + { x := 3, y := 4 : Point})`
  -- Meanwhile, `double` is fine:
  #eval double ⟨1, 2⟩

  section omg
    local instance addPoint : Add Point where add p q := ⟨p.x + q.x, p.y + q.y⟩
    def funny_p : Point := ⟨1, 2⟩
    def funny_q : Point := ⟨3, 4⟩

    #eval funny_p + funny_q

    attribute [-instance] addPoint -- Disables the inference of the `instance addPoint`
                                   --  for the remainder of this `section` (or `namespace`,
                                   --  if that were the scoping block).
    -- `#eval funny_p + funny_q` -- Cannot synthesize instance
  end omg
end local_instances



/- SECTION: Scoped Instances -/
-- Okay, these exist, but I just don't really care...



/- SECTION: `Decidable` Propositions -/
section decidable_props_lol
  -- NOTE: A `Decidable` proposition is one that is *computationally* known to be not true,
  --        or one that is *computationally* known to be true.
  class inductive Decidable' (p : Prop) where
    | isFalse (h : ¬p) : Decidable' p
    | isTrue  (h :  p) : Decidable' p

  #print ite
  /-
    *`def ite.{u}           `*  -- This is what gets called when `if _ then _ else _` is used in code
    *`  : {α : Sort u}      `*
    *`  → (c : Prop)        `*  -- `if c`
    *`  → [h : Decidable c] `*  -- *computational* knowledge of whether of not `c` is true
    *`  → α                 `*  -- `then` branch
    *`  → α                 `*  -- `else` branch
    *`  → α                 `*
    *`  := fun {α} c [h : Decidable c] t e => Decidable.casesOn h (fun x => e) fun x => t `*
  -/
  #print dite -- `d`ependent version, where we can use the proof `h` given to us by `[h : Decideable c]` in the `then` and `else` branches

  -- NOTE: There are lots of instance chains about decidability
  set_option pp.proofs true
  #print instDecidableAnd -- *`: [Decidable p] → [Decidable q] → Decidable (p ∧ q)`*
  #print instDecidableAnd.proof_1
  #print instDecidableAnd.proof_2

  #print instDecidableOr -- *`: [Decidable p] → [Decidable q] → Decidable (p ∨ q)`*

  #print instDecidableNot -- *`: [Decidable p] → Decidable (¬p)`*

  #print DecidableEq
  #print instDecidableEqNat -- *`: DecidableEq Nat`*
  #print Nat.decEq
  set_option pp.proofs false

  def step (a b x : Nat) : Nat :=
    if x < a ∨ b < x then 0 else 1
  set_option pp.explicit true
  #print step -- the long-ass last argument here is the inferred decidability `a b x : Nat ⊢ Decidable (x < a ∨ b < x)`
  set_option pp.explicit false

  -- NOTE: Thanks to the `Classical` law of the `e`xcluded `m`iddle (`Classical.em`), if we assume `Classical` logic, then
  --        every `Prop` is `Decidable`:
  section wow
  namespace wow
    open Classical in
    noncomputable scoped instance (priority := low) propDecidable (p : Prop) : Decidable p :=
      choice $ match em p with
      | Or.inl h_p  => ⟨Decidable.isTrue  h_p⟩
      | Or.inr h_np => ⟨Decidable.isFalse h_np⟩
      -- NOTE: `Classical.choice.{u} : ∀ α : Sort u, Nonempty α → α` is used to construct the **data** of `Decidable p : Type`
      --        from just the **proof** that `Nonempty (Decidable p) : Prop`. This is necessary because we can only use the
      --        `Or.elim`inator from `Classical.em p` to `elim`inate into `Prop`, but `Decidable p` is not of type `Prop`.

    -- The `scoped` in the above means that this instance can only be used in `namespace wow`.
  end wow
  end wow

  -- NOTE: The `decide` tactic uses typeclass synthesization to try and find an `instance Decidable goal` (where `goal` is the goal to be proven),
  --        and then *if* the instance `isTrue`, the tactic closes the goal
  example : (10 : Nat) < 5 ∨ (1 : Nat) > 0 := by decide
  example : ¬ (True ∧ False) := by decide
  example : (10 : Nat) * (20 : Nat) = 200 := by decide
  -- These two functions are what `by decide` uses under the hood
  #print decide
  #print of_decide_eq_true
end decidable_props_lol



/- SECTION: The rest -/
-- The rest of this part of the `@src` was stuff that I already knew from `Functional Programming in Lean4`,
--  or that had already appeared in this chapter of the `@src`. There were no exercises at the end of the chapter.
