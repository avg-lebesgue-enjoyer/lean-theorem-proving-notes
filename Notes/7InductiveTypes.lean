/- @file Notes/7InductiveTypes.lean
 - @src https://lean-lang.org/theorem_proving_in_lean4/inductive_types.html#enumerated-types
 -/

/- SECTION: Enumerated Types -/
section enums_lol
  inductive Weekday : Type where
    | monday : Weekday | tuesday : Weekday | wednesday : Weekday -- cba to do more
    deriving Repr
  -- Introduction rules (constructors):
  --  *`monday    : Weekday`*
  --  *`tuesday   : Weekday`*
  --  *`wednesday : Weekday`*
  -- Elimination rule (catamorphism):
  #check Weekday.rec
  --  *`.{u} : {motive : Weekday → Sort u} → motive monday → motive tuesday → motive wednesday → (t : Weekday) → motive t`*

  namespace Weekday
    def next : Weekday → Weekday
      | monday    => tuesday
      | tuesday   => wednesday
      | wednesday => monday
    def previous : Weekday → Weekday
      | monday    => wednesday
      | tuesday   => monday
      | wednesday => tuesday
    example : next (previous tuesday) = tuesday := rfl
    def all_weekdays : ∀ (w : Weekday), w.previous.next = w := by
      intro w
      cases w <;> rfl
    #print all_weekdays
  end Weekday
end enums_lol



/- SECTION: Constructors with Arguments -/
section constructors_with_arguments
  structure Semigroup.{u} : Type (u + 1) where
    carrier : Type u
    mul : carrier → carrier → carrier
    mul_assoc : ∀ (a b c : carrier), mul (mul a b) c = mul a (mul b c)
  #check Semigroup
  #print Semigroup
  -- ^^ same as vv
  inductive Semigroup'.{u} : Type (u + 1) where
    | mk : (carrier : Type u) → (mul : carrier → carrier → carrier) → (mul_assoc : ∀ (a b c : carrier), mul (mul a b) c = mul a (mul b c)) → Semigroup'
  #check Semigroup'
  #print Semigroup'
end constructors_with_arguments



/- SECTION: Inductively Defined Propositions -/
section ind_def_prop
namespace ind_def_prop
  inductive False : Prop
  inductive True : Prop where
    | intro : True
  inductive And (a b : Prop) : Prop where
    | intro : a → b → And a b
  inductive Or (a b : Prop) : Prop where
    | inl : a → Or a b
    | inr : b → Or a b
  inductive Exists.{u} {α : Sort u} (p : α → Prop) : Prop where
    | intro (w : α) (pf : p w) : Exists p

  inductive Subtype.{u} {α : Type u} (p : α → Prop) where
    | mk : (x : α) → p x → Subtype p
    -- This could be a `structure` instead, much like `True`, `And` and `Exists`.
end ind_def_prop
end ind_def_prop



/- SECTION: Nat -/
section the_nat
  inductive Nat' : Type where
    | zero : Nat'
    | succ : Nat' → Nat'
    deriving Repr, BEq
  namespace Nat'
    #print Nat.rec
    #check @Nat.rec -- catamorphism
    -- *`: {motive : Nat → Sort u}                      `* **motive** for elimination/recursion
    -- *`→ motive Nat.zero                              `* **minor premise** for constructor `Nat.zero`
    -- *`→ ((n : Nat) → motive n → motive (Nat.succ n)) `* **minor premise** for constructor `Nat.succ`
    -- *`→ (t : Nat)                                    `* **Major premise** for recursion
    -- *`→ motive t                                     `*
    -- NOTE: `.recOn` is a version of `.rec` but with the Major premise before the minor premises.
    #check @Nat.recOn

    -- Recursively defined function
    def add (x : Nat') : Nat' → Nat'
      | .zero   => x
      | .succ y => .succ $ add x y
    #print add

    instance : Add Nat' where add := add

    theorem add_zero (x : Nat') : x + Nat'.zero = x := rfl
    theorem add_succ (x y : Nat') : x + succ y = succ (x + y) := rfl

    -- Proof by induction! We just replace the `motive` by `Prop` :)
    theorem zero_add (x : Nat') : zero + x = x :=
      match x with
      | zero    => rfl
      | succ x' =>
        by
          show add zero (succ x') = succ x'
          simp [add]
          exact zero_add x'
        -- This is more explicit and works too:
        -- `by`
        -- `  show add zero (Nat'.succ x') = Nat'.succ x'`
        -- `  calc zero.add x'.succ`
        -- `    _ = Nat'.add zero x'.succ := rfl`
        -- `    _ = succ (Nat'.add zero x') := rfl`
        -- `    _ = succ x' := congrArg succ $ zero_add x'` -- use of inductive hypothesis
    -- A nicer example use
    theorem zero_add' (x : Nat') : zero + x = x :=
      Nat'.recOn (motive := fun y => zero + y = y) x
        rfl
        $ fun y : Nat' =>
          fun ih : zero + y = y =>  -- inductive hypothesis
          -- *`⊢ zero + succ y = succ y`*
          by simp [add_succ, ih]

    theorem add_assoc (x y z : Nat') : (x + y) + z = x + (y + z) :=
      Nat'.recOn (motive := fun z' => (x + y) + z' = x + (y + z')) z
        (show (x + y) + zero = x + (y + zero) from rfl)
        $ fun z' : Nat' =>
          fun ih : (x + y) + z' = x + (y + z') =>
          show (x + y) + succ z' = x + (y + succ z') from
          -- lhs
          have : (x + y) + succ z' = succ ((x + y) + z') := rfl
          have lhs_eq_canon : (x + y) + succ z' = succ (x + (y + z')) :=
            this.trans (congrArg succ ih)
          -- rhs
          have : x + (y + succ z') = x + (succ $ y + z') :=
            congrArg (x + ·) rfl
          have rhs_eq_canon : x + (y + succ z') = succ (x + (y + z')) :=
            this.trans rfl
          -- Stitch together
          lhs_eq_canon.trans rhs_eq_canon.symm
    -- With tactics
    theorem add_assoc' (x y z : Nat') : (x + y) + z = x + (y + z) :=
      Nat'.recOn (motive := fun z' => (x + y) + z' = x + (y + z')) z
        rfl
        $ by
          intros
          simp [Nat'.add_succ]
          assumption

    -- Let's prove commutativity of addition
    theorem succ_add (x y : Nat') : succ x + y = succ (x + y) :=
      match y with
      | zero => rfl
      | succ y' => by
        simp [Nat'.add_succ, succ_add x y']
    -- Okay here it is
    theorem add_comm (x y : Nat') : x + y = y + x :=
      match y with
      | zero    => by rw [add_zero, zero_add]
      | succ y' => by rw [add_succ, succ_add, add_comm x y']
  end Nat'
end the_nat



/- SECTION: Other Recursive Data Types -/
section other_rec_dts
namespace other_rec_dts
  inductive List (α : Type u) : Type u where
    | nil   : List α
    | cons  : α → List α → List α

  namespace List
    def append (as bs : List α) : List α :=
      match as with
      | nil => bs
      | cons a as' => cons a (append as' bs)

    theorem nil_append (as : List α) : append nil as = as := rfl

    theorem cons_append
      (a : α) (as bs : List α)
      : append (cons a as) bs = cons a (append as bs)
      := rfl

    theorem append_nil : (as : List α) → append as nil = as
      | nil       => rfl
      | cons a as => by rw [cons_append, append_nil as]

    theorem append_assoc
      (as bs cs : List α)
      : (as.append bs).append cs = as.append (bs.append cs)
      :=
        match as with
        | nil => by
          rw [nil_append, nil_append]
        | cons a as => by
          rw [cons_append, cons_append, append_assoc as, cons_append]

    def length : List α → Nat
      | nil => 0
      | cons _ as => 1 + length as

    theorem length_hom
      (as bs : List α)
      : (as.append bs).length = as.length + bs.length
      :=
      match as with
      | nil => by
        rw [nil_append, length, Nat.zero_add]
      | cons a as => by
        rw [cons_append, length, length, length_hom, Nat.add_assoc]
  end List

  inductive BinTree where
    | leaf : BinTree
    | node : BinTree → BinTree → BinTree

  inductive CountableTree where
    | leaf : CountableTree
    | sup  : (Nat → CountableTree) → CountableTree

  namespace CountableTree
    def succ (t : CountableTree) : CountableTree :=
      sup (fun _ => t)

    def toCountableTree : Nat → CountableTree
      | 0     => leaf
      | n + 1 => succ $ toCountableTree n

    def omega : CountableTree :=
      sup toCountableTree
  end CountableTree
end other_rec_dts
end other_rec_dts
