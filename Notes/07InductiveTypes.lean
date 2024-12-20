/- @file Notes/07InductiveTypes.lean
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



/- SECTION: Inductive Tactics -/
section inductive_tactics
  -- NOTE: `cases` decomposes a term of an inductive type across its constructors.
  --       i.e. `cases n` is an "interactive" version of `match n`.
  example
    (p : Nat → Prop)
    (h_0 : p 0)
    (h_succ : ∀ n : Nat, p n.succ)
    : ∀ n : Nat, p n
    := by
      intro n
      cases n
      · assumption
      · apply h_succ
  -- `cases n` also rewrites apart anything that depends on `n`
  open Nat in
  example
    (n : Nat)
    (h_n_neq_0 : n ≠ 0)
    : succ (pred n) = n := by
      cases n
      case zero =>
        -- Importantly, `h_n_neq_0 : 0 ≠ 0` has been rewritten here
        simp ; contradiction -- alternatively, `apply absurd rfl h_n_neq_0`
      case succ n' =>
        rfl
  -- `cases` is based
  example
    (p : Nat → Prop)
    (h_0 : p 0)
    (h_succ : ∀ n : Nat, p n.succ)
    (x y : Nat)
    : p (x + 3 * y)
    := by
      cases x + 3 * y with -- This **`generalize`s** away the whole expression `x + 3 * y`; as such, it can become impossible to complete the proof thereafter
      | zero    => assumption
      | succ z  => apply h_succ

  example (x y : Nat) : x - y = 0  ∨  x ≠ y := by
    cases Decidable.em (x = y) with
    | inl h_x_eq_y =>
      rw [h_x_eq_y]
      apply Or.inl
      rw [Nat.sub_self]
    | inr h_x_neq_y =>
      apply Or.inr
      assumption

  -- NOTE: `induction t` uses the `.rec` catamorphism on a term `t` of some inductive type.
  --       That is, it performs a proof by inducting on `t`.
  theorem zero_add (n : Nat) : 0 + n = n := by
    induction n -- `case ⋯ =>` variant
    case zero => rfl
    case succ n' ih =>
      rw [Nat.add_succ, ih]
  theorem zero_add' (n : Nat) : 0 + n = n := by
    induction n with  -- `with | ⋯` variant
    | zero => rfl
    | succ n' ih => rw [Nat.add_succ, ih]
  theorem zero_add'' (n : Nat) : 0 + n = n := by
    induction n <;> simp [*] -- this one is cheating; there's a lot of facts about `Nat` that have the `attribute [simp]`

  open Nat in
  theorem succ_add (x y : Nat) : Nat.succ x + y = Nat.succ (x + y) := by
    induction y
    · rfl
    case succ y' ih =>
      rw [add_succ, add_succ, ih]

  open Nat in
  theorem add_comm (x y : Nat) : x + y = y + x := by
    induction y
    · rw [Nat.zero_add, Nat.add_zero]
    case succ y' ih =>
      rw [Nat.add_succ, ih, ←Nat.succ_add]

  open Nat in
  theorem add_assoc (x y z : Nat) : (x + y) + z = x + (y + z) := by
    induction z
    · rfl
    case succ z ih =>
      rw [Nat.add_succ, Nat.add_succ, Nat.add_succ, ih]
  -- NOTE: You can specify your own induction schemes too, but the source doesn't really say much about this.

  -- NOTE: `injection` is a tactic that uses injectivity of the constructors (true
  --        because the type is freely generated by syntax trees) to peel away
  --        matching constructors in `=` expressions
  open Nat in
  example
    (x y z : Nat)
    (h : succ (succ x) = succ (succ y))
    : y + z = x + z
    := by
      injection h with h' -- Replaces `h` with `h'`, where the injectivity of `succ` has been applied; `h' : ⊢ succ x = succ y`
      injection h' with h'' -- `h'' : x = y`
      rw [h'']
  -- `injection` also detects constructor mismatches, which are contradictions
  --  because constructors have disjoint images (true because of being freely
  --  generated by syntax trees)
  -- It then closes any goals upon detecting such a contradiction.
  open Nat in
  example
    (x y : Nat)
    (h : Nat.succ y = Nat.zero) -- Constructor mismatch! Contradicts freeness!
    : x = x + 7
    := by
      injection h
  -- `contradiction` also closes such contradictions
  open Nat in
  example
    (x y : Nat)
    (h : Nat.succ y = Nat.zero)
    : x = x + 7
    := by
      contradiction
  -- In fact, `contradiction` detects deeper-nester such contradictions
  example (h : 69 = 420) : False := by
    contradiction
end inductive_tactics



/- SECTION: Inductive Families -/
section inductive_families
  -- Dependent types!
  inductive Vector (α : Type u) : Nat → Type u where
    | nil  : Vector α 0
    | cons : α → {n : Nat} → Vector α n → Vector α (n + 1)

  -- NOTE: **The single most important use of this is the definition of equality:**
  inductive Eq' {α : Sort u} (a : α) : α → Prop where
    | refl : Eq' a a
  #check @Eq'.rec
    -- *`: {α : Sort u} → {a : α}                 `*  -- Data matching the diagram behind `Eq`
    -- *`→ {motive : (x : α) → a = x → Sort v}    `*  -- ^^
    --**`→ motive a rfl                           `** -- minor premise; You have a thing to get with the canonical constructor `rfl : a = a`
    -- *`→ {b : α} → (h : a = b)                  `*  -- Major premise; You have an `Eq a` (aka. `a = ·`)-term
    -- *`→ motive b h                             `*  -- conclusion;    The catamorphism gives you a thing from there
    -- NOTE: Importantly, the catamorphism says that
    --        **if you can get to your target type with `rfl : a = a`**,
    --        and if you know `h : a = b`,
    --        then you can get your target type with `h : a = b`.
    -- That's the path induction principle.

  namespace Eq'
    theorem subst
      {α : Type u}
      {a b : α}
      {p : α → Prop}
      (h_a_eq_b : Eq' a b)
      (h_pa : p a)
      : p b
      := match h_a_eq_b with  -- *by the universal property...*
         | refl => h_pa       -- *...we just need to know what to do if the proof were `refl`*
    theorem subst'
      {α : Type u}
      {a b : α}
      {p : α → Prop}
      (h_a_eq_b : Eq' a b)
      (h_pa : p a)
      : p b
      := h_a_eq_b.rec -- *according to the catamorphism...* (aka. the universal arrow)
          h_pa        -- *...we just need to know `p a`*

    theorem symm.{u}
      {α : Type u}
      {a b : α}
      (h_a_eq_b : Eq' a b)
      : Eq' b a :=
        match h_a_eq_b with
        | refl => refl

    theorem trans.{u}
      {α : Type u}
      {a b c : α}
      (h_a_eq_b : Eq' a b)
      (h_b_eq_c : Eq' b c)
      : Eq' a c
      := match h_a_eq_b, h_b_eq_c with
        | refl, refl => refl

    theorem congr.{u}
      {α β : Type u}
      {a b : α}
      (f : α → β)
      (h_a_eq_b : Eq' a b)
      : Eq' (f a) (f b)
      := match h_a_eq_b with
         | refl => refl
  end Eq'
end inductive_families



/- SECTION: Inductive Harder -/
section ind_harder
  -- NOTE: Mutual induction is what you think it is
  mutual
    -- Behind the scenes, this creates a product type and destructs from it, I think
    inductive Even : Nat → Prop where
      | zero_is_even : Even 0
      | succ_odd_is_even : (n : Nat) → Odd n → Even (n + 1)
    inductive Odd : Nat → Prop where
      | succ_even_is_odd : (n : Nat) → Even n → Odd (n + 1)
  end

  -- NOTE: hehe mutual recursion proofs are exactly what you think they are :D
  mutual
    theorem even_iff_0_mod_2
      (n : Nat)
      : Even n ↔ (∃ d : Nat, n = 2 * d)
      := by
        constructor
        case mp =>
          intro h_even_n ; cases h_even_n
          case zero_is_even => exists 0
          case succ_odd_is_even n' h_n' =>
          have ⟨d, h_d'⟩ := (odd_iff_1_mod_2 n').mp h_n'
          rw [h_d']
          simp_arith
          exists d + 1
        case mpr =>
          intro ⟨d, h_d⟩
          cases d
          · simp_arith at h_d
            rw [h_d]
            apply Even.zero_is_even
          case succ n' =>
          simp_arith at h_d
          have : Odd (2 * n' + 1) :=
            (odd_iff_1_mod_2 $ 2 * n' + 1).mpr (by exists n')
          rw [h_d]
          apply Even.succ_odd_is_even
          assumption

    theorem odd_iff_1_mod_2
      (n : Nat)
      : Odd n ↔ (∃ d : Nat, n = 2 * d + 1)
      := by
        constructor
        case mp =>
          intro h
          cases h with
          | succ_even_is_odd n' h_even_n' =>
            cases h_even_n'
            · exists 0
            · rename_i n' h_n'
              have ⟨d', h_d'⟩ : (∃ d' : Nat, n' = 2 * d' + 1) := (odd_iff_1_mod_2 n').mp h_n'
              exists d' + 1
              simp [h_d', Nat.mul_add]
        case mpr =>
          intro ⟨d, h_d⟩
          cases n
          · contradiction
          case succ n' =>
          apply Odd.succ_even_is_odd
          injection h_d with h_n'_eq_2d
          apply (even_iff_0_mod_2 n').mpr
          exists d
  end

  -- NOTE: You can also use *nested* types.
  section nested_hack
    -- We're doing this hack with `TreeList α` instead of using `List (Tree α)`
    --  because theoretically you can't use `List (Tree α)` with "inductive types"
    --  as they usually are.
    -- (We'll see momentarily that Lean bridges the hack we're about to do for us.)
    mutual
      inductive Tree (α : Type u) where
        | node : α → TreeList α → Tree α
      inductive TreeList (α : Type u) where
        | nil : TreeList α
        | cons : Tree α → TreeList α → TreeList α
    end

    -- We'll show that `TreeList α ≃ List (Tree α)`
    def f.{u} {α : Type u} : TreeList α → List (Tree α)
      | .nil        => []
      | .cons t ts  => t :: f ts
    def g.{u} {α : Type u} : List (Tree α) → TreeList α
      | []      => .nil
      | t :: ts => .cons t (g ts)
    -- Need to show that this is an isomorphism
    theorem lem_g_o_f_eq_id.{u} {α : Type u} : g ∘ f = id (α := TreeList α) :=
      -- Extracting this bit out so that we can explicitly recurse
      let rec lem_funexted (ts : TreeList α) : (g ∘ f) ts = id ts := by
        cases ts
        case nil => simp [g, f]
        case cons t ts =>
        simp [g, f]
        exact lem_funexted ts
      by apply funext ; exact lem_funexted
    theorem lem_f_o_g_eq_id.{u} {α : Type u} : f ∘ g = id (α := List (Tree α)) :=
      let rec lem_funexted (ts : List (Tree α)) : (f ∘ g) ts = id ts := by
        cases ts
        case nil => simp [g, f]
        case cons t ts =>
        simp [g, f]
        exact lem_funexted ts
      by apply funext ; exact lem_funexted
    theorem thm_TreeList_iso_List_Tree.{u}
      {α : Type u}
      : ∃ f : TreeList α → List (Tree α),
        ∃ g : List (Tree α) → TreeList α,
        f ∘ g = id  ∧  g ∘ f = id
      := by
        exists f
        exists g
        constructor
        apply lem_f_o_g_eq_id
        apply lem_g_o_f_eq_id

    -- Now that we know that `TreeList α ≃ List (Tree α)`, we can carry any results
    --  referencing `TreeList` to `List ∘ Tree` across the isomorphism.

    -- **Lean knows this hack, and it does it for us**, automatically adding the
    --  relevant isomorphism behind the scenes when we use the sugary `Tree'`:
    inductive Tree'.{u} (α : Type u) where
      | node : α → List (Tree' α) → Tree' α
  end nested_hack
end ind_harder



/- EXERCISES: (1) -/
section ex_1
namespace ligma
  inductive Nat : Type where
    | zero : Nat
    | succ : Nat → Nat
    deriving Repr
  instance : OfNat Nat 0 where ofNat := Nat.zero
  instance [OfNat Nat n] : OfNat Nat (.succ n) where ofNat := Nat.succ (OfNat.ofNat n)
  #eval (0 : Nat)
  #eval (1 : Nat)
  #eval (2 : Nat)
  namespace Nat
    -- We're gonna write `0` instead of `Nat.zero` very often, so this really helps.
    @[simp] theorem lem_zero_eq_zero      : zero      = 0 := rfl
    @[simp] theorem lem_succ_zero_eq_one  : succ zero = 1 := rfl

    /- SECTION: Addition -/
    def add (x : Nat) : Nat → Nat
      | zero    => x
      | succ y  => succ $ add x y
    instance : Add Nat where add := Nat.add
    @[simp] theorem lem_add_zero (x : Nat) : x + 0 = x := rfl -- For example, this result only goes through with `0`, not with `Nat.zero`; the `@[simp] theorem lem_zero_eq_zero` bridges the gap properly for us
    @[simp] theorem lem_add_succ (x y : Nat) : x + (succ y) = succ (x + y) := rfl

    @[simp] theorem lem_zero_add (x : Nat) : 0 + x = x := by
      induction x
      case zero => rfl
      case succ => simp [lem_add_succ] ; assumption
    @[simp] theorem lem_succ_add (x y : Nat) : (succ x) + y = succ (x + y) := by
      induction y
      case zero => rfl
      case succ => simp [lem_add_succ] ; assumption

    @[simp] theorem thm_add_assoc (x y z : Nat) : (x + y) + z = x + (y + z) := by
      induction z
      case zero => rfl
      case succ => simp [lem_add_succ] ; assumption
    -- hmm all these proofs have been the same lol

    theorem thm_add_comm (x y : Nat) : x + y = y + x := by
      induction y
      case zero => calc x + zero
        _ = x         := lem_add_zero x
        _ = zero + x  := (lem_zero_add x).symm
      case succ => simp [lem_add_succ, lem_succ_add] ; assumption

    theorem thm_add_right_cancel (c x y : Nat) : x + c = y + c → x = y := by
      intro h
      induction c
      case zero =>
        simp at h
        assumption
      case succ c ih =>
        simp at h
        exact ih h

    theorem thm_add_left_cancel (c x y : Nat) : c + x = c + y → x = y := by
      intro h
      apply thm_add_right_cancel c
      rw [thm_add_comm x, thm_add_comm y]
      assumption

    @[simp] theorem thm_add_zero_2_args_zero (x y : Nat) : x + y = 0 → x = 0 ∧ y = 0 := by
      intro h
      induction y
      case zero       => simp at * ; assumption
      case succ y ih  => injection h



    /- SECTION: Multiplication -/
    def mul (x : Nat) : Nat → Nat
      | zero    => zero
      | succ y  => mul x y + x
    instance : Mul Nat where mul := Nat.mul
    @[simp] theorem lem_mul_zero (x : Nat) : x * 0 = 0 := rfl
    @[simp] theorem lem_mul_succ (x y : Nat) : x * succ y = x * y + x := rfl

    @[simp] theorem lem_mul_one (x : Nat) : x * 1 = x := by
      rw  [←lem_succ_zero_eq_one
          , lem_mul_succ
          , lem_zero_eq_zero
          , lem_mul_zero
          , lem_zero_add
          ]

    @[simp] theorem lem_zero_mul (x : Nat) : 0 * x = 0 := by
      induction x
      case zero => rfl
      case succ => simp ; assumption

    @[simp] theorem lem_succ_mul (x y : Nat) : succ x * y = x * y + y := by
      induction y
      case zero       => simp
      case succ y ih  => simp [ih, thm_add_comm y x]

    @[simp] theorem thm_dist_mul_add (a x y : Nat) : a * (x + y) = a * x + a * y := by
      induction y
      case zero       => rfl
      case succ y ih  => simp [ih]

    @[simp] theorem thm_mul_assoc (x y z : Nat) : (x * y) * z = x * (y * z) := by
      induction z
      case zero       => rfl
      case succ z ih  => simp [ih]
    -- hmm same proof as the previous result

    theorem thm_mul_comm (x y : Nat) : x * y = y * x := by
      induction y
      case zero       => simp
      case succ y ih  => simp [ih]
    -- hmmmmm

    @[simp] theorem thm_dist_add_mul (a b x : Nat) : (a + b) * x = a * x + b * x := by
      simp [thm_mul_comm (a + b) x, thm_mul_comm x a, thm_mul_comm x b]

    @[simp] theorem thm_euc_dom (x y : Nat) : x * y = 0 → x = 0 ∨ y = 0 := by
      intro h
      induction y
      case zero => simp
      case succ y ih =>
      simp at h
      have : x * y = 0 ∧ x = 0 := by apply thm_add_zero_2_args_zero ; assumption
      have : x = 0 := this.right
      apply Or.inl ; assumption

    @[simp] theorem thm_mul_one_2_args_one (x y : Nat) : x * y = 1 → x = 1 ∧ y = 1 := by
      intro h
      induction y
      case zero => injection h
      case succ y ih =>
      -- *`⊢ x = 1 ∧ y.succ = 1`*
      simp at h
      cases x
      case zero => simp at h
      case succ x =>
      -- *`⊢ x.succ = 1 ∧ y.succ = 1`*
      simp [←lem_succ_zero_eq_one] at h
      have := thm_add_zero_2_args_zero _ _ h
      have h_y_eq_0__x__x_eq_0 := thm_add_zero_2_args_zero _ _ this.right
      have h_y_eq_0 : y = 0 := h_y_eq_0__x__x_eq_0.left
      have h_x_eq_0 : x = 0 := h_y_eq_0__x__x_eq_0.right
      rw [h_x_eq_0, h_y_eq_0]
      -- *`⊢ succ 0 = 1 ∧ succ 0 = 1`*
      constructor <;> rfl
  end Nat
end ligma
end ex_1



/- EXERCISES: (2) -/
section ex_2
namespace ligma
  inductive List.{u} (α : Type u) : Type u where
    | nil   : List α
    | cons  : α → List α → List α
    deriving Repr

  namespace List
    open Nat

    /- SECTION: ++ -/
    def append.{u} {α : Type u} (as bs : List α) : List α :=
      match as with
      | nil => bs
      | cons a as' => cons a (as'.append bs)
    instance {α : Type u} : Append (List α) where append := List.append
    @[simp] theorem lem_nil_append.{u}
      {α : Type u}
      (as : List α)
      : nil ++ as = as
      := rfl
    @[simp] theorem lem_cons_append.{u}
      {α : Type u}
      (a : α)
      (as bs : List α)
      : (cons a as) ++ bs = cons a (as ++ bs)
      := rfl

    @[simp] theorem lem_append_cons.{u}
      {α : Type u}
      (as : List α)
      : as ++ nil = as
      := by
        induction as
        case nil          => rfl
        case cons a as ih => simp [ih]

    @[simp] theorem thm_append_assoc.{u}
      {α : Type u}
      (as bs cs : List α)
      : (as ++ bs) ++ cs = as ++ (bs ++ cs)
      := by
      induction as
      case nil  => simp
      case cons => simp ; assumption

    /- SECTION: length -/
    def length.{u} {α : Type u} : List α → Nat
      | nil       => 0
      | cons _ as => 1 + as.length
    @[simp] theorem lem_length_nil.{u}
      {α : Type u}
      : (@nil α).length = 0 := rfl
    @[simp] theorem lem_length_cons.{u}
      {α : Type u}
      (a : α)
      (as : List α)
      : (cons a as).length = 1 + as.length
      := rfl

    @[simp] theorem thm_length_hom.{u}
      {α : Type u}
      (as bs : List α)
      : length (as ++ bs) = length as + length bs
      := by
      induction as
      case nil          => simp
      case cons a as ih => simp [ih]

    /- SECTION: reverse -/
    def reverse.{u} {α : Type u} : List α → List α
      | nil => nil
      | cons a as => as.reverse ++ (cons a nil)
    @[simp] theorem lem_reverse_nil : nil.reverse = (nil : List α) := rfl
    @[simp] theorem lem_reverse_cons.{u}
      {α : Type u}
      (a : α) (as : List α)
      : (cons a as).reverse = as.reverse ++ (cons a nil)
      := rfl

    theorem thm_length_reverse.{u}
      {α : Type u}
      (as : List α)
      : length (reverse as) = length as
      := by
        induction as
        case nil          => rfl
        case cons a as ih => simp [ih, thm_add_comm _ 1]

    theorem thm_reverse_append.{u}
      {α : Type u}
      (as bs : List α)
      : (as ++ bs).reverse = bs.reverse ++ as.reverse
      := by
        induction as
        case nil          => simp
        case cons a as ih => simp [ih]

    theorem thm_reverse_involution.{u}
      {α : Type u}
      (as : List α)
      : as.reverse.reverse = as
      := by
        induction as
        case nil          => rfl
        case cons a as ih => simp [thm_reverse_append, ih]
  end List
end ligma
end ex_2



/- EXERCISES: (3) -/
section ex_3
namespace sugoma
  inductive Expression : Type where
    | const : Nat → Expression
    | var : Nat → Expression
    | plus : Expression → Expression → Expression
    | times : Expression → Expression → Expression

  def Expression.evaluate (e : Expression) (vars : List Nat) : Option Nat :=
    match e with
    | .const c    => some c
    | .var v      => vars.get? v
    | .plus l r   => do
      let l' ← l.evaluate vars
      let r' ← r.evaluate vars
      pure $ l' + r'
    | .times l r  => do
      let l' ← l.evaluate vars
      let r' ← r.evaluate vars
      pure $ l' * r'
end sugoma
end ex_3
