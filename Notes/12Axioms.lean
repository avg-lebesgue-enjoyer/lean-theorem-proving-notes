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
    (propext : ∀ {p q : Prop}, (p ↔ q) → (p = q))
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
  -- It's still worth emphasising though that `Classical.choice` is what tells us that
  --  we can prove logical equivalences by reducing to boolean truth tables.
end haha_prelude



/- SECTION: `propext` -/
section the_propext
namespace the
  -- The axiom of `prop`ositional `ext`ensionality says exactly what you think
  --  it does: the (thin) `Prop` category (preorder) is skeletal.
  axiom propext {p q : Prop} : (p ↔ q) → (p = q)

  example (a b : Prop) (p : Prop → Prop) (h : a ↔ b)
    : p a → p b
    := (propext h ▸ ·)
end the
end the_propext



/- SECTION: `funext`-/
section the_funext
namespace the
  -- The axiom of `fun`ction `ext`ensionality says exactly what you think
  --  it does: the Yoneda lemma (/s; not really /s).
  #check funext

  def Set (α : Type u) : Type u := α → Prop
  namespace Set
    def mem (x : α) (a : Set α) := a x
    infix:50 (priority := high) " ∈ " => mem

    -- We can derive the (Z) axiom of extensionality for sets from `funext`
    --  and `propext`.
    theorem setext {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b :=
      funext (propext $ h ·)
    -- `setext` is really all we needed when we were trying to show `p → U = V`
    --  in `theorem diaconescu`.

    def empty : Set α := fun _ => False
    notation (priority := high) "∅" => empty

    def inter (a b : Set α) : Set α :=
      fun x => x ∈ a ∧ x ∈ b
    infix:70 " ∩ " => inter

    theorem inter_self (a : Set α) : a ∩ a = a :=
      setext $ fun _ => Iff.intro
        And.left
        (fun h => ⟨h, h⟩)
    theorem inter_empty (a : Set α) : a ∩ ∅ = ∅ :=
      setext $ fun _ => Iff.intro
        And.right
        (fun h : False => h.elim)
    theorem inter.comm (a b : Set α) : a ∩ b = b ∩ a :=
      setext $ fun _ => Iff.intro
        (fun ⟨l, r⟩ => ⟨r, l⟩)
        (fun ⟨l, r⟩ => ⟨r, l⟩)
    theorem empty_inter (a : Set α) : ∅ ∩ a = ∅ :=
      calc ∅ ∩ a
        _ = a ∩ ∅ := by apply inter.comm
        _ = ∅     := by apply inter_empty
  end Set
end the
end the_funext



/- SECTION: Quotients -/
section fav
  -- Given `r : α → α → Prop`, `Quot r` is a `Sort`.
  #print Quot -- *`Quotient primitive Quot.{u} : {α : Sort u} → (α → α → Prop) → Sort u`*
  -- Given `a : α`, `Quot.mk r a` is a term of type `Quot r`
  #print Quot.mk -- *`Quotient primitive Quot.mk.{u} : {α : Sort u} → (r : α → α → Prop) → α → Quot r`*
  -- The induction principle says that to prove a propositon `β` on all of `Quot r`, you need only prove it on each
  --  constructor return value `Quot.mk r a`.
  #print Quot.ind -- *`Quotient primitive Quot.ind.{u} : ∀ {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop}, `*
                  -- *` (∀ (a : α), β (Quot.mk r a)) → ∀ (q : Quot r), β q`*
  -- A function `f : α → β` which respects the relation `r` lifts to a function `Quot {α} r → β`. Interestingly, the
  --  codomain here is not dependent.
  #print Quot.lift -- *`Quotient primitive Quot.lift.{u_src, u_tgt} : {α : Sort u_src} {r : α → α → Prop} → {β : Sort u_tgt}`*
                   -- *`  → (f : α → β) → (∀ (a b : α), r a b → f a = f b) → Quot r → β`*

  -- Extensionality for quotients, basically. This is the axiom that says "`Quot` is a *quotient*".
  #print Quot.sound -- *`axiom Quot.sound.{u} : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Quot.mk r a = Quot.mk r b`*

  /- NOTE: Universal property of the quotient. Can't even be *stated* without `Quot.sound`!
    *`@[reducible] protected def Quot.rec.{u_src, u_tgt}              `*
    *`  : {α : Sort u_src}                                            `*
    *`  → {r : α → α → Prop}                                          `*
    *`  → {motive : Quot r → Sort u_tgt}                              `*
    *`  → (f : (a : α) → motive (Quot.mk r a))                        `*  -- We know what to do on each thing of the form `Quot.mk r a`
    *`  → (∀ (a b : α) (p : r a b), (Quot.sound p) ▸ f a = f b)       `*  -- ^^and that thing respects `r`
    *`  → (q : Quot r) → motive q                                     `*  -- ~> gives us a (dependent) function out of the quotient.
    *`  := fun {α} {r} {motive} f h q =>                              `*
    *`    Eq.ndrecOn (Quot.liftIndepPr1 f h q)                        `*
    *`      (Quot.lift (Quot.indep f) (Quot.indepCoherent f h) q).snd `*
  -/
  #print Quot.rec -- Not a "from on high" recursor; this depends on the axioms `Quot.sound` and other `Quotient primitive`s.
  #print Eq.ndrecOn
  #print Quot.indep

  section z_mod_7
  namespace z_mod_7
    def mod7 (x y : Nat) : Prop := x % 7 = y % 7 -- Kernel of `(· % 7)`
    #check Quot mod7 -- *`: Type`*
    #check (Quot.mk mod7 4) -- *`: Quot mod7`*

    def f (x : Nat) : Bool := x % 7 = 0 -- Identifies zero in the quotient
    theorem f_respects (a b : Nat) (h : mod7 a b) : f a = f b := by rw [f, f, h]
    #check Quot.lift f f_respects -- *`: Quot mod7 → Bool`*

    -- NOTE: `Quot.lift` does what it's supposed to do
    example (a : Nat) : Quot.lift f f_respects (Quot.mk mod7 a) = f a := rfl
    example
      {α : Sort u} {β : Sort u'}
      {r : α → α → Prop}
      (f : α → β)
      (h : ∀ (x y : α), r x y → f x = f y)
      : ∀ (x : α), Quot.lift f h (Quot.mk r x) = f x
      :=
        fun _ => rfl
  end z_mod_7
  end z_mod_7

  section erm_what_the_setoid
    -- A **Setoid** is a type ("set") with a specified equivalence relation of interest.
    class Setoid'.{u} (α : Sort u) where
      r : α → α → Prop
      iseqv : Equivalence r
    -- `Quotient`s are best behaved when they're by *equivalence* relations. Really, this just means that
    --  we don't need to wrap each mention of the underlying relation in a "make this a freely generated
    --  equivalence relation pls" whenever we state and prove results about `Quot`s.
    -- NOTE: `Quot r ≃ Quot (eqv. rel. freely gen. by r)` is really easy to see
    #print Quotient -- *`def Quotient.{u} : {α : Sort u} → Setoid α → Sort u := fun {α} s => Quot Setoid.r`*

    namespace Setoid'
      instance {α : Sort u} [Setoid' α] : HasEquiv α := ⟨Setoid'.r⟩ -- This supports the infix notation `≈` instead of prefix `Setoid.r`.
      variable {α : Sort u} [Setoid' α]

      theorem refl : ∀ (x : α), x ≈ x := iseqv.refl
      theorem symm : ∀ {x y : α}, x ≈ y → y ≈ x :=
        fun {x y : α} (h : x ≈ y) => iseqv.symm h
      theorem trans : ∀ {x y z : α}, x ≈ y → y ≈ z → x ≈ z :=
        fun {x y z : α} (h_xy : x ≈ y) (h_yz : y ≈ z) => iseqv.trans h_xy h_yz
    end Setoid'

    -- NOTE: `Quotient.mk`, `Quotient.sound` etc. are restrictions of `Quot.mk`, `Quot.sound` etc. to `Quotient`.

    -- NOTE: `⟦x⟧ := Quot.mk Setoid.r x`
    #print Quotient.exact -- *`: ∀ {α : Sort u} {s : Setoid α} {a b : α}, Quotient.mk s a = Quotient.mk s b → a ≈ b`*
  end erm_what_the_setoid

  section unordered_pairs
    private def squiggle {α : Type u} (p q : α × α) : Prop :=
      (p.1 = q.1 ∧ p.2 = q.2) ∨ (p.1 = q.2 ∧ p.2 = q.1)
    infix:50 " ~ " => squiggle

    private theorem squiggle.refl {α : Type u} : ∀ (p : α × α), p ~ p := fun _ => .inl ⟨rfl, rfl⟩
    private theorem squiggle.symm {α : Type u} : ∀ {p q : α × α}, p ~ q → q ~ p :=
      fun {_} {_} h =>
      match h with
      | .inl ⟨ll, rr⟩ => .inl ⟨ll.symm, rr.symm⟩
      | .inr ⟨lr, rl⟩ => .inr ⟨rl.symm, lr.symm⟩
    private theorem squiggle.trans {α : Type u} : ∀ {p q r : α × α}, p ~ q → q ~ r → p ~ r :=
      fun {_} {_} {_} h_pq h_qr =>
      match h_pq, h_qr with
      | .inl ⟨p1q1, p2q2⟩, .inl ⟨q1r1, q2r2⟩ => .inl ⟨p1q1.trans q1r1, p2q2.trans q2r2⟩
      | .inl ⟨p1q1, p2q2⟩, .inr ⟨q1r2, q2r1⟩ => .inr ⟨p1q1.trans q1r2, p2q2.trans q2r1⟩
      | .inr ⟨p1q2, p2q1⟩, .inl ⟨q1r1, q2r2⟩ => .inr ⟨p1q2.trans q2r2, p2q1.trans q1r1⟩
      | .inr ⟨p1q2, p2q1⟩, .inr ⟨q1r2, q2r1⟩ => .inl ⟨p1q2.trans q2r1, p2q1.trans q1r2⟩
    private theorem squiggle.is_equivalence {α : Type u} : Equivalence (@squiggle α) :=
      { refl := squiggle.refl, symm := squiggle.symm, trans := squiggle.trans }

    instance unorderedPairSetoid (α : Type u) : Setoid (α × α) where
      r := squiggle ; iseqv := squiggle.is_equivalence
    def UnorderedPair (α : Type u) : Type u := Quotient (unorderedPairSetoid α)
    namespace UnorderedPair
      def mk {α : Type u} (a b : α) : UnorderedPair α := Quotient.mk' (a, b)
      local notation "{ " p ", " q " }" => mk p q

      theorem mk_swap {α : Type u} : ∀ (a b : α), {a, b} = {b, a} :=
        fun a b => Quotient.sound (show (a, b) ~ (b, a) from Or.inr ⟨rfl, rfl⟩)

      private def mem_fn {α : Type u} (a : α) : α × α → Prop
        | (x, y) => x = a ∨ y = a
      private theorem mem_swap {α : Type u} {a : α} : ∀ {p : α × α}, mem_fn a p = mem_fn a ⟨p.2, p.1⟩
        | ⟨p1, p2⟩ => by
          apply propext
          constructor <;> (rw [mem_fn, Or.comm] ; exact id)
      private theorem mem_respects
        {α : Type u}
        {p q : α × α}
        (a : α)
        : p ~ q → mem_fn a p = mem_fn a q
        | .inl ⟨p1q1, p2q2⟩ => by simp_all [mem_fn]
        | .inr ⟨p1q2, p2q1⟩ => by have : q = ⟨p.snd, p.fst⟩ := (by simp_all) ; rw [this] ; apply mem_swap

      def mem {α : Type u} (a : α) : UnorderedPair α → Prop :=
        Quot.lift (mem_fn a) (fun _ _ e => mem_respects a e)
      infix:50 (priority := high) " ∈ " => mem
      theorem mem_mk_left  {α : Type u} (a b : α) : a ∈ {a, b} := Or.inl rfl
      theorem mem_mk_right {α : Type u} (a b : α) : b ∈ {a, b} := Or.inr rfl
      theorem mem_or_mem_of_mem_mk {a b c : α} : c ∈ {a, b} → c = a ∨ c = b := by
        intro h
        cases h with
        | inl h' => exact .inl h'.symm
        | inr h' => exact .inr h'.symm
    end UnorderedPair

    -- QUESTION: Why does `funext` follow from `Quot.sound`?
    section why_funext
      -- The idea is that `funext` is a lifting of "equal everywhere" to "equal", so we prove it by
      --  lifting out of a "quotient by 'equal everywhere'".
      -- If we make "equal everywhere" into an equivalence relation, then we can go via the quotient;
      --  *the action of passing to the quotient is trivial though* because of a cool trick involving
      --  function application.
      -- Since function application is *local* (i.e. only depends on pointwise behaviour; *i.e. only*
      --  *depends on the function **up to extensionality***), it descends to the quotient (by
      --  extensionality), and by definitional equality, the action of `apply f` on the quotient is the
      --  same as `f`. In the quotient, two functions equal-up-to-extensionality are regarded as equal
      --  by `Quot.sound`. These two facts mean that we can go into the quotient via `lift`ing `apply`,
      --  exchange our two extistentionally-the-same functions by `Quot.sound`, and then return from the
      --  quotient by `lift`ing `apply` again.
      def equal_everywhere {α : Sort u} {β : α → Sort u'} (f g : (a : α) → β a) : Prop := ∀ (a : α), f a = g a
      theorem equal_everywhere.iseqv {α : Sort u} {β : α → Sort u'} : Equivalence (@equal_everywhere α β) where
        refl := fun _ _ => rfl
        symm := fun {f} {g} (h : ∀ (a : α), f a = g a) a => (h a).symm
        trans := fun h₁₂ h₂₃ a => (h₁₂ a).trans (h₂₃ a)
      instance fun_up_2_ext (α : Sort u) (β : α → Sort u') : Setoid ((a : α) → β a) where
        r := equal_everywhere
        iseqv := equal_everywhere.iseqv
      -- Quotient
      def FunModExt (α : Sort u) (β : α → Sort u') : Sort (imax u u') := @Quotient ((a : α) → β a) (fun_up_2_ext α β)
      notation:max α " ~> " β " /Ext" => FunModExt α β
      example : (α ~> β /Ext) = FunModExt α β := rfl -- ok yep it worked thank god
      namespace FunModExt
        def mk {α : Sort u} {β : α → Sort u'} (f : (a : α) → β a) : (α ~> β /Ext) := Quotient.mk' f
        theorem ext_eq_implies_equal_in_quotient
          {α : Sort u} {β : α → Sort u'}
          (f g : (a : α) → β a)
          (h : ∀ (a : α), f a = g a)
          : FunModExt.mk f = FunModExt.mk g
          := Quotient.sound h -- *`@Quotient.sound ((a : α) → β a) (fun_up_2_ext α β) f g h`*
        -- NOTE: Function application at any given point respects the extensional equivalence relation
        def apply {α : Sort u} {β : α → Sort u'} : ((x : α) → β x) → (a : α) → β a := id
        theorem apply_respects
          {α : Sort u} {β : α → Sort u'}
          (x : α)
          (f g : (a : α) → β a)
          : f ≈ g → apply f x = apply g x
          := (· x)
        def gaming
          {α : Sort u} {β : α → Sort u'}
          : (α ~> β /Ext) → (x : α) → β x
          := fun qf x => Quotient.lift (apply · x) (α := (a : α) → β a) (apply_respects x) qf
        theorem gaming_down_to_earth
          {α : Sort u} {β : α → Sort u'}
          (f : (a : α) → β a)
          : gaming (FunModExt.mk f) = f
          := rfl
      end FunModExt
      -- NOTE: Here's a proof of `funext` which relies on `Quot.sound`.
      theorem funext'
        {α : Sort u} {β : α → Sort u'}
        (f g : (a : α) → β a)
        (h : ∀ (a : α), f a = g a)
        : f = g
        := calc
          f = FunModExt.gaming (FunModExt.mk f) := rfl
          _ = FunModExt.gaming (FunModExt.mk g) := congrArg FunModExt.gaming $ FunModExt.ext_eq_implies_equal_in_quotient f g h
          _ = g                                 := rfl
    end why_funext
  end unordered_pairs
end fav



/- SECTION: Choice -/
section da_chooser
  #print Classical.choice
  #print Nonempty -- Can only eliminate into `Prop`; erases data of the *witness* to being `Nonempty`
  -- I think these two tell you all that you need to know.
end da_chooser



/- SECTION: LEM -/
section da_lem
  -- Damnit, @src proves Diaconescu's theorem... I didn't need to do it myself--
  -- The use of choice is pretty much the same as in my version of the proof, *I think*, if you forgive
  --  the types being completely different.

  -- NOTE: `Classical` logic gives us `prop`ositional `Complete`ness, which is the rule that **I**
  --  have in my head as "classical logic":
  open Classical in
  theorem propComplete (a : Prop) : a = True ∨ a = False :=
    match em a with
    | .inl h_a  => .inl $ propext $ Iff.intro (fun _ => .intro) (fun _ => h_a)
    | .inr h_na => .inr $ propext $ Iff.intro h_na False.elim
  -- Consequences of `Classical.propComplete` include "proofs by truth tables".
end da_lem

-- *~end of textbook*
-- Thanks, **Jeremy Avigad, Leonardo de Moura, Soonho Kong and Sebastian Ullrich, with contributions from the Lean Community**!
-- (List of authors from https://lean-lang.org/theorem_proving_in_lean4/title_page.html).
