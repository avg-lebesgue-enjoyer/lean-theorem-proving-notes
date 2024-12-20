/- @file Notes/11Conv.lean
 - @src https://lean-lang.org/theorem_proving_in_lean4/conv.html
 -/

/- SECTION: I'm still amazed at `Eq`... -/
set_option pp.proofs true
#print Eq.rec
/-
  *`recursor Eq.rec.{u_tgt, u_src}              `*
  *`  : {α : Sort u_src}                        `*
  *`  → {a : α}                                 `*
  *`  → {motive : (b : α) → a = b → Sort u_tgt} `*
  *`  → motive a (Eq.refl a)                    `*
  *`  → {b : α}                                 `*
  *`  → (t : a = b) → motive b t                `*
-/
set_option pp.proofs false



/- SECTION: Basic navigation and rewriting -/
