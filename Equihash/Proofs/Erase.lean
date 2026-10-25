/-
What a verifier accepts: `erase x` is `some a` when `x` returns `Ok(a)`, and `none` for an `Err`
and a panic alike. It takes `pure`, `bind`, lifted `Option` values and loops of
`ExceptT ε Option` to those of `Option`, so a proof of what a function accepts works in `Option`.
-/
module

public import Init.Internal.Order.While
public import Mathlib.Data.List.Basic

@[expose] public section

namespace Equihash.Verifier

variable {ε α β : Type}

/-- `Ok(a)` is `some a`; an `Err` and a panic are `none`. -/
def erase (x : ExceptT ε Option α) : Option α :=
  match x.run with
  | some (.ok a) => some a
  | _ => none

/-- `erase x` is `some a` exactly when `x` returns `Ok(a)`. -/
theorem erase_eq_some {x : ExceptT ε Option α} {a : α} :
    erase x = some a ↔ x.run = some (.ok a) := by
  unfold erase
  rcases x.run with _ | _ | b <;> simp

/-- `Ok(a)` erases to `some a`. -/
@[simp] theorem erase_pure (a : α) : erase (pure a : ExceptT ε Option α) = some a := rfl

/-- An `Err` erases to `none`, as a panic does. -/
@[simp] theorem erase_throw (e : ε) : erase (throw e : ExceptT ε Option α) = none := rfl

/-- `throw e` runs to `some (.error e)`: an `Err`, not a panic. -/
@[simp] theorem run_throw (e : ε) : (throw e : ExceptT ε Option α).run = some (.error e) := rfl

/-- A lifted `some a` is `pure a`: an `Option` value that is not a panic is an `Ok`. -/
@[simp] theorem monadLift_some (a : α) :
    (MonadLiftT.monadLift (some a) : ExceptT ε Option α) = pure a := rfl

/-- A lifted `Option` value erases to itself: its `none` is a panic, its `some` an `Ok`. -/
@[simp] theorem erase_lift (o : Option α) :
    erase (MonadLiftT.monadLift o : ExceptT ε Option α) = o := by
  rcases o with _ | a <;> rfl

/-- `erase` commutes with `bind`, so a sequence of steps erases step by step. -/
theorem erase_bind (x : ExceptT ε Option α) (f : α → ExceptT ε Option β) :
    erase (x >>= f) = erase x >>= fun a => erase (f a) := by
  show erase (ExceptT.bind x f) = _
  unfold erase ExceptT.bind ExceptT.bindCont ExceptT.run ExceptT.mk
  rcases x with _ | _ | a <;> rfl

/-- `erase` commutes with `if`. -/
theorem erase_ite (c : Prop) [Decidable c] (x y : ExceptT ε Option α) :
    erase (if c then x else y) = if c then erase x else erase y := by
  split <;> rfl

/-- A `for` loop over a list: its passes, erased. -/
theorem erase_forIn_list (l : List α) (b : β) (f : α → β → ExceptT ε Option (ForInStep β)) :
    erase (forIn l b f) = forIn l b fun a b => erase (f a b) := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    simp only [List.forIn_cons, erase_bind]
    congr 1
    funext s
    cases s <;> simp [ih]

/-- A `while` loop: its passes, erased, given a measure that each continuing pass decreases. -/
theorem erase_forIn_loop (b : β) (f : Unit → β → ExceptT ε Option (ForInStep β)) (μ : β → ℕ)
    (hμ : ∀ b b', erase (f () b) = some (.yield b') → μ b' < μ b) :
    erase (forIn Lean.Loop.mk b f) = forIn Lean.Loop.mk b fun u b => erase (f u b) := by
  suffices ∀ n b, μ b < n →
      erase (forIn Lean.Loop.mk b f) = forIn Lean.Loop.mk b fun u b => erase (f u b) from
    this _ b (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro b h; omega
  | succ n ih =>
    intro b hb
    show erase (Lean.Loop.forIn _ b f) = Lean.Loop.forIn _ b _
    rw [Lean.Loop.forIn_eq_of_monadTail, Lean.Loop.forIn_eq_of_monadTail, erase_bind]
    rcases hs : erase (f () b) with _ | s
    · rfl
    · cases s with
      | done b' => rfl
      | yield b' => exact ih b' (by have := hμ b b' hs; omega)

end Equihash.Verifier
