import Quadrature.Binary64.Program

/-!
# An operational quadrature loop over addressable tables

The loop machine is an intermediate operational model of the C loop with
explicit memory loads and callback calls. Its steps are the loop test, the
weight load, the node load, the callback call, the rounded accumulation, and
the checked signed-index increment. A callback may fail or change memory. The
main theorem, `returned_eq_integrate`, says that if the tables are loadable and
every callback call returns the functional value without changing memory, then
every terminating run returns `integrate f terms` with the memory intact.
-/

namespace Quadrature.Binary64.LoopMachine

open FloatLib.Floats.Formats.BinaryInterchange

/-- A table address: an allocation block together with a byte offset inside it. -/
structure Pointer where
  block : Nat
  offset : Int

/-- A memory: a partial map from pointers to binary64 values. -/
abbrev Memory := Pointer → Option Value

/-- The address of element `index` of an array of consecutive 8-byte elements starting at
`base`. -/
def element (base : Pointer) (index : Int) : Pointer :=
  ⟨base.block, base.offset + 8 * index⟩

/-- Load a binary64 value at an 8-byte aligned address. Unaligned accesses fail even if the
memory map contains an entry there. -/
def load (memory : Memory) (address : Pointer) : Option Value :=
  if address.offset % 8 = 0 then memory address else none

/-- The loop parameters: the sample count, the base pointers of the weight and node arrays, and
the callback, which may fail or change memory. -/
structure Context where
  count : Int
  weights : Pointer
  nodes : Pointer
  callback : Memory → Value → Option (Memory × Value)

/-- The program point together with the live variables. `test` is the loop guard `i < n`,
`readWeight` and `readNode` are the two array loads, `call` is the callback invocation,
`accumulate` is `acc += w * f(x)`, `increment` is `i++`, and `returned` is the point after
`return acc`. -/
inductive Control where
  | test (index : Int) (accumulator : Value)
  | readWeight (index : Int) (accumulator : Value)
  | readNode (index : Int) (accumulator weight : Value)
  | call (index : Int) (accumulator weight node : Value)
  | accumulate (index : Int) (accumulator weight sample : Value)
  | increment (index : Int) (accumulator : Value)
  | returned (value : Value)

/-- A machine state: the memory together with the control point. -/
abbrev State := Memory × Control

/-- The integer is representable as a 32-bit two's-complement value, so the C `int` increment
that produces it is defined. -/
def signed32 (value : Int) : Prop :=
  -(2 ^ 31) ≤ value ∧ value < 2 ^ 31

/-- `signed32` is decidable by two integer comparisons. -/
instance (value : Int) : Decidable (signed32 value) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- One transition of the loop machine. A failed load, a failed callback, or an increment that
leaves the 32-bit range yields `none`, and `returned` has no successor. -/
def next (ctx : Context) (state : State) : Option State :=
  let (memory, control) := state
  match control with
  | .test i acc =>
      some (memory, if i < ctx.count then .readWeight i acc else .returned acc)
  | .readWeight i acc => do
      let weight ← load memory (element ctx.weights i)
      pure (memory, .readNode i acc weight)
  | .readNode i acc weight => do
      let node ← load memory (element ctx.nodes i)
      pure (memory, .call i acc weight node)
  | .call i acc weight node => do
      let (updated, sample) ← ctx.callback memory node
      pure (updated, .accumulate i acc weight sample)
  | .accumulate i acc weight sample =>
      some (memory, .increment i (Model.add acc (Model.mul weight sample)))
  | .increment i acc =>
      if signed32 (i + 1) then some (memory, .test (i + 1) acc) else none
  | .returned _ => none

/-- Execute exactly this many transitions; any failed operation stops the run. -/
def run (ctx : Context) : Nat → State → Option State
  | 0, state => some state
  | fuel + 1, state => next ctx state >>= run ctx fuel

/-- Running `first + second` steps is running `first` steps and then `second` more. -/
theorem run_add (ctx : Context) (first second : Nat) (state : State) :
    run ctx (first + second) state =
      (run ctx first state >>= run ctx second) := by
  induction first generalizing state with
  | zero => simp [run]
  | succ first ih =>
      simp only [Nat.succ_add, run]
      cases next ctx state with
      | none => rfl
      | some following => exact ih following

/-- Two runs from the same state that both end in a stuck state end in the same state. The
machine is deterministic, so the shorter run is a prefix of the longer one. -/
theorem run_terminal_unique (ctx : Context) (first second : Nat)
    (initial left right : State)
    (hleft : run ctx first initial = some left)
    (hright : run ctx second initial = some right)
    (hlast : next ctx left = none) (hrlast : next ctx right = none) :
    left = right := by
  induction first generalizing second initial with
  | zero =>
      have hi : initial = left := Option.some.inj hleft
      subst initial
      cases second with
      | zero => exact Option.some.inj hright
      | succ second => simp [run, hlast] at hright
  | succ first ih =>
      cases second with
      | zero =>
          have hi : initial = right := Option.some.inj hright
          subst initial
          simp [run, hrlast] at hleft
      | succ second =>
          cases hs : next ctx initial with
          | none => simp [run, hs] at hleft
          | some following =>
              apply ih second following
              · simpa [run, hs] using hleft
              · simpa [run, hs] using hright

/-- A completed execution certifies the existence of every earlier state. -/
theorem run_prefix_exists (ctx : Context) (total elapsed : Nat) (initial final : State)
    (hcomplete : run ctx total initial = some final) (hle : elapsed ≤ total) :
    ∃ current, run ctx elapsed initial = some current := by
  rw [show total = elapsed + (total - elapsed) by omega, run_add] at hcomplete
  cases hp : run ctx elapsed initial with
  | none => simp [hp] at hcomplete
  | some current => exact ⟨current, rfl⟩

/-- Every state before a completed run's endpoint can take another step. -/
theorem run_prefix_progress (ctx : Context) (total elapsed : Nat)
    (initial current final : State)
    (hcomplete : run ctx total initial = some final)
    (hprefix : run ctx elapsed initial = some current) (hlt : elapsed < total) :
    ∃ following, next ctx current = some following := by
  rw [show total = elapsed + (total - elapsed) by omega, run_add, hprefix] at hcomplete
  obtain ⟨remaining, hremaining⟩ : ∃ remaining, total - elapsed = remaining + 1 :=
    ⟨total - elapsed - 1, by omega⟩
  change run ctx (total - elapsed) current = some final at hcomplete
  rw [hremaining] at hcomplete
  simp only [run] at hcomplete
  cases hs : next ctx current with
  | none => simp [hs] at hcomplete
  | some following => exact ⟨following, rfl⟩

/-- The memory holds the given (weight, node) list as consecutive 8-byte elements of the weight
and node arrays, beginning at index `start`. -/
def Tables (memory : Memory) (ctx : Context) (start : Int) :
    List (Value × Value) → Prop
  | [] => True
  | (weight, node) :: rest =>
      load memory (element ctx.weights start) = some weight ∧
      load memory (element ctx.nodes start) = some node ∧
      Tables memory ctx (start + 1) rest

/-- One loop iteration takes six transitions, from `test index acc` to `test (index + 1)` with
the accumulator updated, given loadable entries and a callback that preserves memory. -/
theorem run_iteration (ctx : Context) (memory : Memory) (index : Int)
    (acc weight node sample : Value)
    (hguard : index < ctx.count) (hindex : signed32 (index + 1))
    (hweight : load memory (element ctx.weights index) = some weight)
    (hnode : load memory (element ctx.nodes index) = some node)
    (hcall : ctx.callback memory node = some (memory, sample)) :
    run ctx 6 (memory, .test index acc) =
      some (memory, .test (index + 1) (Model.add acc (Model.mul weight sample))) := by
  simp [run, next, hguard, hindex, hweight, hnode, hcall]

/-- From `test index acc`, the remaining terms execute in six transitions per sample plus one
final return, and the returned value is the left fold of the rounded products from `acc`. -/
theorem run_suffix (ctx : Context) (memory : Memory) (f : Value → Value)
    (terms : List (Value × Value)) (index : Int) (acc : Value)
    (hindex : 0 ≤ index) (hcount : ctx.count = index + terms.length)
    (hrange : ctx.count < 2 ^ 31)
    (htables : Tables memory ctx index terms)
    (hcallback : ∀ term ∈ terms, ctx.callback memory term.2 = some (memory, f term.2)) :
    run ctx (6 * terms.length + 1) (memory, .test index acc) =
      some (memory, .returned
        ((terms.map fun term ↦ Model.mul term.1 (f term.2)).foldl Model.add acc)) := by
  induction terms generalizing index acc with
  | nil =>
      have hc : ctx.count = index := by simpa using hcount
      simp [run, next, hc]
  | cons term rest ih =>
      rcases term with ⟨weight, node⟩
      rcases htables with ⟨hw, hn, ht⟩
      have hguard : index < ctx.count := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hcount
        omega
      have hinc : signed32 (index + 1) := by
        unfold signed32
        constructor <;> omega
      have hcall := hcallback (weight, node) (by simp)
      have hstep := run_iteration ctx memory index acc weight node (f node)
        hguard hinc hw hn hcall
      have hc : ctx.count = (index + 1) + rest.length := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hcount
        omega
      have hrest := ih (index + 1) (Model.add acc (Model.mul weight (f node)))
        (by omega) hc ht (fun term hm ↦ hcallback term (by simp [hm]))
      rw [show 6 * ((weight, node) :: rest).length + 1 =
        6 + (6 * rest.length + 1) by simp; omega, run_add, hstep]
      simpa using hrest

/-- Starting at index 0 with accumulator `+0`, the machine returns exactly the functional model
`integrate f terms` after `6n + 1` transitions. -/
theorem run_integrate (ctx : Context) (memory : Memory) (f : Value → Value)
    (terms : List (Value × Value))
    (hcount : ctx.count = terms.length) (hrange : ctx.count < 2 ^ 31)
    (htables : Tables memory ctx 0 terms)
    (hcallback : ∀ term ∈ terms, ctx.callback memory term.2 = some (memory, f term.2)) :
    run ctx (6 * terms.length + 1) (memory, .test 0 zero) =
      some (memory, .returned (integrate f terms)) := by
  simpa [integrate] using
    run_suffix ctx memory f terms 0 zero (by omega) (by simpa using hcount)
      hrange htables hcallback

/-- Every run that reaches `returned`, whatever its fuel, returns `integrate f terms` and leaves
the memory unchanged. -/
theorem returned_eq_integrate (ctx : Context) (memory : Memory) (f : Value → Value)
    (terms : List (Value × Value))
    (hcount : ctx.count = terms.length) (hrange : ctx.count < 2 ^ 31)
    (htables : Tables memory ctx 0 terms)
    (hcallback : ∀ term ∈ terms, ctx.callback memory term.2 = some (memory, f term.2))
    (fuel : Nat) (finalMemory : Memory) (value : Value)
    (hreturn : run ctx fuel (memory, .test 0 zero) =
      some (finalMemory, .returned value)) :
    finalMemory = memory ∧ value = integrate f terms := by
  have he := run_terminal_unique ctx fuel (6 * terms.length + 1)
    (memory, .test 0 zero) (finalMemory, .returned value)
    (memory, .returned (integrate f terms)) hreturn
    (run_integrate ctx memory f terms hcount hrange htables hcallback) rfl rfl
  simpa using he

end Quadrature.Binary64.LoopMachine
