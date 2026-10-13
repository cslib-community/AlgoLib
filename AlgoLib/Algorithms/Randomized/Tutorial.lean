/-
Copyright (c) 2026 Antoine du Fresne von Hohenesche. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine du Fresne von Hohenesche
-/

import AlgoLib.Theory.Randomized.Complexity.ExpectedCost
import AlgoLib.Theory.Randomized.Complexity.TailBounds
import AlgoLib.Theory.Randomized.Correctness.Correctness
import AlgoLib.Theory.Randomized.Correctness.Amplify
import AlgoLib.Theory.Randomized.Randomness.RandVec
import AlgoLib.Util.Partition

/-!
# Tutorial: verify your first randomized algorithm

This file is meant to be a guide through the framework, and to
explain it in full detail.

Technically, you can copy it, remove all explanation comments and
replace the toy algorithms with yours (which need not be toy),
and follow the numbered steps.


# Introduction
To introduce the framework we follow one recipe on three toy algorithms,
which altogether illustrate every kind of correctness and complexity
statement the framework supports.

At each step of explanation, we try to point to the real algorithms in
`AlgoLib/Algorithms/Randomized` where the same argument is carried out in full and also
point towards the files in `AlgoLib/Theory/Randomized` where the framework's
machinery is defined.

The reader is encouraged to read those after this tutorial.
-/

/-!
## Step 1: the algorithm
1. The first step is to define the randomized algorithm. The goal is
  to write it once, and to get at the same time code that can run on
  concrete inputs and be formally analysed. Here by analysing we mean
  proving its correctness or describing its complexity.

  In order to achieve this goal, we abstract over the source of
  randomness (which is dropped when the algorithm is deterministic),
  and over the cost model (for the cost of the computation).

  Here is the kind of code we are going to write, so that the rest of
  this step means something:

  ```
  def RandMax {M} [Monad M] [RandMonad M] [MonadCost ℕ M] :
      List α → M α
    | [] => return default
    | L@(_ :: _) => do
        let idx ← randIdx L
        MonadCost.tick 1
        let m ← RandMax (L.eraseIdx idx)
        return max L[idx] m
    termination_by L => L.length
    decreasing_by all_goals grind
  ```

  It finds the maximum of a list by removing a uniformly random element
  at each round. The body is ordinary Lean, but the rest is not obvious
  yet, and it raises the questions that this step will answer, in this
  order:

  - why is `M` left abstract, and what is a monad;
  - what is `RandMonad`, and what does `randIdx` draw;
  - what is `MonadCost`, and what does `tick` charge.

  Note: the framework can technically apply to deterministic algorithms.


  It may be surprising, but both "sources of randomness" and "cost
  models" are abstracted through a monadic structure:

  Recall that a monad is a type constructor `M` (i.e. a function from
  types to types) with operations for any type `α` and `β`:
  `pure : α → M α` and `bind : M α → (α → M β) → M β`, written `>>=`.

  A monad is called lawful when these two operations satisfy three
  laws (for all types `α`, `β`, `γ` and all `a : α`, `m : M α`,
  `f : α → M β`, `g : β → M γ`):

  - `(pure a >>= f) = f a`;
  - `(m >>= pure) = m`;
  - `((m >>= f) >>= g) = (m >>= (fun a => f a >>= g))`.

  This is the distinction Lean makes between the two classes `Monad` and
  `LawfulMonad`, and we keep it throughout this file: "monad" never
  implies the laws, and "lawful monad" always does. It is a distinction
  worth keeping, because running the code only needs a monad, whereas
  proving anything about it needs a lawful one.

### Source of randomness
  "Source of randomness" sounds vague, especially since you may now be
  asking yourself how it is even related to a monad. But it is a precise
  notion, and it is defined at the two following levels.

  At the level of the code, we define a random monad to "simply"
  be a monad `M`, not necessarily a lawful one, equipped with one
  operation and nothing more:

  - `randFin (n : ℕ) [NeZero n] : M (Fin n)`.

  That one operation is the "source of randomness" of `M`. This is the
  class `RandMonad`, in
  `AlgoLib/Theory/Randomized/Randomness/RandMonad.lean`. Observe what
  it does not say: the draw need not be uniform, nor even that it is
  random. It says that `M` is able to make a finite choice. One
  operation is enough because a choice among `n` "things" is a choice
  in `Fin n`, whatever the "things" are. Take the draw of an index
  into a list (which is used everywhere below). It is derived from
  `randFin`:

  ```
  def randIdx {M} [Monad M] [RandMonad M] {α}
      (L : List α) (h : 0 < L.length := by grind) : M (Fin L.length) :=
    have : NeZero L.length := ⟨h.ne'⟩
    RandMonad.randFin L.length
  ```

  This is a definition, and not a second operation of the class. The
  body is `RandMonad.randFin L.length`, so the derivation is one
  instantiation, `n := L.length`. The returned type is worth a look.
  The valid indices into `L` are exactly the elements of `Fin L.length`,
  so a draw is already a legal index, and `L[i]` can be written with
  no bound to carry around.

  The hypothesis `h` says that `L` is non-empty, which is what
  `randFin` asks for through `[NeZero n]`, and the `have` line turns
  `h` into that instance. The `:= by grind` makes `h` an
  auto-parameter, so Lean proves it by itself at each use. This is
  why we can write `randIdx L` (as long as we have a proof that `L` is
  non-empty) and nothing else.

  Note: we could call this a non-empty finite source of randomness.
  The framework does not support continuous distributions, and the
  reason is that the mathematics of continuous distributions (in Lean)
  is much more complex than the discrete case.

  At the level of the mathematics that interface is not enough, since
  it says nothing about what a draw means. The meaning is supplied
  by the class `LawfulRandMonad`, which equips a lawful monad `M`
  with an interpretation into `PMF`, the lawful monad of discrete
  probability distributions (provided by Mathlib). The class asks
  that `M` be lawful, where `RandMonad` above asked only for a monad.
  This interpretation is a function

  - `toPMF : M α → PMF α` (for any type `α`),

  subject to three axioms:

  - `toPMF` commutes with the two `pure`: `toPMF (pure a) = PMF.pure a`
  (for all `a : α`);

  - it commutes with `bind`:
  `toPMF (m >>= f) = (toPMF m >>= (toPMF ∘ f))`
  (for any type `β` and all `m : M α` and `f : α → M β`);

  - and it sends `randFin n` to the uniform distribution on `Fin n`:
  `toPMF (randFin n) = PMF.uniformOfFintype (Fin n)`.

  The first two axioms say exactly that `toPMF` is more than a function:
  it is a morphism of monads; the third calibrates it on the primitive.

  So the notion carries two definitions, one per level, and we use
  both:

  > at the level of the code, a "random monad" is a monad `M` with a
  > primitive function `randFin`, its "source of randomness". This is
  > `RandMonad`.
  >
  > at the level of the mathematics, a "lawful random monad" is a
  > lawful monad `M` with `randFin`, equipped with a monad morphism
  > into the `PMF` monad that sends this primitive draw to the
  > uniform distribution. This is `LawfulRandMonad`.

  These two levels are what let one piece of code be both run and
  reasoned about.

* `IO` is a lawful monad (Batteries proves it) and is a `RandMonad`.
  Its `randFin` calls the generator of the operating system, so the
  algorithm executes. But it is not a `LawfulRandMonad` because
  `toPMF` is missing. Giving `IO` an instance would mean writing a
  function `IO α → PMF α`, which assigns a distribution to every `IO`
  program, and then proving the three axioms for it. An `IO α` is not
  a distribution over `α` in the first place, since it may read a
  file, fail, or depend on the state of the machine. Its draw is not
  random inside the logic either. `IO.rand` reads a mutable reference
  `IO.stdGenRef`, computes a deterministic function of the generator
  it holds, and writes the new generator back. The only genuine
  randomness is the seed taken at start-up from `IO.getRandomBytes`,
  an opaque constant that the logic says nothing about. Even granting
  an ideal generator, the third axiom would be false because Lean's
  `randNat` is only approximately uniform and not truly uniform.

* `PMF` is a `LawfulRandMonad`, in fact the canonical one, where
  `toPMF` is the identity: such a program simply is its own
  distribution. Being noncomputable, it is what we reason about, and
  it does not run.

  A definition therefore asks for `[Monad M]` and `[RandMonad M]`,
  the least that lets the code be run (when it needs a source of
  randomness), and a theorem asks for `[LawfulMonad M]` and
  `[LawfulRandMonad M]`, the least that lets the code be reasoned
  about.

### Cost model
  The cost model is abstracted in the same two-level way.

  At the level of the code, we define a cost model to be a monad `M`,
  again not necessarily a lawful one, equipped with one operation and
  nothing more:

  - `tick : C → M Unit`, where `C` is the type of the costs.

  Here `Unit` is the type with exactly one element, and that element
  is written `()`. Such a type seems useless, but in functional
  programming it is what represents a computation returning nothing.
  So `tick c` returns nothing, and all it does is charge the
  cost `c`.

  This is the class `MonadCost C M`, in
  `AlgoLib/Theory/Randomized/Complexity/MonadCost.lean`. It is a class, and
  not a monad: `M` is the monad, and `MonadCost C M` is the interface
  saying that `M` can charge costs of type `C`. The class does not
  even ask `M` to be a monad.

  Observe what it does not say: the cost need not be counted, nor
  even recorded. What the charge does is left to the instance defined
  for `M`, and we present two of them here.

  The first instance is the default one (valid for any monad, lawful
  or not). It defines `tick _ := pure ()`, so it sends every cost `c`
  to the computation that does nothing and returns `()`. The tick is
  a no-op and the cost is dropped. Every monad has this instance, and
  it is the one used when the algorithm is run with the monad `IO`.

  The second instance is the interesting one: the one that accumulates.
  It is declared for `TimeMT`, the type that carries the clock, so Lean
  picks it only when the monad has that form (i.e., `M = TimeMT C N` for
  some cost type `C` and monad `N`), where the default one above applies
  to any monad at all. Two of the four readings of Step 2 are made
  of `TimeMT`, so we introduce it there and describe its `tick` at the
  same time.

  At the level of the mathematics that interface is not enough, since
  it says nothing about what a tick means. The meaning is supplied by
  the class `LawfulMonadCost C M`, in
  `AlgoLib/Theory/Randomized/Complexity/TimedSemantics.lean`. It presupposes
  that `M` is a lawful random monad, so that `toPMF` is
  available, and it comes with an axiom:

  - `toPMF (tick c) = PMF.pure ()` (for all `c : C`).

  It says that the tick is invisible to the output distribution. The
  tick spends time, and it leaves the output alone.

  So the definition we work with is:

  > at the level of the code, a cost model is a monad `M` with a
  > primitive function `tick`. This is `MonadCost`.
  >
  > at the level of the mathematics, it is a lawful random monad
  > `M`, so a `LawfulRandMonad`, with `tick`, which the
  > monad morphism into the `PMF` monad sends to the point mass on
  > `()`. This is `LawfulMonadCost`.

  The two `MonadCost` instances of the two paragraphs above, the
  default one and the one declared for `TimeMT`, both satisfy this
  axiom, so both are instances of `LawfulMonadCost` as well.

  For the default one there is nothing to check, since its `tick` is
  already a `pure`. For the `TimeMT` one, the interpretation of a
  timed program keeps the value and drops the cost, and a tick
  changes only the cost, so a tick becomes invisible.

  Here again the two levels are not a technicality. A definition asks
  only for `[MonadCost ℕ M]`, and a theorem about the output asks for
  `[LawfulMonadCost ℕ M]` as well. The axiom is what lets the proof
  drop the ticks, and it is why one correctness theorem also covers
  the timed reading `TimeMT ℕ PMF`.

  The algorithm is thus polymorphic over
  `{M} [Monad M] [RandMonad M] [MonadCost ℕ M]`.

  We take ℕ as the basic cost type, because counting ticks is the
  standard cost model. But any other type works. To run, `TimeMT`
  only needs a `Zero` and an `Add` on it. To be a lawful monad, and
  so to be usable in proofs, it needs an `AddMonoid`, that is, the
  monoid laws as well.
-/

/-!
Let us now define the three algorithms of this tutorial. They are
written once, and every term defined above appears in them. We explain
just after why we do three algorithms.
-/

namespace AlgoLib

open Cslib.Algorithms.Lean

-- `Inhabited` supplies the `default` returned on the empty list.
variable {α : Type} [LinearOrder α] [Inhabited α]

/-- Find the maximum by repeatedly removing a uniformly random element
and comparing it against the maximum of the rest (one tick per
comparison). -/
def RandMax {M} [Monad M] [RandMonad M] [MonadCost ℕ M] :
    List α → M α
  | [] => return default
  | L@(_ :: _) => do
      let idx ← randIdx L
      MonadCost.tick 1
      let m ← RandMax (L.eraseIdx idx)
      return max L[idx] m
  termination_by L => L.length
  decreasing_by all_goals grind

/-- Test one uniformly random position and report whether it holds
`x`. One tick per test. -/
def RandMember {M} [Monad M] [RandMonad M] [MonadCost ℕ M]
    (x : α) : List α → M Bool
  | [] => return false
  | L@(_ :: _) => do
      let i ← randIdx L
      MonadCost.tick 1
      return (L[i] == x)

/-- Return a uniformly random element. No tick, so the cost is `0`. -/
def RandPick {M} [Monad M] [RandMonad M] [MonadCost ℕ M] : List α → M α
  | [] => return default
  | L@(_ :: _) => do
      let i ← randIdx L
      return L[i]

/-!
Why do we do three algorithms at once? Simply because they illustrate
different aspects of the framework so the tutorial carries these
three through the recipe together (these are simple algorithms so
they are easy to handle in the brain). We link them to the real
algorithms we defined in `AlgoLib/Algorithms/Randomized` that have roughly the
same shape.

* `RandMax` returns the maximum, removing a random element each round.
  So its output is always correct and only its cost varies: this is a
  so-called Las Vegas algorithm (a type of randomized computer
  algorithm that always gives the correct result, but its running time
  varies and depends on random choices). It illustrates Dirac
  correctness (Step 5a), an exact expected cost (Step 6), the cost
  distribution (Step 7) and a tail bound (Step 8).

  The algorithms of this shape are `Quicksort` and `Quickselect`.

* `RandMember` answers "is `x` in `L`?" by testing one random
  position. Its cost is fixed and its output can be wrong: this is a
  Monte Carlo algorithm (a type of randomized computer algorithm that
  uses repeated random sampling to solve deterministic or
  probabilistic problems; its output may be incorrect with a small,
  controllable probability). It illustrates the exact output
  distribution (Step 5b), one-sided error (5c), a success probability
  and its amplification (5d).

  The algorithms of this shape are `Freivalds`, `SchwartzZippel` and
  `Karger`.

* `RandPick` returns a uniformly random element and does nothing else.
  It never ticks, so it shows that code without `tick` has cost `0`
  (Step 6), and it carries the one expectation that is not a cost
  (Step 9).

  The algorithm of this shape is `FisherYates`.
-/

/-!
## Step 2: instances for free

2. The second step is evaluation.

  Here is the code of this step, for `RandMax`:

  ```
  def RandMax_IO : List ℕ → IO ℕ := RandMax
  #eval RandMax_IO [3, 1, 4, 1, 5, 9, 2, 6]

  noncomputable example : List ℕ → PMF ℕ := RandMax

  def RandMax_IO_Timed : List ℕ → TimeMT ℕ IO ℕ := RandMax
  #eval (RandMax_IO_Timed [3, 1, 4, 1, 5, 9, 2, 6]).run  -- ret 9, time 8
  ```

  On the right of every `:=` there is the same `RandMax` of Step 1.
  What changes is only the monad inside the type on the left: `IO`,
  then `PMF`, then `TimeMT ℕ IO`. That monad is the whole content of
  this step.

  A fourth reading, `TimeMT ℕ PMF`, gets no line of its own here,
  because it is not something one runs.

  This raises two questions, which we answer in this order:

  - what is `TimeMT`, the monad of the third line;
  - what each of the four readings means, and why the `PMF` one is an
    `example` rather than an `#eval`.

  `TimeMT` is built in two stages, and it is also where the
  second `MonadCost` instance (tick instance) of Step 1 lives.

  The first stage is `TimeM`, from `cslib`
  (`Cslib/Algorithms/Lean/TimeM.lean`). A `TimeM T α` is a pair of a
  value `ret : α` and of a cost `time : T`. It is itself a monad as
  soon as `T` has a `0` and a `+`: its `pure` sets the cost to `0`,
  and its `bind` adds the two costs. It is a lawful monad as soon as
  `T` is an additive monoid.

  The second stage is `TimeMT`, defined in
  `AlgoLib/Theory/Randomized/Complexity/TimeMT.lean`. It is a structure with
  a single placeholder, called `run`:

  ```
  structure TimeMT (T : Type) (M : Type → Type) (α : Type) where
    run : M (TimeM T α)
  ```

  Here `T` is again the type of the costs, `α` is any
  type, and `M` is any monad, lawful or not.

  So a `TimeMT T M α` is a box holding one object of type
  `M (TimeM T α)`. Such an object can be an `IO` program,
  a `PMF` distribution, or anything else.

  Writing `⟨p⟩`, for `p : M (TimeM T α)`, puts `p` into the box.
  Writing `m.run`, for `m : TimeMT T M α`, takes it back out.

  The two operations that make it a monad are defined just after the
  structure, in the same file:

  ```
  protected def pure [Zero T] [Pure M] (a : α) : TimeMT T M α :=
    ⟨Pure.pure ⟨a, 0⟩⟩

  protected def bind [Add T] [Monad M]
      (m : TimeMT T M α) (f : α → TimeMT T M β) : TimeMT T M β := ⟨do
      let ⟨a, t1⟩ ← m.run
      let ⟨b, t2⟩ ← (f a).run
      pure ⟨b, t1 + t2⟩⟩
  ```

  The `pure` puts the value in the box and starts the clock at `0`.
  The `bind` opens the box of `m`, opens the box of `f a`, and returns
  the pair `⟨b, t1 + t2⟩`. That single `+` is the whole of the cost
  accounting of this framework, and it is the reason `TimeMT` exists.

  This also answers the question the box raises: why not work with the
  bare type `M (TimeM T α)`? The answer is that on that type the `>>=`
  available is the one of `M`, which carries the pair along without
  ever reading its `time` field, so the costs would have to be added
  by hand at every step. The box is what lets us attach the `bind`
  above instead.

  `TimeMT T M` is therefore a monad as soon as `T` has a `0` and a
  `+`, which is exactly what `pure` and `bind` ask for. It is a lawful
  monad as soon as `T` is an additive monoid and `M` is itself lawful.

  A concrete term makes this less abstract. The term

  - `RandMax_IO_Timed [3, 1, 4, 1, 5, 9, 2, 6] : TimeMT ℕ IO ℕ`

  is such a box. Opening it with `.run` gives an `IO (TimeM ℕ ℕ)`,
  which is an `IO` program, and executing that program prints the
  pair it returns: `{ ret := 9, time := 8 }`, the maximum `9`
  obtained in `8` ticks.

  We can now come back to the second `MonadCost` instance, the one
  announced in Step 1. It is declared in
  `AlgoLib/Theory/Randomized/Complexity/MonadCost.lean` and it delegates to
  one last definition of `TimeMT` (in
  `AlgoLib/Theory/Randomized/Complexity/TimeMT.lean`):

  ```
  instance (priority := 1000) instMonadCostTimeMT
      {T : Type} {M} [Monad M] : MonadCost T (TimeMT T M) where
    tick := TimeMT.tick

  def tick [Monad M] (t : T) : TimeMT T M Unit :=
    ⟨Pure.pure ⟨(), t⟩⟩
  ```

  Read the second definition first. A `tick t` is the box holding the
  pair `⟨(), t⟩`. The value is `()`, which the return type
  `TimeMT T M Unit` forces it to be, and the cost field holds `t`.

  The addition happens in the `bind` shown above. When the algorithm
  writes `MonadCost.tick 1` inside a `do` block, that block is a chain
  of `bind`s, so the `1` meets the `t1 + t2` of `bind` and is added to
  the cost of everything that follows it. This is how the costs of a
  run accumulate.

  The `priority := 1000` is what makes this instance win over the
  default one of Step 1, which has priority `100` and applies to every
  monad (if the monad is a `TimeMT`, the higher priority decides).

  Note: the costs are trusted, not verified. `tick 1` costs one unit
  because we wrote `tick 1`, and nothing checks it against a machine.
  This is inherited from the design principle of `TimeM` (also stated
  plainly in `cslib`). So the `8` above is the number of `tick 1` that
  were executed, and nothing more.

  So the framework proves what follows from the cost model, and the
  cost model is ours to choose. `cslib` asks that the choice be
  written down: what costs one unit, what is free, and whether a
  recursive call is charged.

  Four readings usually matter.

  - `IO` is the executable reading. `randFin` draws from the real
    random number generator, and `tick` is a no-op, because the
    `MonadCost` instance (low priority, in
    `AlgoLib/Theory/Randomized/Complexity/MonadCost.lean`) discards it. The
    algorithm simply runs.

  - `TimeMT ℕ IO` is the executable reading with a clock. The
    `TimeMT` instance of `MonadCost` has higher priority than the
    default one, so here `tick` accumulates instead of vanishing.
    `.run` returns the output paired with the total cost.

  - `PMF` is the mathematical reading: the program denotes the
    distribution of its output. It is noncomputable, so it cannot be
    `#eval`-ed; we assert it with `example`, which is enough to check
    that the instances line up.

  - `TimeMT ℕ PMF` is the reading every cost theorem is about: the
    joint distribution of output and cost. It is what `𝔼_{M}[cost e]`
    (explained in the following steps) instantiates behind the scenes.
-/

-- For RandMax
def RandMax_IO : List ℕ → IO ℕ := RandMax

#eval RandMax_IO [3, 1, 4, 1, 5, 9, 2, 6]        -- 9

noncomputable example : List ℕ → PMF ℕ := RandMax

def RandMax_IO_Timed : List ℕ → TimeMT ℕ IO ℕ := RandMax

#eval (RandMax_IO_Timed [3, 1, 4, 1, 5, 9, 2, 6]).run  -- ret 9, time 8

-- For RandMember
def RandMember_IO : ℕ → List ℕ → IO Bool := RandMember

#eval RandMember_IO 5 [3, 1, 4, 1, 5, 9, 2, 6]   -- true with probability 1/8

noncomputable example : ℕ → List ℕ → PMF Bool := RandMember

def RandMember_IO_Timed : ℕ → List ℕ → TimeMT ℕ IO Bool := RandMember

#eval (RandMember_IO_Timed 5 [3, 1, 4, 1, 5, 9, 2, 6]).run  -- ret random, time 1

-- For RandPick
def RandPick_IO : List ℕ → IO ℕ := RandPick

#eval RandPick_IO [3, 1, 4, 1, 5, 9, 2, 6]

noncomputable example : List ℕ → PMF ℕ := RandPick

def RandPick_IO_Timed : List ℕ → TimeMT ℕ IO ℕ := RandPick

#eval (RandPick_IO_Timed [3, 1, 4, 1, 5, 9, 2, 6]).run  -- ret random, time 0

/-!
## Step 3: name the branch (cost proofs only)
3. The third step gives a name to one piece of the algorithm. It is
  needed for the simplicity of the cost proofs.

  Here is the code of this step:

  ```
  private abbrev randMax_branch
      (M : Type → Type) [Monad M] [RandMonad M] [MonadCost ℕ M]
      (L : List α) (i : Fin L.length) : M α := do
    MonadCost.tick 1
    let m ← RandMax (L.eraseIdx i)
    return max L[i] m
  ```

  Compare it with `RandMax` of Step 1. It is the same body minus its
  first line: the draw `let idx ← randIdx L` has disappeared, and the
  drawn index has become a parameter `i`. What is left is the work
  that `RandMax` does once the index is fixed. This is a branch of the
  algorithm, hence the name `randMax_branch`.

  This raises three questions, which we answer in this order:

  - why the branch needs a name of its own;
  - why an `abbrev` and not a `def`;
  - why only `RandMax` gets one.

  It needs a name because the cost recurrence of Step 6 is a
  statement about it: "the branch at `i` costs `1`, plus the cost of
  the recursive call on a list of one element less". Without a name
  there is no subject for that sentence.

  The name is given by an `abbrev` rather than a `def`, most importantly
  so that it stays reducible: `unfold` brings the do-block back and
  `cost_step` can peel it, while the lemmas about the branch still read
  as "the branch at `i` costs ...", which is convenient.

  Only `RandMax` gets one. For the other two the branch is very short,
  and naming it would buy nothing. In `RandMax` the branch contains the
  recursive call `RandMax (L.eraseIdx i)`, whose cost stays unknown
  until an induction supplies it, in Step 6 for instance. The name is
  what carries that unknown until then.

  So the usual criterion is to name a branch when its cost is not yet
  known, or simply when a name is convenient for the analysis.

  Real examples: `qs_branch` in `Quicksort`, `qsel_branch` in
  `Quickselect`.
-/

/-- The work at a fixed index `i`. -/
private abbrev randMax_branch
    (M : Type → Type) [Monad M] [RandMonad M] [MonadCost ℕ M]
    (L : List α) (i : Fin L.length) : M α := do
  MonadCost.tick 1
  let m ← RandMax (L.eraseIdx i)
  return max L[i] m

/-!
## Step 4: the specification and its transport lemma

4. The fourth step supplies a specification and a transport lemma. The
  specification is a plain function saying what the algorithm should
  return. The transport lemma is an equation about that function,
  which we tag so that the automation of Step 5 can use it.

  Here is the code of this step:

  ```
  def listMax (L : List α) : α := L.foldr max default

  @[spec_transport]
  private lemma listMax_branch (L : List α) (i : ℕ) (h : i < L.length) :
      max L[i] (listMax (L.eraseIdx i)) = listMax L := by
    unfold listMax
    rw [(perm_getElem_cons_eraseIdx L ⟨i, h⟩).foldr_eq default,
      List.foldr_cons]
    rfl
  ```

  These two things are supplied here, one per declaration, and this is
  where you have to work: the framework cannot guess a non-trivial
  specification.

  Notice that neither declaration mentions a monad or any machinery.
  This is simply the mathematics.

  The specification is the function that the output of the algorithm
  must equal. Here it is `listMax`, the maximum of a list.

  The transport lemma says how the specification survives one
  branch of the recursion: if the recursive call already meets the
  specification on the smaller input, then the work done by the
  branch carries it back to the specification on the whole input.
  This is the induction step of the correctness proof, stated in
  isolation and with the randomness left out entirely. Tagging it
  `@[spec_transport]` places it in the pool of lemmas the tactic of
  Step 5 tries on each branch, which is why that step is one line.

  Only `RandMax` has a specification. A specification names a single
  value (here the maximum), so only an algorithm whose output is a
  single value can have one. For `RandMember` and `RandPick` the
  output really is random, so what takes the place of a specification
  is a distribution, a support statement or a bound (see Step 5).

  One practical point, which is where the time goes when a proof does
  not close: it is useful to state the transport lemma so that its
  hypotheses match the hypothesis of the branch leaves in context,
  especially in the form that `simp` normalises them to. Here,
  that means a ℕ index with an explicit bound `i < L.length`,
  because that is what `L[i]` carries with it. `dirac_finish` (which
  behind is a simp) can then use the side conditions by itself.

  Real examples: `sortSpec_partition_cons` in `Quicksort`, and the
  three `orderStat_*_branch` lemmas in `Quickselect`, one per case of
  its split.

  A specification has to name a value, but the value may be a definite
  description: something a property pins down uniquely. `listMax` below
  is the maximum, an iterated `max`. Quicksort's is `sortSpec L`, the
  sorted list, built from `SortedLE` by choice because nothing in the
  library already denoted it. Any Lean term is allowed here and you may
  want to prove that an algorithm agrees with some other implementation.
  You just have to be careful on whether the term you name for the
  specification is the thing you meant to talk about.
-/

/-- Specification: the maximum of a list (with `default` for `[]`). -/
def listMax (L : List α) : α := L.foldr max default

-- `Perm.foldr_eq` (used below) reorders the fold, which needs `max`
-- to be left-commutative.
private instance : LeftCommutative (max : α → α → α) :=
  max_left_commutative

/-- Transport: removing the chosen element and re-inserting it via
`max` recovers the maximum. This holds because `max`-folds are
invariant under permutation, and `L` permutes to `L[i] :: L.eraseIdx i`
by `perm_getElem_cons_eraseIdx` (in `AlgoLib.Helpers.Partition`, which
collects reusable index lemmas). -/
@[spec_transport]
private lemma listMax_branch (L : List α) (i : ℕ) (h : i < L.length) :
    max L[i] (listMax (L.eraseIdx i)) = listMax L := by
  unfold listMax
  rw [(perm_getElem_cons_eraseIdx L ⟨i, h⟩).foldr_eq default, List.foldr_cons]
  rfl

/-!
## Step 5: correctness

5. The fifth step is about correctness. There is no single correctness
  theorem, and this is the one place where the recipe starts to split.

  We first introduce some notation.

  Several notations of this kind appear below, and they all share the
  same pattern. In each of them:

  - `M` is the monad at which we read the algorithm, a lawful
    random monad, typically `PMF`;
  - `e` is the algorithm itself, that is a term of type `M α`, for
    instance `RandMax L` or `RandMember x L`;
  - `v` is one possible output of it, a term of type `α`, for
    instance `true`;
  - `S` is a set of outputs, in other words an event.

  They are all macros. To recall, a macro is a purely syntactic
  abbreviation: Lean replaces it by the term it stands for before type
  checking, so nothing new is defined by it and there is never
  anything to unfold later. This is the difference with `unfold`,
  which replaces a constant by its body during a proof. It also means
  that `simp` and `rw` see the underlying term directly. When we write
  "expands to" below, we name exactly that replacement.

  The first three notations read the output of the algorithm.

  - `𝒟_{M}[e]` is the output distribution of `e`. It expands to
    `LawfulRandMonad.toPMF (e : M _)`, so it is a `PMF`. This is also
    where the `LawfulRandMonad` of Step 1 is finally used: without
    `toPMF` the notation would not exist. It is defined in
    `AlgoLib/Theory/Randomized/Randomness/RandMonad.lean`.

  - `ℙ_{M}[e = v]` is the probability that `e` outputs `v`. It expands
    to `LawfulRandMonad.toPMF (e : M _) v`, which is exactly
    `𝒟_{M}[e]` applied to the point `v`. So the two notations are the
    same object seen twice: `𝒟` is the whole distribution, `ℙ` is that
    distribution read at one value, and is therefore a number in
    `ENNReal`.

  - `ℙ_{M}[e ∈ S]` is the same thing for an event rather than a single
    value. It expands to `prob 𝒟_{M}[e] S`, where
    `prob p s = ∑' a, s.indicator p a` sums the probabilities over
    `s`. Both `ℙ` forms live in
    `AlgoLib/Theory/Randomized/Randomness/Prob.lean`.

  The remaining three notations read the cost instead. They all go
  through the timed reading `TimeMT ℕ M` of Step 2, and they rest
  on a different distribution from the three above, which is worth
  making explicit before we list them.

  A timed program `m : TimeMT ℕ M α` returns a pair, a value and a
  cost, so its law is a law of pairs:

  - `TimedPMF m = toPMF m.run`, of type `PMF (TimeM ℕ α)`, is that
    joint law of the output and the cost.

  A law of pairs has two marginals, and both are used in this file.

  - Forgetting the cost gives the law of the output, of type `PMF α`.
    This is `𝒟` read at `TimeMT ℕ M`, whose instance is
    `toPMF m = toPMF (TimeM.ret <$> m.run)`, that is `TimedPMF m`
    mapped along the projection `TimeM.ret` of a pair onto its value.
    It is what the three notations above mean once the monad carries
    time, and it is why a correctness theorem proved once for an
    abstract `M` covers the timed reading as well.

  - Forgetting the value gives the law of the cost, of type `PMF ℕ`.
    This is `costPMF m = (TimedPMF m).map TimeM.time`, and it is the
    subject of Step 7.

  The three notations below use the joint law itself, since averaging
  or bounding the cost only needs the `time` component of each
  outcome.

  - `𝔼_{M}[cost e]` is the expected cost of `e`. It expands to
    `expected_cost (TimedPMF (e : TimeMT ℕ M _))`, and

    ```
    expected_cost p = ∑' res, p res * (res.time : ENNReal)
    ```

    averages the `time` field of the pair and ignores the value. The
    result is a number in `ENNReal`. It is defined in
    `AlgoLib/Theory/Randomized/Complexity/ExpectedCost.lean` and used from
    Step 6 on.

  - `𝔼ℝ[cost m]` is that same number as a real, through `toReal`.

  - `ℙ[cost m > k]` is the probability that the cost of `m` exceeds
    `k`. It expands to `prob (TimedPMF m) {tm | k < tm.time}`, so it
    is the same `prob` as in the output notations above, applied this
    time to the joint law and to an event that only looks at the
    `time` component: the set of pairs whose cost is greater than `k`.
    It is therefore again a number in `ENNReal`. Similarly
    `ℙ[cost m ≥ k]` expands to `prob (TimedPMF m) {tm | k ≤ tm.time}`.
    They are defined in `AlgoLib/Theory/Randomized/Complexity/TailBounds.lean`,
    and Step 8 bounds the strict one with `runtime_markov_gt` and the
    other with `runtime_markov`. This will be explained later.

  Now that we have introduced the notations, here are the four shapes
  that a correctness theorem takes in this file (there can of course
  be others):

  * Dirac (5a). The output distribution is a point mass. `RandMax` is
    such an algorithm, and so is every Las Vegas one.

    ```
    𝒟_{M}[RandMax L] = PMF.pure (listMax L)
    ```

  * Exact distribution (5b). The output follows a distribution that is
    not a point mass. This is the strongest correctness theorem we can
    get once no single output is the right one.

    ```
    ℙ_{M}[RandMember x (a :: L) = true]
      = ((a :: L).count x : ENNReal) / ((a :: L).length : ENNReal)
    ```

  * Support (5c). A weaker theorem, but often the useful one: the
    output can be wrong, but only in one direction. It holds on every
    run, and no probability appears in it.

    ```
    ∀ b ∈ 𝒟_{M}[RandMember x L].support, b = true → x ∈ L
    ```

  * Success probability, then amplification (5d). Bound the
    probability of a correct output, then repeat to push the
    failure probability down (which is called amplification).

    ```
    1 / ((a :: L).length : ENNReal) ≤ ℙ_{M}[RandMember x (a :: L) = true]
    1 - (1 - p) ^ k ≤ ℙ_{M}[amplify (· || ·) k (RandMember x L) = true]
    ```

    The `amplify (· || ·) k` of the second line is not a notation but
    an ordinary definition, in
    `AlgoLib/Theory/Randomized/Correctness/Amplify.lean`:

    ```
    def amplify {M} [Monad M] {β : Type} (best : β → β → β) :
        ℕ → M β → M β
      | 0, m => m
      | 1, m => m
      | k + 2, m => do
          let a ← m
          let b ← amplify best (k + 1) m
          return best a b
    ```

    `amplify best k m` runs `m` exactly `k` times, independently,
    and folds the `k` answers together with `best`, two at a time.
    Unfolding `k = 3` gives `best a₁ (best a₂ a₃)`, where `a₁`, `a₂`
    and `a₃` are the three runs.

    Notice the limitation: `best` is binary, so the combination is a
    fold, while some ways of aggregating `k` answers are not folds at
    all. Majority vote is the standard example, and a median is
    another. Neither can be written as a `β → β → β` applied pairwise,
    because both have to count or sort all `k` answers at once.

    Notice also that the special case `k = 0` returns one run.
    The reason is the type: the result has to be an `M β`, so it has
    to produce a `β`, and there is no `β` to be had from zero runs.
    Returning nothing would mean changing the type to something like
    `M (Option β)` and carrying that `Option` through every later
    theorem, for a case nobody calls. This costs nothing in the
    theorems, because the bound is vacuous exactly there. At `k = 0`
    it reads `1 - (1 - p)^0 ≤ ℙ[...]`, that is `0 ≤ ℙ[...]`, which is
    true of any probability. At `k = 1` it reads `p ≤ ℙ[...]`, which
    is the hypothesis on one run. The definition and the bound only
    start saying something new at `k = 2`.

    So this is a deliberate choice, and the alternative is worse.
    Asking for `0 < k` would add a hypothesis to `amplify_success`,
    and to every theorem built on it, in order to rule out a case that
    lands correctly on its own.

    There is one place where `k = 0` is not harmless, and it concerns
    the cost rather than the correctness. The equation
    `𝔼[cost amplify best k m] = k * 𝔼[cost m]` is false at `k = 0`,
    where it would claim that one run is free. So
    `expected_cost_amplify` is stated at `k + 1` instead:

    ```
    𝔼[cost amplify best (k + 1) m] = (k + 1 : ENNReal) * 𝔼[cost m]
    ```

    Lastly, `(· || ·)` is Lean's shorthand for
    `fun a b => a || b`, the Boolean "or". It is the right choice for
    `RandMember` precisely because of 5c: a `true` is always
    trustworthy and a `false` may be a miss, so keeping any `true` that
    appears can only improve the answer.

    `best` is left abstract in `amplify` because the right combiner
    depends on the algorithm. For example `Karger`, in
    `AlgoLib/Algorithms/Graph/MinCut/Karger.lean`, returns a pair rather than a
    boolean, the partition it found, and the value of the corresponding
    cut. Its combiner is therefore not `min` but `argmin Prod.snd`,
    which is `fun a b => if a.2 ≤ b.2 then a else b` (it keeps
    whichever of the two runs reported the smaller value, and keeps
    that run's partition along with it).

  Small note: A Monte Carlo algorithm typically needs 5b, 5c and 5d
  together.

### 5a: Dirac correctness (`RandMax`)

With the transport lemma of Step 4 in place, the proof is one tactic.
`dirac_correct RandMax` runs functional induction on the algorithm.
The cases are the algorithm's own cases, and the induction hypotheses
come already quantified over the drawn index. The goal is an equation
about `RandMax L`, which begins by drawing an index. Then, because
every branch returns the same output, we can collapse the draw to the
point mass at the maximum of the list. Collapsing replaces the goal by
the same equation for the branch at a fixed `i`. The lemma that says
so is `toPMF_randIdx_bind_dirac`. Finally it discharges each branch
with the `@[spec_transport]` lemmas. If there is still a goal open
after applying, it is most often due to a transport lemma you have
not stated. It can also be a base case whose specification has to
be unfolded by hand, as in `quickselect_correct`.

Real examples: `quicksort_correct`, `quickselect_correct`.

There are two other routes to a Dirac theorem, for when the
specification is more naturally a property than a value. Naming a
value first means every branch must be proved equal to that one
expression, and the second route below avoids that. Both are in
`AlgoLib/Theory/Randomized/Correctness/Correctness.lean`.

- `toPMF_randIdx_bind_dirac_spec` weakens what each branch must supply.
  Instead of one agreed value it asks for any deterministic output
  meeting a specification `P`, plus the fact that `P` has at most one
  solution. It is `toPMF_randIdx_bind_dirac` with the agreement
  recovered from uniqueness rather than assumed.

- The support route drops the value for the whole induction. Prove the
  Step 5c statement "every reachable output satisfies `P`", then apply
  `eq_pure_of_support_subsingleton`, which upgrades it to a point mass
  as soon as `P` has at most one solution. This is the route that
  inducts most cleanly, because the support of a draw is the union
  of the branch supports, so the branches never have to agree on
  anything and each is discharged on its own.

The second route is worth understanding even if you do not use it,
because it says what the tiers of Step 5 are to each other: Dirac
correctness (5a) is support correctness (5c) plus uniqueness of the
specification.

The price is automation. `@[spec_transport]` lemmas are equations, and
`simp` chains equations, which is why `dirac_correct` is one line. The
support route's branch obligations are implications, which `simp`
cannot chain, so it gets an unpacker (`support_step`) and you write the
assembly step yourself. `Quicksort` carries all three proofs, side by
side, if you want to compare them: `quicksort_correct` (the default
recipe), `quicksort_correct_spec_of_branch_spec` (route A), and
`quicksort_sorted` plus `quicksort_correct_spec_of_support` (route B).
-/

/-- Correctness. For any lawful random monad and any lawful cost model,
`RandMax` returns exactly `listMax L`. The `LawfulMonadCost` hypothesis
is what makes this one statement cover the reading `TimeMT ℕ PMF`. -/
theorem randMax_correct
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M]
    (L : List α) :
    𝒟_{M}[RandMax L] = PMF.pure (listMax L) := by
  dirac_correct RandMax

/-- Correctness at `M = PMF` (where `toPMF` is the identity). -/
theorem randMax_correct_pmf (L : List α) :
    (RandMax L : PMF α) = PMF.pure (listMax L) :=
  randMax_correct (M := PMF) L

/-! ### 5b: the exact output distribution (`RandMember`)

Here, no point mass can describe the output and the theorem is the
distribution itself. For a `Bool`-valued algorithm that distribution
is a Bernoulli distribution, fixed by the probability of `true`.

Here is the code of this step:

```
theorem randMember_prob
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (x : α) (a : α) (L : List α) :
    ℙ_{M}[RandMember x (a :: L) = true] =
      (((a :: L).count x : ℕ) : ENNReal) / (((a :: L).length : ℕ) : ENNReal) := by
  simp only [RandMember]
  refine (toPMF_randIdx_bind_countP (M := M) (P := fun y => y == x) ?_).trans ?_
  · intro i; toPMF_step
  · simp [List.count]
```

`randMember_prob` is the theorem of this step. It says that
`RandMember x (a :: L)`, the algorithm of Step 1, answers `true` with
probability exactly `count x / n`.

Its proof rests on one counting principle, from
`AlgoLib/Theory/Randomized/Randomness/RandVec.lean`:

Note: other counting principles (like `toPMF_randVec_true`) live in
the same file, and the ones this tutorial does not use are listed in
"Where to go from here".

```
theorem toPMF_randIdx_bind_countP
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    {α : Type} {L : List α} {hL : 0 < L.length}
    {f : Fin L.length → M Bool} (P : α → Bool)
    (hf : ∀ i, 𝒟[f i] = PMF.pure (P L[i])) :
    ℙ[(randIdx L hL >>= f : M Bool) = true]
      = (L.countP P : ENNReal) / (L.length : ENNReal)
```

`L` is a non-empty list and `hL` proves it is non-empty.
`randIdx L hL` draws one position of `L`, uniformly. `f` says what to
do at the position drawn, and `>>=` chains the two: draw a position,
then run `f` there. The left-hand side is the probability that this
program answers `true`.

`P` is a test on elements, and the hypothesis `hf` says that the
branch at position `i` answers exactly `P L[i]`. So the program
answers `true` exactly when it drew a position whose element passes
the test, and its probability of doing so is the number of such
positions over the number of positions, `#{i | P L[i]} / |L|`. That
is "accepting choices over all choices", the Laplace probability
definition.

The theorem looks abstract, but read it twice and you will see that
it is concrete.

Read against `RandMember`: the list is `a :: L`, the predicate `P` is
`· == x`, and the branch `f` is what runs at the drawn index, a tick
and then the test. The count of accepting choices is then `L.count x`,
since `List.count x` is `List.countP (· == x)` by definition.

Back to the proof. Its first line unfolds one layer of the algorithm.

To apply the theorem, one thing has to be supplied: the predicate `P`.
The list, its non-emptiness and the branch all occur in the goal, so
Lean reads them from there.

Here `P` is naturally `· == x`.

Two goals remain, and both are short.

- `intro i; toPMF_step` proves `hf`, that the branch returns the value
  of the test. This is where the tick disappears, by the
  `LawfulMonadCost` axiom of Step 1.
- `simp [List.count]` does the count.

The tick is also why the theorem speaks of a branch `f` at all, rather
than of `P L[i]` directly: a branch is free to do more than test, and
`hf` is where that extra work is discharged.

Real examples: `reservoir_correct` (each element kept with probability
`count/n`) and `shuffle_uniform` (each permutation with probability
`1/n!`).
-/

omit [Inhabited α] in
/-- Exact output distribution. The test returns `true` with probability
`count x / n`. -/
theorem randMember_prob
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (x : α) (a : α) (L : List α) :
    ℙ_{M}[RandMember x (a :: L) = true] =
      (((a :: L).count x : ℕ) : ENNReal) / (((a :: L).length : ℕ) : ENNReal) := by
  simp only [RandMember]
  refine (toPMF_randIdx_bind_countP (M := M) (P := fun y => y == x) ?_).trans ?_
  · intro i; toPMF_step
  · simp [List.count]

/-! ### 5c: one-sided error, via the support (`RandMember`)

The support of a distribution is the set of outputs that can occur at
all. A statement about it is therefore of a different nature from a
probability bound: it holds on every run, with no probability
attached and no arithmetic to state it.

Here in `RandMember` the error goes in one direction only: the output
can be `false` while `x` is present (the draw simply missed it), but
never `true` while `x` is absent.

Here is the code of this step:

```
theorem randMember_sound
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (x : α) (L : List α) :
    ∀ b ∈ 𝒟_{M}[RandMember x L].support, b = true → x ∈ L := by
  intro b hb hbt
  subst hbt
  match L with
  | [] =>
    rw [RandMember.eq_1] at hb
    toPMF_step at hb
    simp at hb
  | a :: L =>
    rw [RandMember.eq_2] at hb
    obtain ⟨i, hi⟩ := mem_support_toPMF_randIdx_bind.mp hb
    toPMF_step at hi
    have hx : (a :: L)[(i : ℕ)] = x := by simpa using hi.symm
    exact List.mem_iff_getElem.mpr ⟨(i : ℕ), i.isLt, hx⟩
```

The statement quantifies over the support: for every output the
program can produce, if that output is `true` then `x` really is in
the list.

In the proof, `hb` is the assumption that `true` is reachable with input
`b`. On the empty list nothing is drawn and the answer is `false`, so
`hb` is absurd and `simp` closes the case. On `a :: L` the program draws
first, so `mem_support_toPMF_randIdx_bind` replaces "reachable by the
whole program" with "reachable by the branch at some position `i`",
and `i` is the position that answered `true`. `toPMF_step` reads that
answer, `(a :: L)[i] == x`, which gives `(a :: L)[i] = x`. A position
holding `x` is exactly what `List.mem_iff_getElem` needs.

The lemma we used belongs to the `mem_support_toPMF_*` family in
`AlgoLib/Theory/Randomized/Randomness/RandMonad.lean`. There is one
lemma per way of building a program, and each one turns "this output
is reachable" into a statement about the pieces the program is made
of.

- `mem_support_toPMF_pure`, for `pure a`: the only reachable output
  is `a`.
- `mem_support_toPMF_bind`, for `m >>= f`: an output is reachable
  when `m` can return some `a` and `f a` can then return that output.
- `mem_support_toPMF_bind_pure`, for a `do` block whose last line is
  `return (f x)`: an output is reachable when it is `f a` for some
  `a` that the block can reach.
- `mem_support_toPMF_seq₂`, for two computations combined by a pure
  function `g`: an output is reachable when it is `g a b` for some
  reachable `a` and some reachable `b`.
- `mem_support_toPMF_randIdx_bind`, for `randIdx L hL >>= f`: an
  output is reachable when some branch reaches it. The `bind` lemma
  above would also ask that the drawn index be reachable. Here that
  condition is gone, because a uniform draw reaches every position.
  This is the one used above.

With these lemmas we hope you can prove a support statement by peeling
the program one layer at a time and applying one of them at each layer.

`support_step` does that peeling in one call, for when you would
rather not pick the lemma at each layer. It is the support-tier twin
of `toPMF_step`: lawful ticks vanish, `toPMF` distributes, and the
draw disappears, since it reaches every position.

What it leaves is the hypothesis rewritten in terms of the pieces the
run is built from. In `Quicksort` it becomes "`S1` is reachable by the
recursive call on the `<`-side, `S2` is reachable by the call on the
`≥`-side, and the output is `S1 ++ pivot :: S2`". That is the
induction step of the textbook proof with the randomness gone, and the
inductive hypotheses now apply to `S1` and `S2` directly.

The mathematics is still yours to supply, as it was in Step 4. There
it was an equation tagged `@[spec_transport]`; here it is an
implication tagged `@[spec_preserve]`, saying that if the two sides
are sorted then so is the concatenation. `support_finish` does the
peeling and then chains those implications, which is why
`quicksort_sorted` closes its recursive case with the single line
`support_finish qs_branch at hS`.

Real examples: `karger_isCut` (every output is a genuine cut),
`freivalds_complete` and `schwartzZippel_complete` (never a false
"unequal" or "nonzero"), `support_shuffle` (every output is a
permutation), `quicksort_sorted` (every output is sorted). -/

omit [Inhabited α] in
/-- One-sided error. If the output is `true`, then `x` is in the list.
There are no false positives. -/
theorem randMember_sound
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (x : α) (L : List α) :
    ∀ b ∈ 𝒟_{M}[RandMember x L].support, b = true → x ∈ L := by
  intro b hb hbt
  subst hbt
  match L with
  | [] =>
    rw [RandMember.eq_1] at hb
    toPMF_step at hb
    simp at hb
  | a :: L =>
    rw [RandMember.eq_2] at hb
    obtain ⟨i, hi⟩ := mem_support_toPMF_randIdx_bind.mp hb
    toPMF_step at hi
    have hx : (a :: L)[(i : ℕ)] = x := by simpa using hi.symm
    exact List.mem_iff_getElem.mpr ⟨(i : ℕ), i.isLt, hx⟩

/-! ### 5d: success probability, then amplification (`RandMember`)

Two statements here: how often one run answers `true`, and how much
better `k` runs are.

Here is the code of this step:

```
theorem randMember_success
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (x a : α) (L : List α)
    (hx : x ∈ a :: L) :
    (1 : ENNReal) / (((a :: L).length : ℕ) : ENNReal) ≤
      ℙ_{M}[RandMember x (a :: L) = true] := by
  rw [randMember_prob]
  refine ENNReal.div_le_div_right ?_ _
  have hpos : 0 < (a :: L).count x := List.count_pos_iff.mpr hx
  exact_mod_cast hpos

theorem randMember_amplified
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (x : α) (L : List α)
    {p : ENNReal} (hp : p ≤ ℙ_{M}[RandMember x L = true]) (k : ℕ) :
    1 - (1 - p) ^ k ≤ ℙ_{M}[amplify (· || ·) k (RandMember x L) = true] :=
  amplify_or_success hp k
```

The first one is 5b read as an inequality. If `x` occurs in the list
then its count is at least one, so the probability of `true` is at
least `1/n`. The proof rewrites with `randMember_prob`, which is 5b's
equation `ℙ_{M}[RandMember x (a :: L) = true] = count x / n`. That
leaves two fractions with the same denominator, so it is enough to
compare the numerators.

The second one repeats. `amplify (· || ·) k m` runs `m` `k` times
independently and folds the answers with `||`, so the amplified run
answers `false` only when all `k` runs did. If one run answers `true`
with probability at least `p`, the failure probability is at most
`(1 - p)^k`, which is as small as you like for a cost linear in `k`.

This is where 5c is useful, and why repeating is a good strategy: the
error goes one way. An `||` can turn a `false` into a `true` but never
the reverse. Without a one-sided error, keeping any `true` would risk
keeping a wrong one.

The proof is a term, `amplify_or_success hp k`, because
`AlgoLib/Theory/Randomized/Correctness/Amplify.lean` proves the argument once
for a general combiner and then names the common cases.

- `amplify_success`, the general one: a combiner `best` that keeps a
  success when it sees one, and an invariant set the runs stay in.
- `amplify_or_success`, for a Boolean test: the combiner is `||` and
  no invariant is needed. This is the one used here.
- `amplify_min_success` and `amplify_max_success`, when the answers
  are ordered and one keeps the smallest or the largest.
- `amplify_argmin_success`, when a run reports a witness together
  with its value, and one keeps the witness of smallest value.

`Karger` uses the last one: a run reports a cut and the value of that
cut, so its combiner is `argmin Prod.snd` rather than `min`.

Real examples: `karger_success_prob` and `karger_finds_min`, then
`karger_amplified`. `freivalds_sound` and `schwartzZippel_sound` bound
the error of one run. -/

omit [Inhabited α] in
/-- Success probability. If `x` occurs in the list, one test finds it
with probability at least `1/n`. -/
theorem randMember_success
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (x a : α) (L : List α)
    (hx : x ∈ a :: L) :
    (1 : ENNReal) / (((a :: L).length : ℕ) : ENNReal) ≤
      ℙ_{M}[RandMember x (a :: L) = true] := by
  rw [randMember_prob]
  refine ENNReal.div_le_div_right ?_ _
  have hpos : 0 < (a :: L).count x := List.count_pos_iff.mpr hx
  exact_mod_cast hpos

omit [Inhabited α] in
/-- Amplified. `k` independent runs, combined with `||`, return `true`
with probability at least `1 - (1 - p)^k`. -/
theorem randMember_amplified
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (x : α) (L : List α)
    {p : ENNReal} (hp : p ≤ ℙ_{M}[RandMember x L = true]) (k : ℕ) :
    1 - (1 - p) ^ k ≤ ℙ_{M}[amplify (· || ·) k (RandMember x L) = true] :=
  amplify_or_success hp k

-- done until here (the "human" reading: to be continued)

/-!
## Step 6: expected cost

6. Cost is opt-in. An algorithm that never ticks costs nothing to
  state and nothing to prove, and `RandPick` below is the one-line
  demonstration. Where you do tick, `𝔼_{M}[cost e]` reads the code at
  `TimeMT ℕ M`, takes the distribution of the (output, cost) pair,
  and averages the cost component.

  Costs live in `ENNReal`, which is why no summability side condition
  ever appears: every sum converges, possibly to `∞`, and a proof
  never has to stop to justify itself. Descend to `ℝ` with `toReal`
  at the very end, and only if the closed form needs subtraction (see
  `quicksort_cost_exact`).

  The three toys show the three shapes a cost proof takes. `RandMax`
  recurses, so it needs the full pattern, one lemma per stage:

  - the branch cost, by `cost_step`. The tactic peels the `TimeMT`
    combinators one at a time: a `tick t` contributes `t`, a `pure`
    contributes `0`, a `bind` adds the two. The trailing
    `return max L[i] m` is therefore free, and the branch costs
    `1 + 𝔼[cost RandMax (L.eraseIdx i)]`.
  - the recurrence, by `expected_cost_uniform_step'`. This is the
    one place where uniformity of the draw is used: the cost of
    "draw an index, then run the branch" is the uniform average of
    the branch costs, `E(n) = (1/n) Σᵢ (1 + E(n-1))`.
  - the closed form, by induction along `RandMax.induct`, the
    functional-induction principle Lean derives from the definition
    itself. Its cases are the algorithm's cases, so the induction can
    never drift out of step with the recursion. Here every branch
    recurses on `n - 1` elements, so the average is an average of `n`
    copies of `n`, and `uniform_avg_eq_of_forall` closes it.

  `RandMember` ticks once and stops, so its cost proof is a single
  `cost_step`. `RandPick` never ticks, so its cost is `0`: cost is
  charged where `tick` appears and nowhere else.

  The shape `expected_cost_uniform_step'` expects is convenient, not
  mandatory. `cost_step` reduces any branch, and a recursion whose
  branches differ in size reindexes the sum instead. See "Where to
  go from here".

  Real examples: `quicksort_cost_exact` and `quickselect_cost_exact`
  for the recurrence, `karger_cost_le` for an upper bound,
  `reservoir_cost_exact` and `freivalds_cost_exact` for a single
  pass, and `couponCollector_cost_exact` for a cost assembled from
  stages.
-/

private lemma expected_cost_randMax_branch
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (L : List α) (i : Fin L.length) :
    𝔼_{M}[cost randMax_branch (TimeMT ℕ M) L i] =
    1 + 𝔼_{M}[cost RandMax (L.eraseIdx i)] := by
  unfold randMax_branch
  cost_step

private lemma expected_cost_randMax_step
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (head : α) (tail : List α) :
    𝔼_{M}[cost RandMax (head :: tail)] =
    ((head :: tail).length : ENNReal)⁻¹ *
      ∑ i : Fin (head :: tail).length,
        (1 + 𝔼_{M}[cost RandMax ((head :: tail).eraseIdx i)]) := by
  rw [RandMax.eq_2]
  exact expected_cost_uniform_step' (by simp)
    fun i => expected_cost_randMax_branch (head :: tail) i

private lemma expected_cost_randMax_nil
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M] :
    𝔼_{M}[cost RandMax ([] : List α)] = 0 := by
  -- `cost_step RandMax` unfolds one layer of `RandMax` (its equation
  -- lemmas), then reduces. No compiler-generated `.eq_1` name needed.
  cost_step RandMax

/-- Exact expected cost. `RandMax` performs exactly `n` comparisons in
expectation, and in fact on every run: one per round, `n` rounds. -/
theorem randMax_cost_exact
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (L : List α) :
    𝔼_{M}[cost RandMax L] = (L.length : ENNReal) := by
  induction L using RandMax.induct with
  | case1 =>
    rw [expected_cost_randMax_nil]
    simp
  | case2 head tail ih =>
    rw [expected_cost_randMax_step head tail]
    -- Every branch recurses on `tail.length` elements.
    have hterm : ∀ i : Fin (head :: tail).length,
        1 + 𝔼_{M}[cost RandMax ((head :: tail).eraseIdx i)] =
        ((head :: tail).length : ENNReal) := by
      intro i
      rw [ih i, length_eraseIdx_cons]
      simp only [List.length_cons]
      push_cast
      ring
    -- So the average of `n` copies of `n` is `n`.
    exact uniform_avg_eq_of_forall hterm

omit [Inhabited α] in
/-- Cost of one test. One tick, independent of the list length. -/
theorem randMember_cost
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (x a : α) (L : List α) :
    𝔼_{M}[cost RandMember x (a :: L)] = 1 := by
  rw [RandMember.eq_2]
  cost_step

omit [LinearOrder α] in
/-- `RandPick` has no tick, so its cost is `0`. -/
theorem randPick_cost_zero
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (L : List α) :
    𝔼_{M}[cost RandPick L] = 0 := by
  match L with
  | [] => cost_step RandPick
  | a :: L => rw [RandPick.eq_2]; cost_step

/-!
## Step 7: the cost distribution (determinism)

7. An expectation is one number, and one number hides a great deal:
  the same average is compatible with any amount of spread. `costPMF`
  is the whole law of the cost, which makes it the strongest of the
  three cost statements and the only one that can express
  determinism.

  `RandMax` ticks once per round and never stops early, so it performs
  exactly `n` comparisons on every run, not merely on average. The
  theorem below says precisely that: the cost distribution is a point
  mass at `L.length`. Its proof follows the same skeleton as the
  expected cost (induct along `RandMax.induct`, peel one draw), but
  with the `costPMF` lemmas in place of the averaging ones, and
  `costPMF_lift_bind_const` where the uniform average used to be:
  every branch has the same cost law, so the value drawn does not
  matter at all.

  Real examples: `freivalds_costPMF` and `schwartzZippel_costPMF`
  (cost `3n²` and `1` on every run), `reservoir_costPMF` (exactly
  `n - 1` ticks), `costPMF_shuffle` (cost `0` on every run).
-/

/-- Deterministic cost. The cost distribution of `RandMax` is the point
mass at `L.length`: every run performs exactly `n` comparisons. -/
theorem randMax_costPMF
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    (L : List α) :
    costPMF (RandMax L : TimeMT ℕ M α) = PMF.pure L.length := by
  induction L using RandMax.induct with
  | case1 => exact costPMF_eq_pure_zero (by cost_step RandMax)
  | case2 head tail ih =>
    rw [RandMax.eq_2, randIdx_timeMT]
    refine costPMF_lift_bind_const _ _ fun i => ?_
    rw [MonadCost.tick_timeMT, costPMF_tick_bind, costPMF_bind_pure, ih i,
      PMF.pure_map, length_eraseIdx_cons]
    simp [Nat.add_comm]

/-!
## Step 8: a tail bound, for free

8. Markov's inequality turns any expected-cost theorem into a
  statement about how often the cost is large, and the framework
  applies it for you: no induction, no new lemma, one rewrite.

  `runtime_markov_gt` is stated in the strict form
  `ℙ[cost m > k] ≤ 𝔼[cost m] / (k + 1)`. Because costs are ℕ-valued,
  `cost > k` is the same event as `cost ≥ k + 1`, which makes this
  version both sharper than the textbook `𝔼/k` and free of its
  `k ≠ 0` side condition.

  A tail bound is the weakest of the three cost statements, since it is
  implied by the expectation, which is exactly why it costs one line
 , but it is the one that reads as a running-time guarantee. When
  the expectation alone gives too weak a tail, the second moment is
  available: `variance` and `runtime_chebyshev`, in
  `AlgoLib/Theory/Randomized/Complexity/Variance.lean`.

  Real example: `quicksort_runtime_tail`, obtained the same way from
  `quicksort_cost_le`.
-/

/-- Tail bound. The cost exceeds `k` with probability at most
`n/(k+1)`. Obtained from `randMax_cost_exact` alone. -/
theorem randMax_cost_tail
    {M} [Monad M] [LawfulMonad M] [LawfulRandMonad M]
    (L : List α) (k : ℕ) :
    ℙ[cost (RandMax L : TimeMT ℕ M α) > k] ≤ (L.length : ENNReal) / (k + 1) := by
  have h := runtime_markov_gt (RandMax L : TimeMT ℕ M α) k
  rwa [randMax_cost_exact] at h

/-!
## Step 9: averaging something that is not a cost

9. Not every expectation is a running time. When the quantity to
  average is a function of the output, the height of a random
  tree, the size of a random cut, the tool is `expVal`, with the
  same `pure`/`bind`/uniform decomposition API as expected cost
  applied to the output instead of the clock. It sits one layer below
  the cost machinery, in `AlgoLib/Theory/Randomized/Randomness/Prob.lean`,
  so a purely probabilistic case study never has to import the cost
  layer at all.

  The theorem below is the uniform case, and it is the whole of
  `RandPick`'s analysis: the average of `g` over a uniformly drawn
  element is the uniform average of `g` along the list.

  Real example: `treap_expected_height_le`, which bounds `𝔼[height]`
  by first bounding the exponential moment `𝔼[2^height]`
  (`treap_expVal_exp_height`), an argument entirely about the output,
  which never mentions cost.
-/

omit [LinearOrder α] in
/-- Expectation of a function of the output: the average of `g` over
the drawn element is the uniform average of `g` along the list. -/
theorem expVal_randPick
    {M} [Monad M] [LawfulMonad M] [inst : LawfulRandMonad M]
    [MonadCost ℕ M] [LawfulMonadCost ℕ M] (a : α) (L : List α)
    (g : α → ENNReal) :
    expVal 𝒟_{M}[RandPick (a :: L)] g =
      (((a :: L).length : ℕ) : ENNReal)⁻¹ *
        ∑ i : Fin (a :: L).length, g ((a :: L)[i]) := by
  rw [RandPick.eq_2, expVal_toPMF_randIdx_bind]
  exact congrArg _ (Finset.sum_congr rfl fun i _ => expVal_toPMF_pure _ _)

/-!
## Where to go from here

The three toys were chosen to be small, and being small they leave a
good part of the framework unused. This last section is a map of what
they do not show, with a pointer for each.

### Other sources of randomness

`randIdx` is one sampler among several.
`AlgoLib/Theory/Randomized/Randomness/RandVec.lean` provides three tiers, each
with its own counting principle of the shape "a test accepts with
probability `#accepting / #choices`":

* the list tier, the one used above: `randIdx`, with
  `toPMF_randIdx_bind_countP`, giving `L.countP P / |L|`;
* the bit tier: `randBit`, and `randVec n` for a uniform `0/1` vector,
  with `toPMF_randVec_true` and `toPMF_randVec_true_card`, giving
  `#accepting / 2^n`. `Freivalds` is the client;
* the grid tier: `randElem`, a uniform element of an arbitrary
  non-empty `Finset`, and `randVecOn`, a vector of independent such
  draws, with `toPMF_randVecOn_true`, giving `#accepting / #s^n`.
  `SchwartzZippel` is the client.

None of these samplers ticks, and
`AlgoLib/Theory/Randomized/Complexity/SamplerCosts.lean` says so once and for
all. Its four lemmas are tagged `@[expected_cost_simp]`, so `cost_step`
alone closes the cost proof of any algorithm whose only randomness
comes from them. This is why `freivalds_cost_exact` and
`schwartzZippel_cost_exact` are a single tactic call each, where Step 6
needed three lemmas and an induction.

### Proving a success probability in general

Step 5d read its bound off the exact distribution of 5b, which was
possible only because `RandMember` is simple enough to have one. The
general route is `le_toPMF_randIdx_bind`: it lower-bounds the success
probability by exhibiting a single good draw, and this is how
`karger_success_prob` is proved.

Its exact counterpart is `toPMF_randIdx_bind_apply`, the probabilistic
twin of `expected_cost_uniform_step`: the output probability is the
uniform average of the branch probabilities. `FisherYates` uses it.

### What amplification costs

Step 5d repeats a run `k` times and never says what that costs.
`expected_cost_amplify` says it: `k + 1` runs cost `k + 1` times one
run. `Karger` uses it to turn a success bound and a cost bound into
the two bounds of the amplified algorithm.

### Second moments

Step 8 stops at the first moment.
`AlgoLib/Theory/Randomized/Complexity/Variance.lean` carries the second:
`variance`, written with `absSub` (notation `⊖`) because `ENNReal` has no
subtraction, the classical identity `variance_eq_sub`
(`Var[g] = E[g²] − E[g]²`), and `chebyshev`
(`ℙ(|g − E[g]| ≥ k) ≤ Var[g] / k²`). Its cost form is
`runtime_chebyshev`, and it improves on Markov whenever the expectation
alone gives too weak a tail.

### Loops that retry until they succeed

A `PMF` has total mass `1`, so a computation that terminates only
almost surely does not fit in one.
`AlgoLib/Theory/Randomized/FutureWork/SPMF.lean` opens that door with
`SPMF := OptionT PMF`, whose `mass` is the termination probability.
`RetryMonad` provides the loop, `retry_run_some_of_good` and
`retry_run_some_of_not_good` give its output law, and
`mass_retry_eq_one` is the Las Vegas theorem: retrying a total program
with positive success probability terminates almost surely.

The cost side of that tier is
`AlgoLib/Theory/Randomized/Randomness/Geometric.lean`: `geometric` is the law
of the failure count, `geometricTrials` the law of the trial count, and
`mean_geometricTrials` is the `1/p` that every retry analysis consumes.

`CouponCollector` is the case study, and it is the one file of
`AlgoLib/Algorithms/Randomized` that deliberately bypasses the program layer. "Draw
until a new coupon appears" is not a structurally terminating Lean
program, so that file states its cost law directly, composing
`geometricTrials` stages with `bind`.

### More of the recipe

* Case splits inside a branch. `dirac_correct` performs the split and
  reads the guards off the hypotheses; supply one `@[spec_transport]`
  lemma per case, with hypotheses matching those guards. Either
  orientation works, as long as the rewrite terminates. See
  `quickselect_correct`.
* Branches of unequal size. `RandMax` recurses on `n - 1` whatever it
  draws, which is why its recurrence collapsed to an average of equal
  terms. When the size of a branch depends on the element drawn,
  reindex the recurrence sum by the rank of that element, with
  `nodup_partition_sum₂`. See the exact cost proofs of `Quicksort` and
  `Quickselect`.
* Upper bounds instead of exact formulas. Stay in `ENNReal` and close with
  `uniform_avg_le`; finiteness then follows from the bound itself, and
  `toReal_uniform_avg` descends to `ℝ`. See
  `quickselect_cost_le_quadratic`.

### More of the API

* The event algebra of `prob`: `prob_compl_eq_one_sub`,
  `prob_add_compl`, `prob_mono` and `prob_bind`, in
  `AlgoLib/Theory/Randomized/Randomness/Prob.lean`.
* More of `expVal` than Step 9 uses: the tower rule `expVal_bind`,
  together with `expVal_mono`, `expVal_add` and `expVal_const_mul`,
  which is what `treap_expected_height_le` actually runs on.
* `runtime_markov`, the `≥` form of the tail bound of Step 8.
* `mem_support_timedPMF`, which carries a support invariant proved at
  an abstract `M` into the timed reading.

### The nine case studies

Each file of `AlgoLib/Algorithms/Randomized` is a worked example, and together they
cover the tiers this tutorial only sketches:

* `Quicksort`: Dirac correctness and an exact expected cost, with
  branches of unequal size.
* `Quickselect`: the same, with a three-way case split in the branch,
  and an upper bound next to the exact formula.
* `Karger`: the full Monte Carlo stack on a real algorithm: support,
  success probability, amplification and cost.
* `Freivalds`: the bit-vector sampler, one-sided error, and a cost
  that is the same on every run.
* `SchwartzZippel`: the grid sampler, with the same three statements.
* `ReservoirSampling`: an exact output distribution, an exact cost,
  and a cost law.
* `FisherYates`: a uniform permutation as output law, and cost `0`.
* `Treap`: `expVal` on a functional of the output, the expected height
  of a random tree.
* `CouponCollector`: the cost-law tier, with no program layer at all.
-/

end AlgoLib
