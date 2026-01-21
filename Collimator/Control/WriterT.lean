/-!
# WriterT Monad Transformer

Minimal implementation of the Writer monad transformer for logging/accumulation.
-/

namespace Collimator.Control

universe u v

/--
`WriterT ω M α` is a monad transformer that threads an accumulated log of type `ω`
through a computation in monad `M`, producing a result of type `α`.
-/
structure WriterT (ω : Type u) (M : Type u → Type v) (α : Type u) : Type v where
  run : M (α × ω)

namespace WriterT

variable {ω : Type u} {M : Type u → Type v} {α β : Type u}

instance [Functor M] : Functor (WriterT ω M) where
  map f x := mk (Functor.map (fun (a, w) => (f a, w)) x.run)

instance [Pure M] [EmptyCollection ω] : Pure (WriterT ω M) where
  pure a := mk (Pure.pure (a, ∅))

instance [Monad M] [Append ω] : Seq (WriterT ω M) where
  seq wf wa := mk do
    let (f, w1) ← wf.run
    let (a, w2) ← (wa ()).run
    pure (f a, w1 ++ w2)

instance [Monad M] [EmptyCollection ω] [Append ω] : Applicative (WriterT ω M) where
  pure := Pure.pure
  seq := Seq.seq

instance [Monad M] [EmptyCollection ω] [Append ω] : Monad (WriterT ω M) where
  bind x f := mk do
    let (a, w1) ← x.run
    let (b, w2) ← (f a).run
    pure (b, w1 ++ w2)

/-- Append a value to the log. -/
@[inline]
def tell [Pure M] [EmptyCollection ω] [Append ω] (w : ω) : WriterT ω M PUnit :=
  mk (Pure.pure (⟨⟩, w))

end WriterT

/-- Append a value to the log (top-level function). -/
@[inline]
def tell {ω : Type u} {M : Type u → Type v} [Pure M] [EmptyCollection ω] [Append ω]
    (w : ω) : WriterT ω M PUnit :=
  WriterT.tell w

end Collimator.Control
