/-!
# Const Functor

The `Const` functor ignores its second type parameter, useful for implementing
optics operations like `Forget` for traversals.
-/

namespace Collimator.Control

universe u

/--
`Const α β` is definitionally equal to `α`, ignoring the `β` parameter.
This is useful for accumulating values during traversals.
-/
def Const (α : Type u) (_β : Type u) : Type u := α

instance {α : Type u} : Functor (Const α) where
  map _ x := x

/--
Extract the underlying value from a `Const`.
-/
def Const.get (c : Const α β) : α := c

/--
Wrap a value in `Const`.
-/
def Const.mk (a : α) : Const α β := a

/--
`Applicative` instance for `Const` requires `One` and `Mul` on the carrier type.
- `pure` returns the unit element (ignoring its argument)
- `seq` combines values using multiplication
-/
instance {α : Type u} [One α] [Mul α] : Applicative (Const α) where
  pure _ := Const.mk 1
  seq f x := Const.mk (Const.get f * Const.get (x ()))

end Collimator.Control
