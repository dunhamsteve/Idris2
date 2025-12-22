data Bar : Nat -> Type where
  B : Unit -> Bar n

Bars : Type
Bars = (
      (Bar 4, Bar 120)
    , (Bar 120, Bar 84)
    , (Bar 84, Bar 2)
  )

bar : (a, b, c, d, e : Unit) -> Unit

foo : Bars -> Unit
foo ((B a, B b), (B c, B d), (B e, B f)) =  id $ bar a b c d e

