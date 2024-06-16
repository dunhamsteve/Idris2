foo : Nat -> Nat
foo x = let n = if x == 42
        then pure 0
        else 1
        in x * n
