%default total
%logging "elab.case" 10
interface Test t a where
    test : (a -> Bool) -> t -> Bool

%tcinline
test2 : (t : Test s a) => (a -> Bool) -> a -> s -> Bool
-- test2 f x y = f x && test f y -- compiles
test2 f x y = -- doesn't compile
    let True = test f y
        | False => False
     in f x

Test (List a) a where
    test f [] = True
    test f (x :: xs) = test2 f x xs
