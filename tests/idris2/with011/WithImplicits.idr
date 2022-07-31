import Decidable.Equality


test : {eg : DecEq a}  ->  (x : a) -> List a -> Bool
test x ys with (ys)
    _ | [] = False
    _ | (y :: ys') with (decEq x y)
        _ | Yes prf = True
        _ | No contra = (test x (y :: ys') | ys')
