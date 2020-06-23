import Data.List
import Data.List.Elem

||| Proof that an element is still inside a list if we append to it.
export
total
elemAppLeft : (ys : List a) -> (prf : Elem x xs) -> Elem x (xs ++ ys)
elemAppLeft {xs} [] prf =
  rewrite appendNilRightNeutral xs in prf
elemAppLeft _ Here = Here
elemAppLeft ys (There prf) = There $ elemAppLeft ys prf

||| Proof that an element is still inside a list if we prepend to it.
export
total
elemAppRight : {xs : List a} -> (ys : List a) -> (prf : Elem x xs) -> 
               Elem x (ys ++ xs)
elemAppRight [] prf = prf
elemAppRight {xs = []} ys prf = absurd prf
elemAppRight {xs = (x::xs)} [] prf = prf
elemAppRight {xs = (x::xs)} (y :: ys) prf = There $ elemAppRight ys prf

||| Proof that membership on append implies membership in left or right sublist.
export
total
elemAppLorR : (xs, ys : List a) -> (prf : Elem k (xs ++ ys)) -> 
              Either (Elem k xs) (Elem k ys)
elemAppLorR [] [] prf = absurd prf
elemAppLorR [] _ prf = Right prf
elemAppLorR (x :: xs) [] prf = Left prf'
  where
    prf' : Elem k (x :: xs)
    prf' = replace {p = \q => Elem k q} (appendNilRightNeutral (x :: xs)) prf
elemAppLorR (x :: xs) _ Here = Left Here
elemAppLorR (x :: xs) ys (There prf) =
  case ih of
    (Left l) => Left $ There l
    (Right r) => Right r
  where
    ih : Either (Elem k xs) (Elem k ys)
    ih = elemAppLorR xs ys prf
