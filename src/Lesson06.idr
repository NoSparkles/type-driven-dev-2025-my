module Lesson06

import Data.Vect
import Decidable.Equality

rt : 1 = 1
rt = Refl

t' : Void -> Int
t' _ = 42

t1 : Void -> 3 = 3
t1 x = Refl

t2 : Void -> 2 = 3
t2 x impossible

t3 : 2 = 3 -> Void
t3 Refl impossible

failing
    t4 : 2 = 2 -> Void
    t4 Refl impossible
    

zeroNotSucc : 0 = S k -> Void
zeroNotSucc Refl impossible

succNotZero : S k = 0 -> Void
succNotZero Refl impossible

norec : (k = j -> Void) -> S k = S j -> Void
norec f Refl = f Refl

checkEqNat : (nat1 : Nat) -> (nat2 : Nat) -> Dec(nat1 = nat2)
checkEqNat 0 0 = Yes Refl
checkEqNat 0 (S k) = No zeroNotSucc 
checkEqNat (S k) 0 = No succNotZero
checkEqNat (S k) (S j) = case checkEqNat k j of
                    (Yes prf) => Yes (cong S prf)
                    (No contra) => No (norec contra)

exactLen : {len2 : Nat} -> (len1 : Nat) -> Vect len2 a -> Maybe (Vect len1 a)
exactLen {len2} len1 xs = case checkEqNat len1 len2 of
                    (Yes Refl) => Just xs
                    (No contra) => Nothing


exactLen' : {len2 : Nat} -> (len1 : Nat) -> Vect len2 a -> Maybe (Vect len1 a)
exactLen' {len2} len1 xs = case decEq len1 len2 of
                    (Yes Refl) => Just xs
                    (No contra) => Nothing

--- more sophisticated

test0 : plus 1 len = S len
test0 = Refl

test1 : plus len 1 = S len
test1 = ?test1_rhs

plus1NComm : (a : Nat) -> plus 1 a = plus a 1
plus1NComm 0 = Refl
plus1NComm (S k) = plusCommutative 1 (S k)

fixMath : Vect (plus len 1) a -> Vect (plus 1 len) a
fixMath xs = rewrite plus1NComm len in xs

myReverse : {n : Nat} -> Vect n a -> Vect n a
myReverse [] = []
myReverse (x :: xs) = fixMath (myReverse xs ++ [x])

th : {n : Nat} -> {m :Nat} -> n = m -> n + n = m + m
th prf = rewrite prf in Refl

plusNZ : (n : Nat) -> plus n Z = n
plusNZ 0 = Refl
plusNZ (S k) = let indH = plusNZ k in (cong S indH)


skIsPlusK1 : S (S k) = S (plus k 1)
skIsPlusK1 = rewrite plusCommutative k 1 in Refl

th2 : (n : Nat) -> (m : Nat) -> S (n + m) = n + S m
th2 0 m = Refl
th2 (S k) m = 
            let indH = th2 k m in
            rewrite indH in Refl



plusComm : (a, b : Nat) -> a + b = b + a
plusComm 0 b = rewrite plusNZ b in Refl 
plusComm (S k) b = 
    let indH = plusComm k b in 
    rewrite indH in
    rewrite th2 b k in
    Refl


append_nil_rhs_0 : Vect m a -> Vect (plus m 0) a
append_nil_rhs_0 xs = rewrite plusNZ m in xs

fix : Vect (S (plus m len)) a -> Vect (plus m (S len)) a
fix xs = rewrite sym (plusSuccRightSucc m len) in xs

append : Vect n a -> Vect m a -> Vect (m + n) a
append [] ys = append_nil_rhs_0 ys
append (x :: xs) ys = fix (x :: append xs ys)
