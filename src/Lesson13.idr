module Lesson13

import Data.Vect

%default total

f1 : Vect n a
f1 = ?f1_rhs

f2 : {n : _} -> {a : _} -> Vect n a
f2 = ?f2_rhs

f2' : {0 n : _} -> {a : _} -> Vect n a
f2' = ?f2'_rhs

f2'' : {0 n : _} -> {a : _} -> Vect n a
f2'' {n} = f1 {n=n}


data Drill = MkDrill

destroyDrill : (1 _ : Drill) -> ()
destroyDrill MkDrill = ()
