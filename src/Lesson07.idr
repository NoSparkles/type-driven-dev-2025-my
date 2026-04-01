module Lesson07

namespace TypesAreStatements
    namespace Implication
        apply : (a -> b) -> a -> b
        apply f x = f x

        trans : (a -> b) -> (b -> c) -> a -> c
        trans f g x = g (f x)


        ylppa : (a -> b) -> b -> a
        ylppa f x = ?fsd

        ylppa' : (String -> Nat) -> Nat -> String
        ylppa' f k = ""

    namespace Conjuction
        fst : (a, b) -> a
        fst (x, y) = x

        snd : (a, b) -> b
        snd (x, y) = y

        pair : a -> b -> (a, b)
        pair x y = (x, y)

    namespace BoolValues
        tt : ()
        tt = ()

        ff : Void

    namespace Disjunction
        opt_a : a -> Either a b
        opt_a x = Left x

        opt_b : b -> Either a b
        opt_b x = Right x

        disj_elim : (a -> q) -> (b -> q) -> Either a b -> q
        disj_elim f g (Left x) = f x
        disj_elim f g (Right x) = g x

    namespace Negation
        contra_pos : (a -> b) -> (Not b -> Not a)
        contra_pos f g x = g (f x)

th1 : a -> b -> Either (Not a) b
th1 x y = Right y

th1' : (a -> b) -> Either (Not a) b
th1' f = ?th1'_rhs

th2 : Either (Not a) b -> a -> b
th2 (Left x) y = void (x y)
th2 (Right x) y = x

th3 : (p, q) -> Either p q
th3 (x, y) = Left x

th4 : Either (p, q) r -> (Either p r, Either q r)
th4 (Left x) = (Left (fst x), Left (snd x))
th4 (Right x) = (Right x, Right x)

th5 : (Either p r, Either q r) -> Either (p, q) r
th5 ((Left x), (Left y)) = Left (x, y)
th5 ((Left x), (Right y)) = Right y
th5 ((Right x), (Left y)) = Right x
th5 ((Right x), (Right y)) = Right x

th6 : Not p -> Not (p, q)
th6 f (x, y) = f x

th7 : (p -> Not p) -> Not p
th7 f x = f x x

th8 : Not (p -> q) -> Not q
th8 f x = f (\_ => x)

th9 : Not (p, q) -> (p -> Not q)
th9 f x y = f (x, y)

th10 : Not (Either (p, Not p) (q, Not q))
th10 (Left (x, y)) = y x
th10 (Right (x, y)) = y x

th11 : p -> Not (Not p)
th11 x f = f x

