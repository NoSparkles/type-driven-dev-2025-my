module Lesson08
import Decidable.Equality
import Data.Nat -- LTE/GTE
%default total


-- ((a -> b) -> (~a \/ b))
-- a = b ==>  (~a \/ a)


namespace OnForall
    {-  Look at these:

            a ∈ Nat ⇒ a ≥ 0         (a is implicitly bound)
            ∀ a ∈ Nat : a ≥ 0       (bounded quantification)

        We can extend them to:

            ∀ a ∈ Nat : a ≥ 0  -->  ∀ a. a ∈ Nat ⇒ a ≥ 0
            a ∈ Nat ⇒ a ≥ 0    -->  ∀ a. a ∈ Nat ⇒ a ≥ 0

        Both of them actually stand for the universal quantification.
    -}

    {-  The above looks very similar to the implication!

        See (https://ncatlab.org/nlab/show/propositional+logic+as+a+dependent+type+theory).
        The exact inference rules differ a bit. Ignoring definition of ∈,
        the overall structure of the rules is similar.
        The main difference is between `B` and `B(x)`.

        Introduction rules:

               Γ,x : A ⊢ b(x) : B
            ------------------------ (⇒-Intro)
             Γ ⊢ (x↦b(x)) : A⇒B

                Γ,x∈A ⊢ b(x) : B(x)
            ---------------------------- (∀-Intro)
              Γ ⊢ λx.b(x) : ∀x∈A.B(x)

        Elimination rules:

              Γ ⊢ f : A⇒B    Γ ⊢ a : A
            ----------------------------- (⇒-Elim)
                     Γ ⊢ f(a) : B

             Γ ⊢ f : ∀x∈A.B(x)    Γ ⊢ a∈A
            ---------------------------------- (∀-Elim)
                   Γ ⊢ f(a) : B[a/x]

        Thus `⇒` is a specific case of , where the type `B` does not depend on `a:A`.
        I.e simply-typed function can model only implication, and the dependently-typed
        function can also model `∀`.
    -}

    mp : a -> (a -> b) -> b
    mp x f = f x

    {- And now, there is an example with forall:

        ∀ f ∈ a->b, x,y ∈ a.
            (x = y) ⇒ (f x = f y)

        The resulting type depends on `f`, `x` and `y`, but not on `x = y`.
    -}
    fa : (f : a -> b) -> (x : a) -> (y : a) -> (x = y) -> ((f x) = (f y))
    fa f x x Refl = Refl

namespace OnExists

    {-  In classical logic ∃ can be proved in 2 ways:
            a) ¬∀x. ¬P(x) ⇒ ∃x. P(x)
            b) find such `a` that `P(a)`, then
               P(a) ⇒ ∃x. P(x)

        The first one is non-constructive.
        The only thing that left -- the second one.

        Let's look at the intro/elim rules.
        See (https://ncatlab.org/nlab/show/propositional+logic+as+a+dependent+type+theory).

                Γ ⊢ A type      Γ,x∈A ⊢ B(x) prop
            ----------------------------------------- (∃-Intro)
             Γ, x∈A, y∈B(x) ⊢ in(x,y) : ∃x∈A.B(x)

        I.e. if we have type A and dependent type B(x),
        then from `x` and `y` we can construct a dependent pair.
    -}
    exIntro : {a : Type} -> {b : a -> Type} -> (x : a) -> (y : b x) -> (x' : a ** b x')
    exIntro x y = (x ** y) -- NOTE: Difference between the value and type, : is required in type.

    {-  Now let's see to the elimination rule.

             Γ                  ⊢ A type      -- Type A exists.
             Γ,            x∈A ⊢ B(x) prop    -- Dependent type B(x) exist.
             Γ,   z:∃x∈A.B(x) ⊢ C(z) prop     -- Dependent type C(z) exist.
             Γ,   x∈A, y∈B(x) ⊢ c:C(in(x,y))
            ----------------------------------------------------- (∃-Elim)
             Γ, z:∃x∈A.B(x) ⊢ ind^C_(∃x∈A.B(x))(c)(z) : C(z)

        First premises are described inline.
        The 4-th premise: from x and y can construct a proof of C() whose type depends on in(x,y).
        The conclusion can be read as: from proof z of ∃ we have proof of C(z).
        I.e. we will obtain `x` and `y` from `z`, and by 4-th p. we will get c.

        `in(x, y)` is known as a dependent pair.
        `ind^C_T` identifies an element `z` proving `C(z)`?
    -}

    {- Example, start with particular types:

        (∃ n∈Nat. n+n=n*n) ∧ (m+m=m*m ⇒ j=13) ⇒ j=13

            - take such `n` from ∃ and the proof of `n+n=n*n`.
            - use that proof to obtain j=13.
            - Return j=13.

        Thus, we return a facts that's not dependent on `n` (stands for `C`),
        but `B(n)=n+n=n*n` was needed to obtain `C`.
    -}
    exElim'' :
        {j : Nat} ->
        ({m : Nat} -> (m+m=m*m) -> j = 13) ->
        (n : Nat ** (n+n=n*n)) ->
        j = 13
    exElim'' f (fst ** snd) = f snd

    {-  We can replace concrete types with abstract ones:
        First introduce `a : Type`, `b : a -> Type`.
         - `j=13 : Type` ---> `c : Type`,
         - `n : Nat` ---> `x : a`, and `n+n=n*n` ---> `b x`
         - `m : Nat` ---> `x : a`, and `m+m=m*m` ---> `b x`
    -}
    exElim' :
        {a : Type} ->           -- Type A exists.
        {b : a -> Type} ->      -- Dependent type B(x) exist.
        {c : Type} ->           -- That's the type of final fact we want to prove.
        ({x1 : a} -> (y : b x1) -> c) -> -- x∈A, y∈B(x) ⊢ c:C(in(x,y))
        (z : (x : a ** b x)) ->  -- From the proof z:∃x∈A.B(x)
        c
    exElim' f (fst ** snd) = f snd

    {-  Make c dependent on (x**y).
    -}
    exElim :
        {a : Type} ->           -- Premise 1: Type A exists.
        {b : a -> Type} ->      -- Premise 2: Dependent type B(x) exist.
        {c : (x : a ** b x) -> Type} -> -- Premise 3: Dependent type of thing to prove.
        ({x : a} -> (y : b x) -> c (x ** y)) -> -- Premise 4: x∈A, y∈B(x) ⊢ c:C(in(x,y))
        (z : (x : a ** b x)) -> -- Antecedent in conclusion, `z:∃x∈A.B(x)`.
        c z                     -- Consequent in conclusion, `... : C(z)`
    exElim f (a ** ba) = f ba

    {- Compare the above with the elimination rule:
             Γ                  ⊢ A type      -- Type A exists.
             Γ,            x∈A ⊢ B(x) prop    -- Dependent type B(x) exist.
             Γ,   z:∃x∈A.B(x) ⊢ C(z) prop     -- Dependent type C(z) exist.
             Γ,   x∈A, y∈B(x) ⊢ c:C(in(x,y))
            ----------------------------------------------------- (∃-Elim)
             Γ, z:∃x∈A.B(x) ⊢ ind^C_(∃x∈A.B(x))(c)(z) : C(z)
    -}

namespace OnEvenOdd

    --  A /\ B -> C
    -- \A x \in A . P(x)

    {-
        Defining a Set Inductively
        • The set of even numbers is the least set such that
        • 0 is even.
        • If n is even, then n+2 is even.
    -}

        data Even : Nat -> Type where
            EvenZero : Even 0
            EvenNext : Even x -> Even (S (S x))

        data Odd : Nat -> Type where
            OddOne : Odd 1
            OddNext : Odd x -> Odd (S (S x))

    {-  Then we build-up lemmas around the introduced definitions.
        Lemmas encapsulate the internal structure and exposes its properties.

        ∀ x ∈ Nat : (even x) ⇒ (odd (x + 1))
    -}
namespace OnLTE

    --
    -- ∀ a, b ∈ Nat : a ≤ b ∨ b ≤ a
    --
    some : (a : Nat) -> (b : Nat) -> Either (LTE a b) (LTE b a)
    some 0 b = Left LTEZero
    some (S k) 0 = Right LTEZero
    some (S k) (S j) = case some k j of
                            (Left x) => Left (LTESucc x)
                            (Right x) => Right (LTESucc x)

    --
    -- ∀ a, b ∈ Nat : a ≥ b /\ a ≤ b ⇒ a = b
    --
    other: (GTE a b) -> (LTE a b) -> a = b
    other LTEZero LTEZero = Refl
    other (LTESucc x) (LTESucc y) = case other x y of
                                      Refl => Refl

namespace OnMax

    {-  Another example of a predicate.
        States that m is max of a and b.
    -}
    data Max : (a : Nat) -> (b : Nat) -> (m : Nat) -> Type where
        MaxA : LTE b a -> Max a b a
        MaxB : LTE a b -> Max a b b

    my_max : Nat -> Nat -> Nat
    my_max a b = if a <= b then a else 0


    decCmp : (a : Nat) -> (b : Nat) -> Either (LTE a b) (LTE b a)
    decCmp 0 0 = Left LTEZero
    decCmp 0 (S k) = Left LTEZero
    decCmp (S k) 0 = Right LTEZero
    decCmp (S k) (S j) =
        case decCmp k j of
            (Left x) => Left (LTESucc x)
            (Right x) => Right (LTESucc x)

    {-  And that's how we can use it.

            ∀ a, b ∈ Nat :
                ∃ m ∈ Nat :
                    m = max a b
    -}
    maxOfNats : (a : Nat) -> (b : Nat) -> (m : Nat ** Max a b m)
    maxOfNats a b =
        case decCmp a b of
            (Left prf) => (b ** MaxB prf)
            (Right prf) => (a ** MaxA prf)

    {-  And to prove additional properties of it.

            -- ∀ a ∈ Nat:
            --     ∀ b∈ Nat:
            --       ∀ m ∈ Nat :
            ∀ a, b, m ∈ Nat :
                (m = max a b) ⇒
                    a ≤ m ∧ b ≤ m ∧ (a = m ∨ b = m)

        If a, b and c are naturals, and m is max of a and b,
        then a <= b, and ...
    -}
    maxOfNatsProps :
        {a : Nat} ->
        {b : Nat} ->
        Max a b m ->
        (LTE a m, LTE b m, Either (a = m) (b = m))
    maxOfNatsProps (MaxA x) = (reflexive, x, Left Refl)
    maxOfNatsProps (MaxB x) = (x, reflexive, Right Refl)

-- Extrinsic: ...
-- Intrinsic: 

data Even : Nat -> Type where
    EvenZero : Even 0
    EvenNext : Even x -> Even (S (S x))

data Odd : Nat -> Type where
    OddOne : Odd 1
    OddNext : Odd x -> Odd (S (S x))

f1 : {a : Type} -> {P : a -> Type} -> ((x : a) -> P x) -> ((y : a) -> P y)
f1 f y = f y

f2 : {P : Nat -> Type} -> ((x : Nat) -> (P x -> P x))
f2 x y = y

f3 : {x : Nat} -> Odd x -> Even (S x)
f3 OddOne = EvenNext EvenZero
f3 (OddNext y) = EvenNext (f3 y)

f4 : {x : Nat} -> Even (S x) -> Odd x
f4 {x = (S 0)} (EvenNext x) = OddOne
f4 {x = (S (S k))} (EvenNext x) = OddNext (f4 x)

f5 : {x : Nat} -> Either (Even x) (Odd x)
f5 {x = 0} = Left EvenZero
f5 {x = (S 0)} = Right OddOne
f5 {x = (S (S k))} = case f5 {x = k} of 
                (Left x) => Left (EvenNext x)
                (Right x) => Right (OddNext x)

f10 : (n : Nat ** (m : Nat) -> LTE n m)
f10 = (0 ** \m => LTEZero)

LTENN : (n : Nat) -> LTE n n
LTENN 0 = LTEZero
LTENN (S k) = LTESucc (LTENN k)

f11 : {n : Nat} -> (m : Nat ** LTE n m)
f11 {n} = (n ** LTENN n)
