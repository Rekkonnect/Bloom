module Sqrt
{
    function SqrtReal(x: real) : (result: real)
        requires x >= 0.0
        ensures result >= 0.0 && result * result == x

    lemma SqrtRealLemma(x: real, y: real)
        requires x >= 0.0
        requires SqrtReal(x) == y
        ensures y * y == x

    lemma SqrtRealLemma'(x: real, y: real)
        requires x >= 0.0
        requires y * y == x
        ensures SqrtReal(x) == y

    lemma SquareNonNegative(x: real)
        ensures Square(x) >= 0.0

    lemma NonNegativeSquareNonNegative(x: real)
        requires x >= 0.0
        ensures NonNegativeSquare(x) >= 0.0

    function Square(x: real) : real
    {
        x * x
    }

    function NonNegativeSquare(x: real) : real
        requires x >= 0.0
    {
        x * x
    }

    lemma SqrtZero()
        ensures SqrtReal(0.0) == 0.0
    {
        SqrtRealLemma'(0.0, 0.0);
    }

    lemma SqrtOne()
        ensures SqrtReal(1.0) == 1.0
    {
        SqrtRealLemma'(1.0, 1.0);
    }

    lemma SqrtRealLow(x: real)
        requires 0.0 < x < 1.0
        ensures SqrtReal(x) > x
    {
        var y := SqrtReal(x);
        assert y * y == x;
        assert 0.0 < y * y < 1.0;
        SqrtRootBelowOne(x);
        assert 0.0 < y < 1.0;
        SmallerSquareLow(y);
        assert y * y < y;
        assert x < y;
    }

    lemma SqrtRealHigh(x: real)
        requires x > 1.0
        ensures SqrtReal(x) < x
    {
        var y := SqrtReal(x);
        assert y * y == x;
        assert y * y > 1.0;
        SqrtRootOverOne(x);
        assert y > 1.0;
        SmallerSquareHigh(y);
        assert y * y > y;
        assert x > y;
    }

    lemma SmallerSquareLow(x: real)
        requires 0.0 < x < 1.0
        ensures x * x < x

    lemma SmallerSquareHigh(x: real)
        requires x > 1.0
        ensures x * x > x

    lemma SqrtRootBelowOne(x: real)
        requires 0.0 < x < 1.0
        ensures 0.0 < SqrtReal(x) < 1.0

    lemma SqrtRootOverOne(x: real)
        requires x > 1.0
        ensures SqrtReal(x) > 1.0

    function NaturalPower(x: real, n: nat) : real
        decreases n
    {
        if n == 0 then
            1.0
        else if n == 1 then
            x
        else
            x * NaturalPower(x, n - 1)
    }
}
