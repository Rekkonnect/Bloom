module Sequences
{
    predicate IndexWithinBounds<T>(s: seq<T>, index: nat)
    {
        0 <= index < |s|
    }

    predicate NonEmpty<T>(s: seq<T>)
    {
        |s| > 0
    }

    predicate Singleton<T>(s: seq<T>)
    {
        |s| == 1
    }
    function ExtractSingleton<T>(s: seq<T>) : T
        requires Singleton(s)
    {
        s[0]
    }

    function LengthSlice<T>(s: seq<T>, start: nat, length: nat) : seq<T>
        requires length > 0
        requires IndexWithinBounds(s, start)
        requires IndexWithinBounds(s, start + length - 1)
    {
        s[start..(start + length)]
    }

    function DelimitElement<T(==)>(s: seq<T>, delimiter: T) : (result: seq<seq<T>>)
        ensures forall i | 0 <= i < |result|
            :: NotContainsElement(result[i], delimiter)
    {
        if NotContainsElement(s, delimiter) then
            [s]
        else
            var index := FirstElementIndex(s, delimiter);
            ContainsElementYieldsValidSequenceIndex(s, delimiter, index);
            assert index < |s|;
            SubsequenceBeforeFirstElementNotContainsElementLemma(s, delimiter, index);
            var left := s[..index];
            assert NotContainsElement(left, delimiter);
            var result := [left];
            if (index + 1) >= |s| then
                result
            else
                var remaining := s[(index + 1)..];
                var right := DelimitElement(remaining, delimiter);
                result + right
    }

    function DelimitSeq<T(==)>(s: seq<T>, delimiter: seq<T>) : (result: seq<seq<T>>)
        requires NonEmpty(delimiter)
        ensures forall i | 0 <= i < |result|
            :: NotContainsSubsequence(result[i], delimiter)
    {
        if NotContainsSubsequence(s, delimiter) then
            [s]
        else
            var index := FirstSubsequenceIndex(s, delimiter);
            ContainsSubsequenceYieldsValidSequenceIndex(s, delimiter, index);
            assert index < |s|;
            SubsequenceBeforeFirstSubsequenceNotContainsSubsequenceLemma(s, delimiter, index);
            var left := s[..index];
            assert NotContainsSubsequence(left, delimiter);
            var result := [left];
            if (index + 1) >= |s| then
                result
            else
                var remaining := s[(index + 1)..];
                var right := DelimitSeq(remaining, delimiter);
                result + right
    }

    lemma SingletonSeqEnsuresSingleElementAbsenceLemma<T>(s: seq<T>, subsequence: seq<T>)
        requires Singleton(subsequence)
        requires NotContainsSubsequence(s, subsequence)
        ensures NotContainsElement(s, subsequence[0])
    {
        if |s| == 0
        {
            return;
        }

        var element := ExtractSingleton(subsequence);

        if |s| == 1
        {
            assert s[0] != element;
            return;
        }

        var i := 0;
        assert element == subsequence[0];
        assert |subsequence| == 1;
        assert [s[0]] == s[0..1];
        assert |s| > 1;
        assert NotContainsSubsequence(s, subsequence);
        SubsequencesSubsequentlyNotContainingSubsequenceLemma(s, subsequence);
        assert s[1..|s|] == s[1..];
        SubsequencesSubsequentlyNotContainingSubsequenceLemma(s[1..], subsequence);
        assert NotContainsSubsequence(s[0..1], subsequence);
        assert NotContainsElement(s[0..1], element);
        SingletonSeqEnsuresSingleElementAbsenceLemma(s[1..], subsequence);
        assert NotContainsSubsequence(s[1..], subsequence);
        assert NotContainsElement(s[1..], element);
        assert s[i] != element;
    }

    predicate SubsequenceEquals<T(==)>(s: seq<T>, index: nat, target: seq<T>)
        requires NonEmpty(target)
        requires IndexWithinBounds(s, index)
    {
        var length : nat := |target|;
        var endIndex := index + length - 1;
        if !IndexWithinBounds(s, endIndex) then
            false
        else
            SubsequencesEqual(s, index, target, 0, length)
    }

    predicate SubsequencesEqual<T(==)>(s1: seq<T>, s1Index: nat, s2: seq<T>, s2Index: nat, length: nat)
        requires length > 0
        requires IndexWithinBounds(s1, s1Index)
        requires IndexWithinBounds(s2, s2Index)
        requires IndexWithinBounds(s1, s1Index + length - 1)
        requires IndexWithinBounds(s2, s2Index + length - 1)
    {
        LengthSlice(s1, s1Index, length)
            == LengthSlice(s2, s2Index, length)
    }

    // TODO: Create prime version following the other prime version
    lemma SubsequencesSubsequentlyNotContainingElementLemma<T>(s: seq<T>, element: T)
        requires NotContainsElement(s, element)
        ensures forall i, j :: 0 <= i < j <= |s| ==>
            NotContainsElement(s[i..j], element)
    {
        if |s| < 1
        {
            return;
        }

        if |s| == 1
        {
            return;
        }

        assert |s| > 1;

        var i := 0;
        assert NotContainsElement(s[i..], element);
        while i < |s|
            invariant i < |s| ==>
                forall j | i < j <= |s| ::
                    NotContainsElement(s[i..j], element)
        {
            var j := i + 1;
            SubsequenceContainedLemma(s, i, j);
            assert !ContainsElement(s[i..j], element);
            while j <= |s|
                invariant j <= |s| ==> NotContainsElement(s[i..j], element)
            {
                if (i == 0 && j == |s|)
                {
                    break;
                }

                SubsequenceContainedLemma(s, i, j);
                assert ContainsSubsequence(s, s[i..j]);
                assert !ContainsElement(s[i..j], element);
                assert NotContainsElement(s[i..j], element);
                j := j + 1;
            }
            
            i := i + 1;
        }
    }

    // lemma SubsequencesSubsequentlyNotContainingSubsequenceLemma'<T>(s: seq<T>, subseq: seq<T>, i: nat, j: nat)
    //     requires 0 <= i < j <= |s|
    //     requires NonEmpty(subseq)
    //     requires NotContainsSubsequence(s, subseq)
    //     ensures forall i, j :: 0 <= i < j <= |s| ==>
    //         NotContainsSubsequence(s[i..j], subseq)
    // {
    //     SubsequencesSubsequentlyNotContainingSubsequenceLemma(s, subseq);
    //     SubsequencesSubsequentlyNotContainingSubsequenceLemma(s[i..j], subseq);
    // }

    // TODO: Choose between proving this or the prime version of the lemma
    lemma SubsequencesSubsequentlyNotContainingSubsequenceLemma<T>(s: seq<T>, subseq: seq<T>)
        requires NonEmpty(subseq)
        requires NotContainsSubsequence(s, subseq)
        ensures forall i, j :: 0 <= i < j <= |s| ==>
            NotContainsSubsequence(s[i..j], subseq)
    {
        if |s| < |subseq|
        {
            return;
        }

        if |s| == |subseq|
        {
            return;
        }

        assert |s| > |subseq| > 0;

        var i := -1;
        // forall j | i < j <= |s|
        // {
        //     SubsequenceContainedLemma(s, i, j);
        // }
        
        // assert forall j | i < j <= |s| ::
        //     ContainsSubsequence(s, s[i..j]);

        // assert forall j | i < j <= |s| ::
        //     !ContainsSubsequence(s[i..j], subseq);
        // assert forall j | i < j <= |s| ::
        //     NotContainsSubsequence(s[i..j], subseq);
        while i < |s|
            invariant 0 <= i < |s| ==>
                forall j | i < j <= |s| ::
                    NotContainsSubsequence(s[i..j], subseq)
        {
            i := i + 1;

            if i >= |s|
            {
                break;
            }

            var j := i + 1;
            SubsequenceContainedLemma(s, i, j);
            assert !ContainsSubsequence(s[i..j], subseq);
            while j <= |s|
                invariant j <= |s| ==> NotContainsSubsequence(s[i..j], subseq)
            {
                SubsequenceContainedLemma(s, i, j);
                assert ContainsSubsequence(s, s[i..j]);
                assert !ContainsSubsequence(s[i..j], subseq);
                assert NotContainsSubsequence(s[i..j], subseq);
                j := j + 1;
            }
        }
    }

    lemma SubsequenceLeft<T>(s: seq<T>, left: nat)
        requires 0 <= left < |s|
        ensures s[left..] == s[left..|s|]
    {}

    lemma SubsequenceRight<T>(s: seq<T>, right: nat)
        requires 0 < right <= |s|
        ensures s[..right] == s[0..right]
    {}

    lemma NotContainsSubsequenceTrueResults<T>(s: seq<T>, subseq: seq<T>)
        requires NonEmpty(subseq)
        requires NotContainsSubsequence(s, subseq)
        ensures s != subseq
    
    lemma NotContainsSubsequenceFalseResults<T>(s: seq<T>, subseq: seq<T>)
        requires NonEmpty(subseq)
        requires !NotContainsSubsequence(s, subseq)
        ensures |s| >= |subseq|

    lemma NotContainsSubsequenceEqualSizeFalseResult<T>(s: seq<T>, subseq: seq<T>)
        requires NonEmpty(subseq)
        requires |s| == |subseq|
        requires !NotContainsSubsequence(s, subseq)
        ensures s == subseq

    lemma ContainsSubsequenceLemma<T>(s: seq<T>, subseq: seq<T>)
        requires NonEmpty(subseq)
        requires !NotContainsSubsequence(s, subseq)
        ensures
            exists i | 0 <= i <= |s| - |subseq|
                :: s[i..(i + |subseq|)] == subseq
    {
        if !exists i | 0 <= i <= |s| - |subseq|
                :: s[i..(i + |subseq|)] == subseq
        {
            assert NotContainsSubsequence(s, subseq);
        }
    }

    lemma ContainsSubsequenceLemmaSpecific<T>(s: seq<T>, subseq: seq<T>, i: int)
        requires NonEmpty(subseq)
        requires 0 <= i < |s| - |subseq|
        requires !NotContainsSubsequence(s, subseq)
        decreases |s| - i
    {
    }

    lemma NotContainsSubsequenceLemma<T>(s: seq<T>, subseq: seq<T>)
        requires NonEmpty(subseq)
        requires NotContainsSubsequence(s, subseq)
        ensures
            forall i, j | 0 <= i < j <= |s|
                && 0 < |s[i..j]| < |s|
                    :: NotContainsSubsequence(s[i..j], subseq)
    {
        forall i, j | 0 <= i < j <= |s|
            && 0 < |s[i..j]| < |s|
        {
            NotContainsSubsequenceLemmaSpecific(s, subseq, i, j);
        }
    }

    lemma NotContainsSubsequenceLemmaSpecific<T>(s: seq<T>, subseq: seq<T>, i: int, j: int)
        requires NonEmpty(subseq)
        requires 0 <= i < j <= |s|
        requires NotContainsSubsequence(s, subseq) 
        ensures NotContainsSubsequence(s[i..j], subseq)
        decreases j - i
    {
        var slice := s[i..j];
        if |slice| == |s|
        {
            assert slice == s;
            assert NotContainsSubsequence(s, subseq);
            assert NotContainsSubsequence(slice, subseq);
        }
        else
        {
            if |slice| < |subseq|
            {
                assert NotContainsSubsequence(slice, subseq);
            }
            else if |slice| == |subseq|
            {
                if slice == subseq
                {
                    assert !NotContainsSubsequence(slice, subseq);
                    NotContainsSubsequenceLemmaSpecific(s, subseq, i, j);
                    assert !NotContainsSubsequence(s, subseq);
                }
                assert slice != subseq;
            }
        }

        assert NotContainsSubsequence(slice, subseq);
    }

    predicate ContainsSubsequence<T(==)>(s: seq<T>, subseq: seq<T>)
        requires NonEmpty(subseq)
        decreases |s|
    {
        !NotContainsSubsequence(s, subseq)
    }

    predicate NotContainsSubsequence<T(==)>(s: seq<T>, subseq: seq<T>)
        requires NonEmpty(subseq)
        decreases |s|
    {
        if |s| == 0 then
            true

        else if |s| < |subseq| then
            true

        else if |s| == |subseq| then
            s != subseq

        else
            var left := s[1..];
            var right := s[..(|s| - 1)];

            var notContainsLeft := NotContainsSubsequence(left, subseq);
            var notContainsRight := NotContainsSubsequence(right, subseq);
            
            var result := notContainsLeft && notContainsRight;

            result
    }

    lemma SubsequenceIdentities<T>(s: seq<T>, i: nat, j: nat)
        requires i < j
        requires IndexWithinBounds(s, i)
        requires IndexWithinBounds(s, j - 1)
        ensures s[i..j] == s[i..][..(j - i)]
    {

    }

    lemma SubsequenceContainedLemma<T>(s: seq<T>, start: nat, end: nat)
        requires NonEmpty(s)
        requires start < end
        requires IndexWithinBounds(s, start)
        requires end > 0 && IndexWithinBounds(s, end - 1)
        ensures ContainsSubsequence(s, s[start..end])
    {
        var subseq := s[start..end];
        assert SubsequenceEquals(s, start, subseq);
    }

    predicate NotContainsElement<T(==)>(s: seq<T>, c: T)
    {
        forall i | 0 <= i < |s| ::
            s[i] != c
    }
    predicate ContainsElement<T(==)>(s: seq<T>, c: T)
    {
        !NotContainsElement(s, c)
    }

    lemma SubsequenceBeforeFirstSubsequenceNotContainsSubsequenceLemma<T>(s: seq<T>, c: seq<T>, i: nat)
        requires ContainsSubsequence(s, c)
        requires FirstSubsequenceIndex(s, c) == i
        requires i < |s|
        ensures NotContainsSubsequence(s[..i], c)
    {
        if i == 0
        {
            return;
        }

        var subsequenceUntilFirst := s[..(i + 1)];
        var si := FirstSubsequenceIndex(subsequenceUntilFirst, c);
        assert si == i;

        var left := s[..i];
        var leftIndex := FirstSubsequenceIndex(left, c);
        if leftIndex < i
        {
            assert FirstSubsequenceIndex(s, c) > leftIndex;
        }
        assert NotContainsSubsequence(left, c);
    }

    lemma SubsequenceBeforeFirstElementNotContainsElementLemma<T>(s: seq<T>, c: T, i: nat)
        requires ContainsElement(s, c)
        requires FirstElementIndex(s, c) == i
        requires i < |s|
        ensures NotContainsElement(s[..i], c)
    {
        if i == 0
        {
            return;
        }

        var subsequenceUntilFirst := s[..(i + 1)];
        var si := FirstElementIndex(subsequenceUntilFirst, c);
        assert si == i;

        var left := s[..i];
        var leftIndex := FirstElementIndex(left, c);
        if leftIndex < i
        {
            assert FirstElementIndex(s, c) > leftIndex;
        }
        assert NotContainsElement(left, c);
    }

    lemma ContainsSubsequenceYieldsValidSequenceIndex<T>(s: seq<T>, c: seq<T>, i: nat)
        requires NonEmpty(c)
        requires ContainsSubsequence(s, c)
        requires FirstSubsequenceIndex(s, c) == i
        ensures i < |s|
    {
        if i == |s|
        {
            var x :| 0 <= x < |s| - |c| && s[x..(x + |c|)] == c;
            assert FirstSubsequenceIndex(s, c) <= x;
            assert NotContainsSubsequence(s, c);
        }
    }

    lemma ContainsElementYieldsValidSequenceIndex<T>(s: seq<T>, c: T, i: nat)
        requires ContainsElement(s, c)
        requires FirstElementIndex(s, c) == i
        ensures i < |s|
    {
        if i == |s|
        {
            var x :| 0 <= x < |s| && s[x] == c;
            assert FirstElementIndex(s, c) <= x;
            assert NotContainsElement(s, c);
        }
    }

    lemma ContainsElementYieldsValidSequenceIndex'<T>(s: seq<T>, c: T)
        requires ContainsElement(s, c)
        ensures FirstElementIndex(s, c) < |s|
    {
        var x :| 0 <= x < |s| && s[x] == c;
        ElementOccurrenceIndexEqualToFirstElementIndexOrGreater(s, c, x);
        assert FirstElementIndex(s, c) <= x;
    }

    lemma NotContainsElementYieldsInvalidSequenceIndex<T>(s: seq<T>, c: T)
        requires NotContainsElement(s, c)
        requires |s| > 0
        ensures FirstElementIndex(s, c) == |s|
    {
        assert !exists x | 0 <= x < |s| :: s[x] == c;
        var first := FirstElementIndex(s, c);
        if first < |s|
        {
            assert s[first] != c;
        }
        assert first == |s|;
    }

    lemma InvalidFirstOccurrenceIndexDenotesNotContaining<T>(s: seq<T>, c: T)
        requires |s| > 0
        requires FirstElementIndex(s, c) == |s|
        ensures NotContainsElement(s, c)
    {
        if ContainsElement(s, c)
        {
            // We must somehow prove something here
            var i :| 0 <= i < |s| && s[i] == c;
            var first := FirstElementIndex(s, c);
        }
    }

    lemma ElementOccurrenceIndexEqualToFirstElementIndexOrGreater<T>(s: seq<T>, c: T, i: nat)
        requires ContainsElement(s, c)
        requires IndexWithinBounds(s, i)
        requires s[i] == c
        ensures FirstElementIndex(s, c) <= i
    {
        var first := FirstElementIndex(s, c);
        if first == |s|
        {
            NotContainsElementYieldsInvalidSequenceIndex(s, c);
            assert NotContainsElement(s, c);
        }
        if first == i
        {
            assert true;
        }
        else if first > i
        {
            var leftBeforeFirst := s[..i];
            SubsequenceBeforeFirstElementNotContainsElementLemma(s, c, first);
            assert false;
        }
    }

    function FirstSubsequenceIndex<T(==)>(s: seq<T>, subseq: seq<T>) : (result: nat)
        requires |s| > 0
        requires |subseq| > 0
        ensures result <= |s|
    {
        SubsequenceIndexHelper(s, subseq, 0)
    }
    function SubsequenceIndexHelper<T(==)>(s: seq<T>, subseq: seq<T>, i: nat) : (result: nat)
        requires |subseq| > 0
        requires i < |s|
        ensures result <= |s|
        decreases |s| - i
    {
        if i >= |s| - |subseq| then
            |s|
        else if s[i..(i + |subseq|)] == subseq then
            i
        else if (i + 1) < |s| - |subseq| then
            SubsequenceIndexHelper(s, subseq, i + 1)
        else
            |s|
    }

    function FirstElementIndex<T(==)>(s: seq<T>, c: T) : (result: nat)
        requires |s| > 0
        ensures result <= |s|
    {
        ElementIndexHelper(s, c, 0)
    }
    function ElementIndexHelper<T(==)>(s: seq<T>, c: T, i: nat) : (result: nat)
        requires i < |s|
        ensures result <= |s|
        decreases |s| - i
    {
        // We do not have to, and it would be better not to
        // prove that i + 1 will never go out of bounds
        // since we may have this function called on an index
        // beyond the last occurrence of the element
        // Instead of proving that this function cannot be called on such scenarios,
        // it is best to prove that the invocation never returns |s|
        if s[i] == c then
            i
        else if (i + 1) < |s| then
            ElementIndexHelper(s, c, i + 1)
        else
            |s|
    }
}
