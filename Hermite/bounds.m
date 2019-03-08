// Some helper functions related to the computation on bounds of indices
// and discriminants needed in the classification

function PrimeIdealsUpTo(R, bound)
    lst := [];
    for p in PrimesUpTo(bound) do
        lst cat:= [ P : P in Support(p*R) | Norm(P) le bound ];
    end for;

    // Sort by ascending norm
    Sort(~lst, func<A,B | Norm(A) - Norm(B)>);

    return lst;
end function;

function HermiteMaxIndex(O, p)
    // Input: A quaternion order O and a prime ideal p of the center of O.
    //
    // Output: n such that any Hermite suborder O' that differs from O only at p
    //         must have [O_p:O_p'] \le Nm(p)^n
    //
    // See Lemma 4.0.7
    A := Algebra(O);
    R := BaseRing(O);

    q := Norm(p);

    // Actually, usually O will be p-maximal
    Omax := pMaximalOrder(O,p);
    numUnits := #Units(Omax);

    factor := #UnitSquareClassReps(p);

    m := Valuation(Discriminant(O),p) - Valuation(Discriminant(Omax),p);
    n := m;

    repeat
        n := n+1;
        unitIndices := [ q^n * (1 + 1/q), q^n * (1 - 1/q), q^n * (1 - 1/q^2) ];
        if IsRamified(p, Algebra(O)) then
            unitIndices := [ u / (1 - 1/q) : u in unitIndices ];
        end if;

        idxPossible := false;
        for idx in unitIndices do
            if IsIntegral(idx)
               and IsDivisibleBy(Integers() ! numUnits * factor, Integers() ! idx) then
                idxPossible := true;
            end if;
        end for;

        if idxPossible eq false then
            vprintf Quaternion: "For prime of norm %o maximal possible exponent in index is %o\n", q, n - 1;
            return n - 1;
        end if;
    until false;
end function;

function GetPossibleDiscriminants(O, lst, bound, parity)
    // Given a list of prime ideals (`lst`), sorted by norm in ascending order,
    // determine all possible discriminants of totally definite quaternion
    // algebras with \prod_{p|D} (Nm(p) -1) at most `bound`.
    // `parity` makes sure that only totally definite quaternion algebras are
    // counted.  (pass the  number of archimedean places of the field as `parity`)
    //
    // See Proposition 4.0.6

    discs := [];
    if ((parity mod 2) eq 0) and (bound ge 1)then
        Append(~discs, ideal<O|1>);
    end if;

    for i in [1..#lst] do
        C := AbsoluteValue(Norm(lst[i]) - 1);

        if C gt bound then
            return discs;
        end if;

        subdiscs := $$(O, lst[i+1..#lst], bound/C, (parity+1) mod 2);
        discs cat:= [ lst[i]*x : x in subdiscs];
    end for;

    Sort(~discs, func<a,b | Norm(a) - Norm(b)>);
    return discs;
end function;
