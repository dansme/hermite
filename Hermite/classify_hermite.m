import "bounds.m" : PrimeIdealsUpTo, HermiteMaxIndex, GetPossibleDiscriminants;

intrinsic FindHermiteSuborders(O) -> GrphDir
    { Given a maximal quaternion order O, find all Hermite suborders.

      Results are returned as a digraph, arrows point to radical idealizers.
    }
    A := Algebra(O);
    K := BaseRing(A);
    R := BaseRing(O);

    vprintf Quaternion: "Checking a maximal order and its suborders\n";

    N := #Units(O);

    // A list of primes at which we need to consider non-maximal suborders
    possible_primes := PrimeIdealsUpTo(R, N+2);
    vprintf Quaternion: "  Norms of possible primes: %o\n",
                        [ Norm(p)
                          : p in possible_primes
                          | HermiteMaxIndex(O,p) gt 0 ];

    G := EnumerateSuborders(O, possible_primes
                            , [ Infinity() : p in possible_primes ]
                            : Selector := IsHermite
                            , MaxIndex := HermiteMaxIndex);
    vprintf Quaternion: "  Found %o Hermite orders\n", #VertexSet(G);

    return G;
end intrinsic;

intrinsic FindHermiteOrdersOverField(F::FldNum) -> SeqEnum
    { Find definite Hermite orders in quaternion algebras over F }
    _ := ClassGroup(F); // Makes sure that NarrowClassGroup gives a
                        // guaranteed correct result (without GRH)
    C, f := NarrowClassGroup(F);
    R := MaximalOrder(F);
    parity := #InfinitePlaces(F);

    // Upper bound \prod_{p|D} (Nm(p) - 1), see Proposition 4.0.6
    N := Floor(1/2 * ((2*3.15)^(2*Degree(F)) * #C/ClassNumber(R))
                 / AbsoluteValue(Discriminant(R))^(3/2) + 0.01);
    vprintf Quaternion: "For F=QQ[x]/(%o) bound for prod_{p|D} (Nm(p)-1) is %o\n",
                        DefiningPolynomial(F), N;
    if N lt 1 then
        return [];
    end if;

    // Find all prime ideals of R with norm at most N+1
    possible_primes := PrimeIdealsUpTo(R, N+1);

    vprintf Quaternion: "  Found %o possible prime ideals\n", #possible_primes;

    // Find all possible discriminants that satisfy the bound
    possible_discs := GetPossibleDiscriminants(R, possible_primes, N, parity mod 2);

    vprintf Quaternion: "  Possible N(D) for quaternion algebras over F: %o\n",
                        [ Norm(D) : D in possible_discs ];
    found := [];
    for D in possible_discs do // Iterate over suitable discriminants
        vprintf Quaternion: "    Checking an algebra with N(D)=%o\n", Norm(D);
        A := QuaternionAlgebra(D, InfinitePlaces(F));
        O := MaximalOrder(A);

        for OO in ConjugacyClasses(O) do
            G := FindHermiteSuborders(OO);
            if #VertexSet(G) gt 0 then
                Append(~found, G);
            end if;
        end for;
    end for;
    return found;
end intrinsic;

intrinsic FindHermiteOrdersOverFields(fields::[FldNum]) -> SeqEnum
    { Find definite Hermite orders in quaternion algebras over given fields }
    return &cat[ FindHermiteOrdersOverField(F) : F in fields ];
end intrinsic;

intrinsic FindHermiteOrdersForDegree(degree::RngIntElt
                                   : dbound := 0) -> SeqEnum
    { Find definite Hermite orders in quaternion algebras over fields of given degree }
    if dbound eq 0 then
        // Bound on the discriminant, cf. Proposition 4.0.2
        dbound := Ceiling(2^(2*degree-4/3)*3.15^(4*degree/3));

        if degree eq 9 then
            // Need a refined bound in degree 9 to ensure all the fields
            // are in the list
            dbound := 15143226271;
        end if;
    end if;

    // Number field databases of John Voight
    // https://math.dartmouth.edu/~jvoight/nf-tables/index.html
    nf_names := [ "", "nf/2-30.txt", "nf/3-25.txt", "nf/4-20.txt",
                  "nf/5-17.txt", "nf/6-16.txt", "nf/7-17.txt", "nf/8-17.txt",
                  "nf/9-14.5.txt" ];

    if degree gt 9 then
        return [**];
    elif degree gt 1 then
        fields := GetFieldsFromVoightFile(nf_names[degree]);
    else
        fields := [ RationalsAsNumberField() ];
    end if;

    // Filter fields matching the bound
    fields := [ K : K in fields | Discriminant(K) le dbound ];

    vprintf Quaternion: "Checking %o fields of degree %o; discriminant bound is %o\n", #fields, degree, dbound;

    return FindHermiteOrdersOverFields(fields);
end intrinsic;

intrinsic FindHermiteOrders() -> SeqEnum
    { Find all definite Hermite orders }
    res := [];
    for n := 1 to 9 by 1 do
        res := res cat FindHermiteOrdersForDegree(n);
    end for;
    return res;
end intrinsic;
