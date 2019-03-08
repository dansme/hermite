// Functions for computing the stable class group and related information

declare attributes AlgAssVOrd: StableClassGroup;
declare attributes AlgAssVOrd: RightClassSet;

intrinsic RepLocalNorms(O::AlgAssVOrd, p::RngOrdIdl, prec::RngIntElt) -> SeqEnum
    { Given a quaternion order O and a prime ideal p of the center R of O,
      compute a set of representatives in R for nrd(O_p^\times) / (1 + p^prec R_p)
    }
    R := BaseRing(O);

    Obar, g := ResidueRing(O, p);

    _, G, _ := UnitGroup(Obar);
    unit_gens_mod_p := [ O!(x @@ g) : x in Generators(G) ];

    // We need to consider all units of O/p^prec O
    B := ZBasis(O);
    pg := WeakApproximation([p], [1]); // Element that is a uniformizer in R_p

    extra_units := [];
    for i:=1 to prec-1 by 1 do
        extra_units := extra_units cat [ 1 + pg^i * x : x in B ];
    end for;

    return [ Norm(x) : x in unit_gens_mod_p ] cat [ Norm(y) : y in extra_units ];
end intrinsic;

intrinsic StableClassGroup(O::AlgAssVOrd) -> GrpAb
    { Given a quaternion order O, compute its stable class group Cl_G(O) R.

      Also returns a map from Cl_G(O) R to the ideals of R.
    }

    // Use cached result if it exists
    if assigned O`StableClassGroup then
       G := O`StableClassGroup[1];
       f := O`StableClassGroup[2];
       return G, f;
    end if;

    R := BaseRing(O);
    A := Algebra(O);
    K := BaseRing(A);
    _, arch := RamifiedPlaces(A);

    // Shortcut
    if IsEichler(O) and IsDefinite(A) then
        _ := ClassGroup(R);
        G, f := NarrowClassGroup(R);
        return G, f;
    end if;

    d := Discriminant(O) / Discriminant(A);
    nonmax := [ l[1] : l in Factorization(d) ];

    // We compute the stable class group as a quotient of a suitable
    // ray class group. First set up the modulus in a suitable way, so
    // that squares lift.
    m := ideal<R|1>;
    if not (#nonmax eq 0) then
        m := &*[ p^(Valuation(R!4, p) + 1) : p in nonmax];
    end if;

    archIndices := [ Index(InfinitePlaces(K), plc) : plc in arch ];

    // We first compute the class group (with the default Proof := "Full").
    // This ensures that RayClassGroup afterwards will give a ray class group
    // that is guaranteed to be correct.
    _ := ClassGroup(R);
    G, f := RayClassGroup(m, archIndices);

    gens := [];
    for p in nonmax do
        prec := Valuation(R!4, p) + 1;
        // Compute a set of generators for the local norms (modulo our modulus)
        nsq := RepLocalNorms(O, p, prec);

        for a in nsq do
            if (not #nonmax eq 1) then
                I1 :=  &*[ q^(Valuation(R!4, q) + 1) : q in nonmax | q ne p ];
            else
                I1 := ideal<R|1>;
            end if;
            I2 := p^prec;

            b := CRT(I1, I2, R!1, R!a);  // b = a mod p^{..}, and b = 1 mod m/p^{...}
            // Make sure generator is positive at all places where A is ramified
            c := CRT(I1*I2, archIndices, R!b, [1 : x in archIndices]);
            Append(~gens, ideal<R|c>);

            if #nonmax eq 1 then
                assert (ideal<R|c>@@f) eq (ideal<R|a>@@f);
            end if;
        end for;
    end for;

    C, g := quo<G | [x @@ f : x in gens]>;

    O`StableClassGroup := <C, Inverse(g)*f>;

    return C, Inverse(g) * f;
end intrinsic;

intrinsic RightClassSet(O) -> SeqEnum
    { Compute the right class set of a quaternion order O in a naive way.
      This code is originally by Voight (also appears as commented out code in
      ideals-jv.m). Some small modifications have been made.

      We use this naive version, because it works for any order.
    }

    // Use cached result if it exists
    if assigned O`RightClassSet then
        return O`RightClassSet;
    end if;

    AvoidPrimes := { x[1] : x in Factorization(Discriminant(O)) };
    A := Algebra(O);
    R := BaseRing(O);

    massformula := 1/#UnitGroup(O);
    masses := [massformula];  // record the contribution of each ideal class to the total mass

    masstotal := Mass(O);
    vprintf Quaternion:
        "Starting with the trivial ideal class. \nMass %o out of total mass %o\n", massformula, masstotal;

    ideals := [rideal<O | 1>];
    ZbasisO := ZBasis(O);

    pe := 2;
    while massformula ne masstotal do
        factpe := Factorization(ideal<R|pe>);
        // NB Daniel: only use primes where residue field is minimal, in an attempt to speed up the search
        primes := [ x[1] : x in factpe | not x[1] in AvoidPrimes and Norm(x[1]) eq pe ];

        for pp in primes do
            M2F, phi := pMatrixRing(O, pp);

            // Magma's choice of generators for a matrix algebra, whatev!
            e11 := Inverse(phi)(M2F.1);
            e21 := Inverse(phi)(M2F.2*M2F.1);

            // Ideals mod pp are in 1-1 correspondence with elements
            // of P^1(F_pp) on the first row (with zeros on the second)
            k, mk := ResidueClassField(pp);

            // Reduce mod p otherwise 'rideal' will choke  (Steve added this)
            e11coords, e21coords := Explode(Coordinates( [A!e11,A!e21], ZbasisO ));

            e11 := O! &+[ (e11coords[i] mod pe) * ZbasisO[i] : i in [1..#ZbasisO]];
            e21 := O! &+[ (e21coords[i] mod pe) * ZbasisO[i] : i in [1..#ZbasisO]];
            for museq in [[0,1]] cat [[1,x@@mk] : x in [x : x in k]] do
                mu := O!(museq[1]*e11 + museq[2]*e21);
                I := rideal<O | [mu] cat Generators(pp)>;
                I`Norm := pp;

                found := false;
                for jj := 1 to #ideals do
                    if IsIsomorphic(I, ideals[jj]) then
                        found := true;
                        break jj;
                    end if;
                end for;
                if not found then
                    vprintf Quaternion: "New ideal of norm %o, now found %o ideal classes\n", 
                                        Norm(Norm(I)), #ideals+1;
                    Append(~ideals, I);
                    mass := 1/#UnitGroup(LeftOrder(I));
                    massformula +:= mass;
                    Append(~masses, mass);
                    vprintf Quaternion: "Masstotal now %o out of %o\n", massformula, masstotal;
                    vprintf Quaternion: "Contributions: %o\n", masses;

                end if;
            end for;
        end for;
        pe := NextPrime(pe);
    end while;

    O`RightClassSet := ideals;
    return ideals;
end intrinsic;

intrinsic TypeNumber(O::AlgAssVOrd) -> Int
    { Compute type number for arbitrary order using RightClassSet }

    C := RightClassSet(O);
    orders := [ LeftOrder(OO) : OO in C ];
    noniso := [];

    for OO in orders do
        already_seen := false;
        for Ox in noniso do
            if IsIsomorphic(OO,Ox) then
                already_seen := true;
                break;
            end if;
        end for;

        if not already_seen then
            Append(~noniso, OO);
        end if;
    end for;
    return #noniso;
end intrinsic;

intrinsic StablyFreeMass(O::AlgAssVOrd) -> FldRatElt
    { Compute mass(Cls^1 O) }
    return Mass(O) / #StableClassGroup(O);
end intrinsic;

intrinsic IsHermite(O::AlgAssVOrd) -> Bool
    { Is the quaternion order O a Hermite ring? }
    return StablyFreeMass(O) eq 1/#Units(O);
end intrinsic;

intrinsic HasCancellation(O::AlgAssVOrd) -> Bool
    { Does the quaternion order O have locally free cancellation? }
    return #StableClassGroup(O) eq #RightClassSet(O);
end intrinsic;
