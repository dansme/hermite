import "helpers.m" : TypeOfOrder;

intrinsic PrintOrdersAsText(filename::MonStgElt, orders::[AlgAssVOrd])
    { Print a plain-text list, summarizing some properties of the ordes }
    F := Open(filename, "w");
    for O in orders do
        Cset := #RightClassSet(O);
        G := #StableClassGroup(O);
        if HasCancellation(O) then
            has_cancelation := 1;
        else
            has_cancellation := 0;
        end if;
        type := TypeOfOrder(O);

        A := Algebra(O);
        K := BaseRing(A);
        C:="   ";
        if has_cancellation eq 1 then
            C := "[C]";
        end if;

        fprintf F, "%o n=%o d(K)=%o N(d(A))=%o N(N(R))=%o H=%o h=%o t=%o f=%o\n",
                C, Degree(K), Discriminant(MaximalOrder(K)), Norm(Discriminant(A)),
                Norm(Discriminant(O)/Discriminant(A)), Cset, G, type, DefiningPolynomial(K);
    end for;
end intrinsic;

intrinsic FormatOrderTable(filename::MonStgElt, orders::[AlgAssVOrd])
    { Print a list of orders as LaTeX table, suitable for publication.

      Slow due to it's naive way of deduplicating orders.
    }

    // First get a list of all relevant primes of ZZ.
    // These are the primes appearing in the indices of an order.

    Ms := { Norm(Discriminant(O)) / Norm(Discriminant(Algebra(O))) : O in orders };
    primes := Sort(Setseq(&join{ { x[1] : x in Factorization(Integers() ! M) } : M in Ms }));

    function FormatList(l, sep)
        lstr := [ Sprintf("%o", x) : x in l ];
        s := "";
        for i:=1 to #lstr do
            if i gt 1 then
                s cat:= sep;
            end if;
            s cat:= lstr[i];
        end for;
        return s;
    end function;

    function MyEichlerSymbol(O,p)
        if IsIntegral(Discriminant(O) / p) then
            return Sprintf("%o", EichlerInvariant(O,p));
        else
            return "*";
        end if;
    end function;

    // First, we deduplicate the list using automorphisms of the base field
    // The returned list contains pair, with the first element an order, and
    // the second element the multiplicity with which this order occured in the
    // original list
    orders_mult := DedupOrders(orders);

    // We group together all orders by base field & algebra,
    // then sort based on discriminant of the base field and norm of
    // the discriminant of the algebra
    //
    // Finally, within each algebra, we sort by norm of the
    // discriminant of the order
    lut := [];
    for OO in orders_mult do
        O := OO[1];
        R := BaseRing(O);
        A := Algebra(O);
        F := BaseRing(A);

        Append(~lut, < Degree(F), Discriminant(R), Norm(Discriminant(A)), DefiningPolynomial(F), Eltseq(F!(A.1^2)), Eltseq(F!(A.2^2)) >);
    end for;

    function cmpfunc1(A, B)
        t1 := < A[1], A[2], A[3] >;
        t2 := < B[1], B[2], B[3] >;
        if t1 lt t2 then
            return -1;
        elif t1 eq t2 then
            return 0;
        else
            return 1;
        end if;
    end function;

    Sort(~lut, cmpfunc1);

    // This is now a list of defining polynomials and algebra invariants,
    // sorted by discriminants
    // we are going to sort the orders according to this
    lut := [ < x[4], x[5], x[6]> : x in lut ];

    function cmpfunc2(OO1, OO2)
        O1 := OO1[1];
        O2 := OO2[1];
        A1 := Algebra(O1);
        A2 := Algebra(O2);

        F1 := BaseRing(A1);
        F2 := BaseRing(A2);

        t1 := < DefiningPolynomial(F1), Eltseq(F1!(A1.1^2)), Eltseq(F1!(A1.2^2)) >;
        t2 := < DefiningPolynomial(F2), Eltseq(F2!(A2.1^2)), Eltseq(F2!(A2.2^2)) >;

        i1 := Index(lut, t1);
        i2 := Index(lut, t2);

        if not i1 eq i2 then
            return i1 - i2;
        else
            return Norm(Discriminant(O1)) - Norm(Discriminant(O2));
        end if;
    end function;

    Sort(~orders_mult, cmpfunc2);

    primes_header := FormatList(primes, " & ");

    f := Open(filename, "w");
    fprintf f, "\\begin{longtable}{rrrr|c|c|%o|cccc|c}\n", ("c" ^ #primes);
    fprintf f, "$n$ & $d$ & $D$ & $N$ & & c & %o & $\\#\\Cls(O)$ & $\\#\\StCl(O)$ & $t(O)$ & $\\#\\Cl(R)$ & \\#\\\\\n", primes_header;
    fprintf f, "\\toprule\n";
    fprintf f, "\\endhead\n";

    last_poly := 0;
    last_inv := <[],[]>;
    last_n := 0;

    def := ""; // What to put as default value (e.g. for class number 1)

    for OO in orders_mult do
        O := OO[1];
        R := BaseRing(O);
        A := Algebra(O);
        F := BaseRing(A);

        show_n := false;
        show_d := false;
        show_D := false;

        n := Degree(F);
        if (last_n eq 0) or (not last_n eq n) then
            show_n := true;
            show_d := true;
            show_D := true;
            last_n := n;
        end if;

        poly := DefiningPolynomial(F);
        if (last_poly eq 0) or (not last_poly eq poly) then
            show_d := true;
            show_D := true;
            last_poly := poly;
        end if;

        inv := < Eltseq(F!(A.1^2)), Eltseq(F!(A.2^2)) >;
        if (last_inv eq <[],[]>) or (not last_inv eq inv) then
            show_D := true;
            last_inv := inv;
        end if;

        res_symbols := [];
        local_data := [];
        for p in primes do
            if IsDivisibleBy(Integers()!Norm(Discriminant(O)), p) then
                fact := Factorization(R*p);
                // Sort primes first by norm, then exponent
                function cmp_primes(x,y)
                    if not Norm(x[1]) eq Norm(y[1]) then
                        return Norm(y[1]) - Norm(x[1]);
                    else
                        return y[2] - x[2];
                    end if;
                end function;
                Sort(~fact, cmp_primes);

                pps := [ x[1] : x in fact ];
                l := [];
                for pp in pps do
                    if IsIntegral(Discriminant(O) / pp) then
                        Append(~l, IntegerToString(EichlerInvariant(O,pp)));
                        Append(~res_symbols, EichlerInvariant(O,pp));
                    else
                        Append(~l, "*");
                    end if;
                end for;
                Append(~local_data, FormatList(l, ", "));
            else
                Append(~local_data, "");
            end if;
        end for;

        if IsMaximal(O) then
            type := "maximal";
        elif IsHereditary(O) then
            type := "hereditary";
        elif IsEichler(O) then
            type := "Eichler";
        elif forall{x : x in res_symbols | x eq -1} then
            type := "residually inert";
        elif forall{x : x in res_symbols | not x eq 0 } then
            type := "residually quadratic";
        elif IsBass(O) then
            type := "Bass";
        elif IsGorenstein(O) then
            type := "Gorenstein";
        else
            type := "non-Gorenstein";
        end if;

        if show_d then
            d_str := IntegerToString(Discriminant(R));
        else
            d_str := "";
        end if;

        if show_D then
            D_str := IntegerToString(Norm(Discriminant(A)));
        else
            D_str := "";
        end if;

        if show_n then
            n_str := Degree(F);
        else
            n_str := "";
        end if;

        class_number_str := IntegerToString(#RightClassSet(O));
        if class_number_str eq "1" then
            class_number_str := def;
        end if;

        stable_class_number_str := IntegerToString(#StableClassGroup(O));
        if stable_class_number_str eq "1" then
            stable_class_number_str := def;
        end if;

        R_class_number_str := IntegerToString(ClassNumber(R));
        if R_class_number_str eq "1" then
            R_class_number_str := def;
        end if;

        if HasCancellation(O) then
            has_cancellation := "c";
        else
            has_cancellation := def;
        end if;

        type_number_str := IntegerToString(TypeNumber(O));
        if type_number_str eq "1" then
            type_number_str := def;
        end if;

        if show_n and (not OO eq orders_mult[1]) then
            fprintf f, "\\midrule\n";
        end if;

        // How often would that order appear in the list if we considered
        // orders up to R-algebra automorphisms?
        // This information is computed by the DedupOrders function
        number_of_orders := "";
        if OO[2] gt 1 then
            number_of_orders := IntegerToString(OO[2]);
        end if;

        fprintf f, "%o & %o & %o & %o & %o & %o & %o & %o & %o & %o & %o & %o \\\\\n",
                n_str, d_str, D_str, Norm(Discriminant(O)),
                type, has_cancellation, FormatList(local_data, " & "),
                class_number_str, stable_class_number_str, type_number_str,
                R_class_number_str, number_of_orders;
    end for;
    fprintf f, "\\end{longtable}";
end intrinsic;
