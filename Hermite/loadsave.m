// Load/save a list of orders together with extra data related to cancellation
// to a file

import "helpers.m" : ComputeExtraData;

intrinsic GetFieldsFromVoightFile(filename::MonStgElt) -> SeqEnum
    {
    Load a list of fields from one of John Voight's files containing
    tables of totally real fields.
    }
    file := Open(filename, "r");

    QQ<x> := PolynomialRing(Rationals());
    fields := [];

    while true do
        s := Gets(file);
        if IsEof(s) then
            break;
        end if;

        is_match, _, m := Regexp("\\[([0-9]+), \\[([0-9, -]+)\\]\\]", s);
        if is_match then
            a := [ StringToInteger(c) : c in Split(m[2], ",") ];
            d := StringToInteger(m[1]);

            f := QQ ! 0;
            for i in [1..#a] do
                f := f + a[i]*x^(i-1);
            end for;

            K := NumberField(f);
            O := MaximalOrder(K);
            if not(Discriminant(O) eq d) then
                print "Warning: Wrong discriminant for f=", f;
                print "d=",d, " true discriminant = ", Discriminant(O);
            end if;
            if K eq Rationals() then
                K := RationalsAsNumberField();
            end if;
            Append(~fields, K);
        elif not(s eq "") then
            print "Ignoring unexpected line: ", s, " in ", filename;
        end if;
    end while;

    return fields;
end intrinsic;

function SerializeOrder(O)
    A := Algebra(O);
    K := BaseRing(A);

    gens := [ [ ElementToSequence(y) : y in ElementToSequence(x) ] : x in Generators(O) ];

    return < Coefficients(DefiningPolynomial(K))
           , ElementToSequence(K ! (A.1^2))
           , ElementToSequence(K ! (A.2^2))
           , gens >;
end function;

function DeserializeOrder(dat, alg_cache)
    S<X> := PolynomialRing(Rationals());
    f := S ! dat[1];

    K := NumberField(f : Global := true
                       , DoLinearExtension := true);

    a := K ! dat[2];
    b := K ! dat[3];

    index := <f, ElementToSequence(a), ElementToSequence(b)>;

    if IsDefined(alg_cache, index) then
        A := alg_cache[index];
    else
        A := QuaternionAlgebra< K | a, b >;
        alg_cache[index] := A;
    end if;

    gens := [ A ! [K ! x : x in y] : y in dat[4] ];

    return Order(gens), alg_cache;
end function;

intrinsic SaveOrders(file::MonStgElt, orders::[AlgAssVOrd])
    { Save a list of orders to a file.

      Each entry will be a tuple consisting of an order, and additional
      metadata (class groups, ...). If that data has not been computed yet,
      SaveOrders will take some time to run.
    }

    data := [ <SerializeOrder(O), ComputeExtraData(O)> : O in orders ];

    // Format the data for each order on a single line
    lines := [];
    for i := 1 to #data do
        odat := data[i];
        line := "";
        l := Split(Sprint(odat), "\n");
        for j := 1 to #l do
            line cat:= l[j];
            if j lt #l then
                line cat:= " ";
            elif i lt #data then
                line cat:= "\n";
            end if;
        end for;

        Append(~lines,line);
    end for;

    c:= GetColumns();
    SetColumns(0);
    PrintFile(file, lines : Overwrite := true);
    SetColumns(c);
end intrinsic;

intrinsic LoadOrdersPlus(file::MonStgElt) -> SeqEnum
    { Load a list of orders, plus extra data, as saved by SaveOrders }
    data := eval Read(file);
    alg_cache := AssociativeArray();
    l := [];
    for odat in data do
        O, alg_cache := DeserializeOrder(odat[1], alg_cache);
        Append(~l, <O, odat[2]>);
    end for;
    return l;
end intrinsic;

intrinsic LoadOrders(file::MonStgElt) -> SeqEnum
    { Load a list of orders, as saved by SaveOrders. Ignores the extra data. }
    orders_plus := LoadOrdersPlus(file);
    return [ O[1] : O in orders_plus ];
end intrinsic;
