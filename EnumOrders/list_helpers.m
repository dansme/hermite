// This file contains functions to help dealing with graphs or lists of
// quaternion orders

intrinsic OrdersAsList(res::[GrphDir]) -> SeqEnum
    { Convert a list of graphs of orders into a flat list of orders.

      Also deduplicate this list by throwing out isomorphic orders.
      Only orders within algebras that are equal are compared.
    }
    orders := [];
    for G in res do
        new_orders := VertexLabels(G);
        for O in new_orders do
            // Check that we haven't seen this order yet in a totally naive way
            seen := false;
            for OO in orders do
                A1 := Algebra(OO);
                A2 := Algebra(O);
                F1 := BaseRing(A1);
                F2 := BaseRing(A2);
                if IsIsomorphic(F1,F2) and F1 eq F2
                   and IsIsomorphic(A1,A2) and A1 eq A2
                   and IsIsomorphic(OO, O) then
                    seen := true;
                end if;
            end for;

            if not seen then
                Append(~orders, O);
            end if;
        end for;
    end for;
    return orders;
end intrinsic;

intrinsic DedupOrders(orders::[AlgAssVOrd]) -> SeqEnum
    { Deduplicate a list of orders by isomorphism as rings (not as R-algebras!)

      The result is a list of tuples. The first entry in each tuple is an order,
      the second a count describing how often the order appeared in the original
      list.
    }
    new_orders := [];

    for O in orders do
        // Check that we haven't seen this order yet in a totally naive way
        seen := false;
        for i:=1 to #new_orders by 1 do
            OO := new_orders[i][1];
            if IsIsomorphicAsRing(O, OO) then
                seen := true;
                // update count
                new_orders[i][2] +:= 1;
                break;
            end if;
        end for;

        if not seen then
            // Store the order together with a count
            Append(~new_orders, <O, 1>);
        end if;
    end for;
    return new_orders;
end intrinsic;

intrinsic CompareOrderLists(orders1::[AlgAssVOrd]
                           , orders2::[AlgAssVOrd]) -> Bool, SeqEnum, SeqEnum
    { Compare two lists of orders. Very inefficient. }

    leftover1 := [];
    for O in orders1 do
        found := false;
        for i:=1 to #orders2 by 1 do
            if IsIsomorphicAsRing(O, orders2[i]) then
                Remove(~orders2, i);
                found := true;
                break;
            end if;
        end for;

        if not found then
            Append(~leftover1, O);
        end if;
    end for;

    is_same := #leftover1 eq 0 and #orders2 eq 0;
    return is_same, leftover1, orders2;
end intrinsic;

function DefaultGroupFunc(v)
    // For organizing orders according to their discriminant when visually
    // representing their graph
    f := Factorization(Discriminant(Label(v)));
    if #f eq 0 then
        return 0;
    else
        return &+[ x[2] : x in f ];
    end if;
end function;

intrinsic ColorClassesAtP(p::RngOrdIdl, v::GrphVert) -> MonStgElt
    { Give a nice default coloring based on Maximal, Eichler, Bass, ...
    }

    O := Label(v);
    if IspMaximal(O, p) then
        return "red";
    elif IsHereditary(O, p) then
        return "darkorange";
    elif IsEichler(O, p) then
        return "green";
    elif EichlerInvariant(O,p) eq -1 then
        return "blue";
    elif IsBass(O,p) then
        return "cyan3";
    elif IsGorenstein(O,p) then
        return "deeppink";
    else
        return "black";
    end if;
end intrinsic;

intrinsic SaveOrdersGraphToDot(G::GrphDir, filename::MonStgElt
                               : ColorFunc := func<v | "black">
                               , GroupFunc := DefaultGroupFunc)
    { Save a graph of orders to a graphviz dot file for visual representation }

    f := Open(filename, "w");
    Write(f, "digraph G\n");
    Write(f, "{\n");

    Gs := StandardGraph(G);

    Write(f, "  edge[arrowhead=\"none\", penwidth=0.2];\n");
    Write(f, "  rankdir=BT;\n");
    Write(f, "\n");

    for v in Vertices(Gs) do
        Write(f, Sprintf("  O%o [color=%o];\n", v, ColorFunc(v)));
    end for;

    Write(f, "\n");
    for e in Edges(Gs) do
        O1 := Label(InitialVertex(e));
        O2 := Label(TerminalVertex(e));
        index := Norm(Discriminant(O1)/Discriminant(O2));
        Write(f, Sprintf("  O%o -> O%o [label=%o];\n", InitialVertex(e), TerminalVertex(e), index));
    end for;

    // Group by discriminant (or whatever group function we've been passsed)
    grpvalues := { GroupFunc(v) : v in Vertices(Gs) };

    // Add some invisible nodes to ensure that vertices are really grouped GroupFunc
    // (otherwise orders with different value according to group function might be
    // drawn side-by-side)
    minval := Minimum(grpvalues);
    maxval := Maximum(grpvalues);

    for i := minval to maxval by 1 do
        Write(f, Sprintf("  dummy%o [style=invis];\n", i));
    end for;
    for i := minval+1 to maxval by 1 do
        Write(f, Sprintf("  dummy%o -> dummy%o [style=invis];\n", i, i-1));
    end for;

    for grp in grpvalues do
        Write(f, Sprintf("  { rank=same; dummy%o ", grp));

        for v in Vertices(Gs) do
            if GroupFunc(v) eq grp then
                Write(f, Sprintf("O%o ", v));
            end if;
        end for;
        Write(f, "}\n");
    end for;

    Write(f, "}\n");
end intrinsic;
