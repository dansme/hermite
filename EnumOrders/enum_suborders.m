// Functions to enumerate suborders of a given quaternion order,
// possibly picking out a given class of orders.

import "orders_aux.m" : Subalgebras;

import "tree_helpers.m" : AttachSubtree;

function Suborders(O, p, Selector : UpTo := "Isomorphism"
                                  , MaxIndex := 4)
    // Given an order O and a prime ideal p, compute all orders
    // O' such that
    // *) pO ⊆ O' ⊊ O
    // *) [O:O'] <= p^MaxIndex
    // *) Selector(O') is true
    //
    // The parameter UpTo selects if orders should be enumerated up to
    // "Equality", "Isomorphism", or "LocalIsomorphism"
    //
    // The algorithm is naive: First the residue ring O/pO is computed,
    // then all subalgebras of O/pO are lifted to orders and checked

    A:= Algebra(O);

    B:= LocalBasis(O, p : Type := "Submodule");
    pO:= [g*b : b in Generators(O), g in Generators(p)];

    if UpTo eq "Equality" then
        cmpfunc := func< O1, O2, p | false >;
    elif UpTo eq "LocalIsomorphism" then
        cmpfunc := func< O1, O2, p | IsLocallyIsomorphic(O1, O2, p)>;
    else // default is up to global isomorphism
        cmpfunc := func< O1, O2, p | IsConjugate(O1, O2 : FindElement := false)>;
    end if;

    Omodp, h := ResidueRing(O, p);

    L:= [];
    for S in Subalgebras(Omodp : OnlyProper := true, MinDim := Maximum(0, 4 - MaxIndex)) do
        OO := Order([ A!(x @@ h) : x in Basis(S) ] cat pO);
        if Selector(OO) and forall{l : l in L | not cmpfunc(OO, l, p)} then
            Append(~L, OO);
        end if;
    end for;
    return L;
end function;

function CanonicalSuborders(O, p : UpTo := "Isomorphism"
                                 , MaxIndex := 4)
    // Compute proper suborders of O that differ from O at p and have
    // radical idealizer equal to O
    return Suborders(O, p,
                     func< OO | RadicalIdealizer(OO,p) eq O >
                     : UpTo := UpTo, MaxIndex := MaxIndex);
end function;

function HereditaryAtPSuborders(O, p : UpTo := "Isomorphism")
    // Compute proper suborders of O, that only differ
    // from O at p and are hereditary at p
    return Suborders(O, p,
                     func< OO | IsHereditary(OO,p) >
                     : UpTo := UpTo);
end function;

intrinsic EnumerateSubordersAtP(O::AlgAssVOrd, p::RngOrdIdl, max_index::.
                                : UpTo := "LocalIsomorphism"
                                , Selector := func<O | true>
                                , CheckSelf := true) -> GrphDir
    { Enumerate suborders of O at prime p up to index depth.

      Orders will be returned in the form of a graph. Retrieve orders as
      labels of vertices. A directed edge from V1 to V2 means that V2 is the
      radical idealizer of V1 at p.

      UpTo ... "Isomorphism" or "LocalIsomorphism"
      Selector ... Function that returns which orders to enumerate. The
                   property must be such that if an order satisfies it, also
                   all orders containing it satisfy the it.
      CheckSelf ... Whether to check if O itself satisfies Selector(O)
    }

    assert (UpTo eq "Isomorphism") or (UpTo eq "LocalIsomorphism");

    if CheckSelf and not Selector(O) then
        // If O itself does not satisfy the selection criterion,
        // return empty digraph.
        G := Digraph<1|>;
        RemoveVertex(~G,1);
        return G;
    end if;

    G := Digraph<1 | >;
    v := VertexSet(G) . 1;
    AssignLabel(~G, v, O);

    A := Algebra(O);

    // First produce all suborders that are hereditary at p
    if IspMaximal(O,p) and IsUnramified(p, A) and max_index gt 0 then
        level := p*Discriminant(O)/Discriminant(A);
        vprintf Quaternion: "Considering p-hereditary orders at prime of norm %o (index: %o)\n", Norm(p), [ Norm(q[1]) : q in Factorization(level) ];

        l := HereditaryAtPSuborders(O, p : UpTo := UpTo);
        vprintf Quaternion: "  Found %o such orders\n", #l;

        // Add all of those orders satisfying the selection criterion to the
        // graph
        for OO in l do
            if Selector(OO) then
                AddVertex(~G);
                V := VertexSet(G);
                w := V . #V; // last vertex
                AssignLabel(~G, w, OO);
            end if;
        end for;
    end if;

    // open_nodes is a list of orders whose canonical suborders we have not yet
    // looked at
    open_nodes := [];
    V := VertexSet(G);
    for i := 1 to #V by 1 do
        Append(~open_nodes, < Label(V.i), i >);
    end for;

    while #open_nodes gt 0 do
        vprintf Quaternion: "Number of orders left, whose canonical suborders have to be searched: %o\n", #open_nodes;
        OO := open_nodes[1][1];
        idx := open_nodes[1][2];
        Remove(~open_nodes, 1);

        istart := #Vertices(G);

        pindex := Valuation(Discriminant(OO), p) - Valuation(Discriminant(Algebra(OO)), p);

        suborders := CanonicalSuborders(OO, p : UpTo := UpTo
                                              , MaxIndex := max_index - pindex);

        vprintf Quaternion: "Looking at %o suborders at prime of norm %o\n", #suborders, Norm(p);
        for Onew in suborders do
            if Selector(Onew) then
                AddVertex(~G);
                Vnew := VertexSet(G);
                u := Vnew . #Vnew; // get the vertex with maximal index
                v := Vnew . idx; // recreate v, since graph has changed
                AssignLabel(~G, u, Onew);
                AddEdge(~G, u, v);
                Append(~open_nodes, <Onew, #Vnew>);
            end if;
        end for;
    end while;

    return G;
end intrinsic;

intrinsic EnumerateSuborders(O::AlgAssVOrd, primes::[RngOrdIdl], max_index::[.]
                                : Selector := func<OO | true>
                                , MaxIndex := func<OO, p | Infinity()>) -> GrphDir
    { Enumerate suborders of O at given primes up to index depth.
      Orders are enumerated up to isomorphism.

      Orders will be returned in the form of a graph. Retrieve orders as
      labels of vertices. A directed edge from V1 to V2 means that V2 is the
      radical idealizer of V1 at one of the primes.

      primes ... list of primes at which to search
      max_index ... for each prime, a bound n such that all returned orders O'
                    satisfy [O_p:O_p'] < Nm(p)^n

     Selector ... Function that returns which orders to enumerate. The property
                  must be such that if an order satisfies it, also all orders
                  containing it satisfy it.
     MaxIndex ... Similar to max_index, but allows more flexibility by
                  parametrizing on the order and p.
    }
    G := Digraph<1|>;
    if not Selector(O) then
        RemoveVertex(~G, 1);
        return G;
    end if;

    AssignLabel(~G, VertexSet(G).1, O);

    visited_primes := [];

    for p in primes do
        vprintf Quaternion: "Enumerating suborders at prime of norm %o\n", Norm(p);
        V := VertexSet(G);
        new_trees := [];

        for v in V do
            max1 := max_index[Index(primes,p)];
            max2 := MaxIndex(Label(v), p);
            max:= Min(max1,max2);
            H := EnumerateSubordersAtP(Label(v), p, max
                                       : UpTo := "Isomorphism"
                                       , Selector := Selector
                                       , CheckSelf := false);
            Append(~new_trees, <Index(v), H>);
        end for;

        for x in new_trees do
            i := x[1];
            T := x[2];

            // Note: for each newly attached order, this will also
            // compute the radical idealizers at the already visited primes
            // and patch the tree up accordingly.
            AttachSubtree(~G, i, T, visited_primes);
        end for;

        Append(~visited_primes, p);
    end for;
    return G;
end intrinsic;
