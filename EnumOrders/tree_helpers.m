// Helper to handle data structures in enum_suborders.m

procedure AttachSubtree(~G, i, T, visited_primes)
    // Helper function to attach a tree returned by EnumerateSubordersAtP
    // to a vertex of another such tree.
    //
    // This is used by EnumerateSuborders in patching together the
    // recursive results at different primes p.
    if #VertexSet(T) eq 0 then
        return;
    end if;

    // Renumber vertices of T
    n := #VertexSet(G);
    ChangeSupport(~T, {@ x : x in [ n .. #VertexSet(G)+#VertexSet(T)-1 ] @});

    // The root of T is already present in G (as vertex i)
    // Find its children, remove the root, and splice the remainder of the tree into G
    edges := IncidentEdges(VertexSet(T) ! n);
    children := [ (n-1) + Index(InitialVertex(e)) : e in edges ];
    RemoveVertex(~T, VertexSet(T) ! n); // this order is already present in G

    L1 := VertexLabels(G);
    L2 := VertexLabels(T);
    G := G join T;
    assert #(L1 cat L2) eq #VertexSet(G);
    AssignVertexLabels(~G, L1 cat L2); // join does not preserve labels

    // Add the children of i back in
    V := VertexSet(G);
    for j in children do
        AddEdge(~G, V!j, V!i);
    end for;

    // Now we need to patch up to the radical idealizers of the orders we already know
    for j:=n+1 to #V by 1 do
        O := Label(V!j);
        for q in visited_primes do
            RI := RadicalIdealizer(O,q);
            if RI eq O then
                continue;
            end if;

            // now find that idealizer in the graph
            found := false;
            for k:=1 to #V by 1 do
                if IsIsomorphic(RI, Label(V!k)) then
                    AddEdge(~G, V!j, V!k);
                    found := true;
                    break;
                end if;
            end for;

            assert found;
        end for;
    end for;
end procedure;
