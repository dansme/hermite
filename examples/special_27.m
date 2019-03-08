AttachSpec("../Hermite.spec");
orders := LoadOrders("../hermite.dat");
filtered := [ O : O in orders | Degree(BaseRing(Algebra(O))) eq 1 and not HasCancellation(O) ];
assert #filtered eq 1;
O := filtered[1];

L := TernaryLatticeOfGorensteinOrder(O);
Ls := InnerProductScaling(L,27);
G := ChangeRing(GramMatrix(Ls), Integers());
Lz := LLL(LatticeWithGram(G));
print "LLL reduced Gram Matrix", GramMatrix(Lz);

C := RightClassSet(O);
G, f := StableClassGroup(O);
print [ Norm(I) @@ f : I in C ];

