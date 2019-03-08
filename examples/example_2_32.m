AttachSpec("../Hermite.spec");
orders := LoadOrders("../hermite.dat");
filtered := [ O : O in orders | Degree(BaseRing(Algebra(O))) eq 1 and Norm(Discriminant(O)) eq 32 and not IsGorenstein(O) ];
assert #filtered eq 1;
O := filtered[1];
OO, bb := GorensteinClosure(O);

_, b := IsPrincipal(bb);
b := Integers() ! b;

L := TernaryLatticeOfGorensteinOrder(OO);
Ls := InnerProductScaling(L, 2);
G := ChangeRing(GramMatrix(Ls), Integers());
Lz := LLL(LatticeWithGram(G));
print GramMatrix(Lz);
