SetSeed(1);
AttachSpec("../Hermite.spec");
QQ := RationalsAsNumberField();
ZZ := Integers(QQ);
B := QuaternionAlgebra< QQ | -1, -1>;
O := MaximalOrder(B);
p := 3*ZZ;

G := EnumerateSubordersAtP(O, p, 6);
SaveOrdersGraphToDot(G, "suborders.gv" : ColorFunc := func< v | ColorClassesAtP(3*ZZ, v) >);
V := VertexSet(G);
O16 := Label(V.16);
print Generators(O16);
