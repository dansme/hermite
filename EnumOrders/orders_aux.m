// Auxiliary (mathematical) functions for quaternion orders:
//  residue rings, radical idealizer,
//  subalgebras of a finite dimensional algebra.

intrinsic ResidueRing(O::AlgAssVOrd, p::RngOrdIdl) -> AlgMat, Map
    { Compute residue ring of O modulo a prime ideal p of the center}

    A := Algebra(O);

    // Get a set of elements that for a R_(p) basis for O_(p)
    B := LocalBasis(O, p : Type := "Submodule");

    k, phi := ResidueClassField(p);

    BMI := Matrix([ Eltseq(A ! x) : x in B ]);
    BM := BMI^-1;
    // BM is the transformation matrix from standard basis of A into basis B
    // (apply to row vectors from the right)

    // Obtain structure coefficients for A, w.r.t. the basis B
    C := [ [ Vector(A!(x*y))*BM : y in B ] : x in B ];

    // Reduce structure coefficients to the residue class field.
    // x lives in the localization R_(p), where R is the center of O,
    // but phi can be applied to such elements.
    C := [ [ [ phi(x) : x in Eltseq(v) ] : v in L] : L in C ];

    A1 := AssociativeAlgebra<k, 4 | C>;
    V := RowSpace(BM);
    h := hom<O -> A1 | x :-> (A1 ! [ phi(v) : v in Eltseq((V ! Vector(A!x)) * BM)]),
                       y :-> O ! A ! Vector(ChangeRing(ChangeRing(y, Inverse(phi)), BaseRing(A))*BMI) >;

    A2, g :=  MatrixAlgebra(A1);
    return A2, h*g;
end intrinsic;

intrinsic RadicalIdealizer(O::AlgAssVOrd, p::RngOrdIdl) -> AlgAssVOrd
    { Compute the radical idealizer of O at the prime ideal p of the center }

    AA, f := ResidueRing(O, p);
    JJ := JacobsonRadical(AA);
    J := rideal<O | [x @@ f : x in Generators(JJ)] cat Generators(p)>;
    RO := RightOrder(J);
    return RO;
end intrinsic;

function Subalgebras(A : OnlyProper := false
                       , MinDim := 0)
    // For a finite dimensional algebra over a finite field
    // (given as AssociativeAlgebra or as MatrixAlgebra), return
    //   a list of all subalgebras

    A0, f := AssociativeAlgebra(A);
    V, h := VectorSpace(A0);
    W, p := quo<V| h(A0!1)>;

    // We can't call Submodule() for VectorSpace
    F := RModule(BaseRing(A0), Dimension(W));
    d := Dimension(F);
    algebras := [];
    for G in Submodules(F : CodimensionLimit := d - MinDim + 1) do
        if OnlyProper and Dimension(G) eq Dimension(W) then
            continue;
        end if;
        b0 := ChangeUniverse(ChangeUniverse(Basis(G), F), W);
        b := [ x @@ p : x in b0 ];
        A1 := sub< A | A!1, [ x @@ h @@ f : x in b ]>;
        // The following check makes sure that the dimension of the algebra
        // spanned by the space U is not actually bigger than the dimension of U
        // itself.
        // Thus, it verifies that the vector spaces U really is a subalgebra
        // already.
        if #b + 1 eq Dimension(A1) then
            Append(~algebras, A1);
        end if;
    end for;
    return algebras;
end function;

intrinsic TernaryLatticeOfGorensteinOrder(O:AlgAssVord) -> LatNF
    { Get the ternary quadratic lattice corresponding to an order }

    require IsGorenstein(O): "O needs to be Gorenstein";

    R := BaseRing(O);
    A := Algebra(O);
    K := BaseRing(A);
    IPM := InnerProductMatrix(NormSpace(A));
    P := PseudoMatrix(O);
    assert CoefficientIdeals(P)[1] eq 1*R; // FIXME: we should actually transform 1 to the correct element in L
    assert Basis(P)[1] eq [ R.1, 0, 0, 0];
    L := NumberFieldLattice(Rows(ChangeRing(Matrix(P),K))
                            : Ideals := CoefficientIdeals(P)
                            , InnerProduct := IPM);
    Ld := Dual(L);
    return OrthogonalComplement(Ld, L.1);
end intrinsic;

intrinsic IsLocallyIsomorphic(O1::AlgAssVOrd, O2::AlgAssVOrd, p::RngOrdIdl) -> Bool
    { Test whether two orders are locally isomorphic at p }
    assert IsIsomorphic(Algebra(O1), Algebra(O2));

    D1 := Discriminant(O1);
    D2 := Discriminant(O2);

    // Quick first check: are discriminants the same at p?
    if not Valuation(D1,p) eq Valuation(D2, p) then
        return false;
    end if;

    OO1, b1 := GorensteinClosure(O1);
    OO2, b2 := GorensteinClosure(O2);

    if not Valuation(b1,p) eq Valuation(b2,p) then
        return false;
    end if;

    L1 := TernaryLatticeOfGorensteinOrder(OO1);
    L2 := TernaryLatticeOfGorensteinOrder(OO2);

    d1 := Determinant(L1);
    d2 := Determinant(L2);

    // First we rescale the Gram matrix of L2 so that
    // the determinants of the lattices lie in the same square class
    // locally at p
    // Then the lattices are similar at p if and only if they are isometric p
    if not Valuation(d1,p) eq Valuation(d2,p) then
        return false;
    end if;

    L2 := InnerProductScaling(L2, d1/d2);
    d2 := Discriminant(L2);

    return IsLocallyIsometric(L1, L2, p);
end intrinsic;

intrinsic IsIsomorphicAsRing(O1::AlgAssVOrd, O2::AlgAssVOrd) -> Bool
    { Check if two quaternion orders are isomorphic as rings
      (We allow non-trivial automorphisms of the base ring)
    }
    if not Norm(Discriminant(O1)) eq Norm(Discriminant(O2)) then
        return false;
    end if;

    A1 := Algebra(O1);
    A2 := Algebra(O2);

    K1 := BaseRing(A1);
    K2 := BaseRing(A2);

    isi, f := IsIsomorphic(K1, K2);

    if not isi then
        return false;
    end if;

    isos := [ f*g : g in Automorphisms(K2) ];

    for h in isos do
        // A3 is isomorphic to A1, but with base field K2
        A3 := QuaternionAlgebra< K2 | h(A1.1^2), h(A1.2^2) >;
        gens := Generators(O1);
        gensInA3 := [ A3 ! [ h(y) : y in Eltseq(x) ] : x in gens ];

        isi, g := IsIsomorphic(A3, A2 : Isomorphism := true);
        if isi then
            O4 := Order([ g(x) : x in gensInA3 ]);
            if IsIsomorphic(O2, O4) then
                return true;
            end if;
        end if;
    end for;

    return false;
end intrinsic;
