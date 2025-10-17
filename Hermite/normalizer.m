// Functions for the normalizer group

function SquareTotallyPositiveSubgroup(m);
  // takes a map from an abstract abelian group to ideals,
  // return the subgroup which squares to narrowly principal ideals, and the map

  A := Domain(m);
  R := Ring(Codomain(m));
  ClRplus, mClRplus := NarrowClassGroup(R);
  h := function(x); if x eq 1 then return GF(2)!0; else return GF(2)!1; end if; end function;
  Aplus := Kernel(hom<A -> ClRplus | [(m(A.i)^2)@@mClRplus : i in [1..Ngens(A)]]>);
  _, mAplus := sub<A | Aplus>;
  return Aplus, mAplus*m;
end function;

intrinsic NormalizerGroup(O::AlgAssVOrd : Strict := false) -> GrpAb, Map
  {Given an Eichler quaternion order O, compute the normalizer of
   O in B^* modulo F^*O^* as an abelian group, together with a map.
   If Strict, then compute the subgroup with totally positive
   reduced norm.}

  // In the Eichler case, the stable class group is ClR so this is just 
  // the 2-torsion; but I'm writing it in this complicated way in case
  // we want to generalize later 
  // ClGOR, mGOR := StableClassGroup(O);

  assert IsEichler(O);  // Only implemented for Eichler orders for now

  R := BaseRing(O);
  F := NumberField(R);
  Foo := RealPlaces(F);
  _, RamBoo := RamifiedPlaces(Algebra(O));
  ClGOR, mGOR := RayClassGroup(1*R, [Index(Foo,v) : v in RamBoo]);

  ClR, mR := ClassGroup(R);
  ClR2upO, mClR2upO := sub<ClR | [mGOR(x)@@mR : x in ClGOR | 2*x eq Id(ClGOR)]>;
  mClR2upO := mClR2upO*mR;

  ALO, mALO := AtkinLehnerGroup(O : Strict := true);
  assert Codomain(mR) eq Codomain(mALO);  // should be set of ideals of R

  NO, _, _, pi1, pi2 := DirectSum(ClR2upO, ALO);
  mNO := hom<NO -> Codomain(mR) | x :-> mClR2upO(pi1(x))*mALO(pi2(x))>;

  if Strict then
    NO, mNO := SquareTotallyPositiveSubgroup(mNO);
  end if;

  return NO, mNO;
end intrinsic;

intrinsic AtkinLehnerGroup(O::AlgAssVOrd : Strict := true) -> GrpAb, Map
  {Given an Eichler quaternion order O, compute the Atkin-Lehner
   group of O.}

  assert IsEichler(O);  // Only implemented for Eichler orders for now, sorry!

  R := BaseRing(O);
  NN := Discriminant(O);
  NNppefact := [c[1]^c[2] : c in Factorization(NN)];
  ALO := AbelianGroup([2 : i in [1..#NNppefact]]);
  mALO := map<ALO -> Parent(NN) | w :-> &*([1*R] cat [NNppefact[i] : i in [1..#NNppefact] | 
                                              Eltseq(w)[i] ne 0])>;
  if Strict then
    ALO, mALO := SquareTotallyPositiveSubgroup(mALO);
  end if;  

  return ALO, mALO;
end intrinsic;



/*
F<w> := NumberField(Polynomial([16129,0,-256,0,1]));
ZF := Integers(F);
pp := PrimesUpTo(20,F)[3];
B := QuaternionAlgebra(pp, RealPlaces(F)[2..4]);
Omax := MaximalOrder(B);
O := Order(Omax, 2*ZF);
NO, mNO := NormalizerGroup(O);
NO;
NOplus, mNOplus := NormalizerGroup(O : Strict := true);
NOplus;
*/