// A few small helper functions that are used in saving/loading/printing orders

function TypeOfOrder(O)
    type := -1;
    if IsMaximal(O) then
        type := 4;
    elif IsHereditary(O) then
        type := 3;
    elif IsEichler(O) then
        type := 2;
    elif IsBass(O) then
        type := 1;
    elif IsGorenstein(O) then
        type := 0;
    end if;

    return type;
end function;

function ComputeExtraData(O)
    C := #RightClassSet(O);
    G := #StableClassGroup(O);
    if C eq G then
        has_cancellation := 1;
    else
        has_cancellation := 0;
    end if;

    return <C, G, has_cancellation, TypeOfOrder(O), TypeNumber(O), #ClassGroup(BaseRing(O))>;
end function;
