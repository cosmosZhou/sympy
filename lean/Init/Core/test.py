from lean import *

PetName = String | String
animals = List[PetName](
    PetName.inl("Spot"), 
    PetName.inr("Tiger"), 
    PetName.inl("Fifi"), 
    PetName.inl("Rex"), 
    PetName.inr("Floof")
)

print(animals)

@Function
def howManyDogs(pets: List[PetName]) -> Nat:
    if pets is List[PetName].nil:
        return 0
    head, pets = pets.args
    n = howManyDogs(pets)
    if isinstance(head, PetName.inl):
        n += 1
    return n

print(howManyDogs(animals))

Integers = Nat | Int
integers = List[Integers](
    Integers.inl(0), 
    Integers.inr(-1), 
    Integers.inl(2), 
    Integers.inl(3), 
    Integers.inr(-4)
)

print(integers)

class ArithExpr(Inductive):
    ann = Type
    int : (ann, Int) = Self  # type: ignore
    plus : (ann, Self, Self) = Self  # type: ignore
    minus : (ann, Self, Self) = Self  # type: ignore
    times : (ann, Self, Self) = Self  # type: ignore

print(ArithExpr)