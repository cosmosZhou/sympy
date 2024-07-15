from lean import *


class Sign(Inductive):
    pos = Self
    neg = Self


@Function
def posOrNegThree(s: Sign) -> lambda s: Nat if s is Sign.pos else Int:
    match s:
        case Sign.pos:
            return Nat(3)
        case Sign.neg:
            return Int(-3)


print(Sign.pos)
print(Sign.neg)

print(posOrNegThree(Sign.neg))