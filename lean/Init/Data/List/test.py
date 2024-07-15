from lean import *


class length(Function):

    α = Type
    def __new__(cls, xs: List[α]) -> Nat:
        if xs:
            _, xs = xs.args
            return Nat.succ(length[cls.α](xs))
        return Nat.zero

print(length(List[Nat](2, 3, 5, 7)))
print(len(List[Nat](2, 3, 5, 7)))
print(not List[Nat](2, 3, 5, 7))

print(not Nat(0))

class drop(Function):

    α = Type
    def __new__(cls, n: Nat, xs: List[α]) -> List[α]:
        if not n or not xs:
            return xs
        n, = n.args
        _, xs = xs.args
        return drop[cls.α](n, xs)

print(drop(2, List[Nat](2, 3, 5, 7)))