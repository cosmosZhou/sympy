from lean import *


class Point(Structure):
    x = float
    y = float


pt = Point(1.0, y=2.0)
print(pt)

print(pt.x, pt.y)
pt = pt(x=3.0)

print(pt)


class PPoint(Structure):
    α = Type
    β = Type
    x = α
    y = β
    z = Nat

print(PPoint[Nat, float](0, 0, 0))


class replaceX(Function):
    α = Type
    def __new__(cls, point: PPoint[α, float], newX: α) -> PPoint[α, float]:
        return point(x=newX)


print(replaceX(PPoint[Nat, float](0, 0, 0), 1))

@Function
def maximum(n: Nat, k : Nat) -> Nat:
    return k if n < k else n

print("maximum(1, 2) =", maximum(1, 2))


@Function
def even(n : Nat) -> bool:
    match n:
        case Nat.zero:
            return True

        case Nat.succ():
            n, = n.args
            return not even(n)

        
print("even(Nat(3)) =", even(Nat(3)))
