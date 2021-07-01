from util import *


@apply
def apply(imply, index=-1):
    x, args = imply.of(Contains[Intersection])
    first = Intersection(*args[:index])
    second = Intersection(*args[index:])
    
    return Contains(x, first), Contains(x, second)


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    Eq << apply(Contains(x, A & B))

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()

