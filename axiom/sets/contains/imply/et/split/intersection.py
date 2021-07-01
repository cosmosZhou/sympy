from util import *


@apply
def apply(given, index=-1):
    e, args = given.of(Contains[Intersection])
    first = Intersection(*args[:index])
    second = Intersection(*args[index:])
    return Contains(e, first), Contains(e, second)


@prove
def prove(Eq):
    e = Symbol.e(integer=True, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    Eq << apply(Contains(e, A & B))

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()

