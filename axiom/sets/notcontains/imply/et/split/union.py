from util import *


@apply
def apply(given, index=-1):
    e, args = given.of(NotContains[Union])
    
    first = Union(*args[:index])
    second = Union(*args[index:])
    return NotContains(e, first), NotContains(e, second)


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    Eq << apply(NotContains(x, A | B))

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()

