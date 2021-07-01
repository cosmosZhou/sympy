from util import *


@apply
def apply(given, index=-1):
    from axiom.algebra.et.imply.et import split 
    et, *limits = given.of(All)
    first, second = split(et, index)

    return All(first, *limits), All(second, *limits),


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    A = Symbol.A(etype=dtype.real * k)
    y = Symbol.y(real=True, shape=(k,), given=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    b = Symbol.b(shape=(k,), real=True)
    Eq << apply(All[x:A](And(Unequal(x, y), Unequal(f(x), g(y)), Equal(f(x), b))))

    Eq <<= Eq[1] & Eq[2]


if __name__ == '__main__':
    run()

