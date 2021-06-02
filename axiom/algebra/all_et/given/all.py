from util import *
from axiom.algebra.et.imply.conds import split


@apply
def apply(given, index=0): 
    et, *limits = given.of(ForAll)
    first, second = split(et, index)

    return ForAll(first, *limits), ForAll(second, *limits),


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)    
    x = Symbol.x(real=True, shape=(k,), given=True)
    
    A = Symbol.A(etype=dtype.real * k)
    y = Symbol.y(real=True, shape=(k,), given=True)
    
    f = Function.f(real=True)
    g = Function.g(real=True)
    b = Symbol.b(shape=(k,), real=True)
    
    Eq << apply(ForAll[x:A](And(Unequal(x, y), Unequal(f(x), g(y)), Equal(f(x), b))))
    
    Eq <<= Eq[1] & Eq[2]

    
if __name__ == '__main__':
    run()

