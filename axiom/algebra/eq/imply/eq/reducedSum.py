from util import *


@apply
def apply(given, *, simplify=True): 
    lhs, rhs = given.of(Equal)
    
    lhs, rhs = ReducedSum(lhs), ReducedSum(rhs)
    if simplify:
        lhs = lhs.simplify()
        rhs = rhs.simplify()
    
    return Equal(lhs, rhs)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(domain=Range(0, n))
    assert i.is_integer
    f = Function.f(shape=(), complex=True)
    g = Function.g(shape=(), complex=True)
    
    Eq << apply(Equal(f(i), g(i)))
    
    Eq << Eq[1].subs(Eq[0])
    
    
if __name__ == '__main__':
    run()

