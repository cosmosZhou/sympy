from util import *
import axiom



@apply
def apply(given):
    assert given.is_NotContains    
    
    e, S = given.args
    args = S.of(Union)
    
    eqs = [NotContains(e, s) for s in args]
    
    return And(*eqs)


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)

    Eq << apply(NotContains(x, A | B))
    
    Eq << Eq[-1].simplify()
    
if __name__ == '__main__':
    run()

