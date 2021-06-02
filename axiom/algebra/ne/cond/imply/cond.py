from util import *
import axiom

def process_given_conditions(*given, swap=False):
    if swap:
        f_eq, eq = given
    else:
        eq, f_eq = given
        
    lhs, rhs = eq.of(Unequal)    
    assert f_eq.is_Boolean
    
    return eq, f_eq._subs(KroneckerDelta(lhs, rhs), Zero())


@apply
def apply(*given, **kwargs):    
    eq, f_eq = process_given_conditions(*given, **kwargs)
    return f_eq


@prove
def prove(Eq):    
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    f = Function.f(nargs=(2,), shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    Eq << apply(Unequal(x, y), Unequal(g(KroneckerDelta(x, y)), f(x, y)))
    
    Eq << Equal(KroneckerDelta(x, y), 0, plausible=True)
    
    Eq << Eq[-1].simplify()
    
    Eq << Eq[1].subs(Eq[-1])
    
    Eq << Eq[2].reversed
    
    
if __name__ == '__main__':
    run()

