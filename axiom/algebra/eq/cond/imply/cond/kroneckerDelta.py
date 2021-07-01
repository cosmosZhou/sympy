from util import *


def process_given_conditions(*given, swap=False, delta=True, reverse=False):
    if swap:
        f_eq, eq = given
    else:
        eq, f_eq = given
        
    lhs, rhs = eq.of(Equal)    
    assert f_eq.is_Boolean
    if reverse:
        lhs, rhs = rhs, lhs    
    elif delta:
        lhs, rhs = KroneckerDelta(lhs, rhs), One()
    return eq, f_eq._subs(lhs, rhs)


@apply
def apply(*given, **kwargs): 
    eq, f_eq = process_given_conditions(*given, **kwargs)
    return f_eq


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    Eq << apply(Equal(x, y), Unequal(g(KroneckerDelta(x, y)), f(x, y)))

    Eq << Equal(KroneckerDelta(x, y), 1, plausible=True)

    Eq << Eq[-1].simplify()

    Eq << Eq[1].subs(Eq[-1])

    Eq << Eq[2].reversed


if __name__ == '__main__':
    run()

