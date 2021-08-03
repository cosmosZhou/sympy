from util import *


@apply
def apply(f_eq, *, given=None, simplify=True, invert=False, assumptions={}):
    if invert:
        lhs, rhs = given.invert(), S.false
    else:
        lhs, rhs = given, S.true    
    return f_eq._subs(lhs, rhs, simplify=simplify, assumptions=assumptions)


@prove
def prove(Eq):
    from axiom import algebra

    a, b = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)
    f = Function(integer=True)
    Eq << apply(Equal(Piecewise((f(a), Contains(a, A)), (f(b), True)), 0), given=Contains(a, A))

    Eq <<= Eq[0] & Eq[1]
    Eq << algebra.et.given.et.subs.bool.apply(Eq[-1])


if __name__ == '__main__':
    run()