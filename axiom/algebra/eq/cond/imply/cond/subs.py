from util import *


@apply
def apply(eq, f_eq, *, reverse=False, simplify=True, assumptions={}):
    from axiom.algebra.all_eq.cond.imply.all.subs import subs
    if not eq.is_Equal:
        eq, f_eq = f_eq, eq
    lhs, rhs = eq.of(Equal)
    if reverse:
        lhs, rhs = rhs, lhs
    return subs(f_eq, lhs, rhs, simplify=simplify, assumptions=assumptions)


@prove
def prove(Eq):
    m = Symbol(integer=True, positive=True)
    n = Symbol(integer=True, positive=True)
    a = Symbol(real=True, shape=(m, n))
    b = Symbol(real=True, shape=(m, n))
    c = Symbol(real=True, shape=(m, n))
    S = Symbol(etype=dtype.real * (m, n))
    Eq << apply(Equal(a, 2 * c), Contains(a * b, S))

    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()
