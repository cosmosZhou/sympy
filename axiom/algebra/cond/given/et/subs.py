from util import *


@apply
def apply(f_eq, old, new, reverse=False, simplify=True, assumptions={}):
    from axiom.algebra.all_eq.cond.imply.all.subs import subs    
    if reverse:
        old, new = new, old
    return subs(f_eq, old, new, simplify=simplify, assumptions=assumptions), Equal(old, new)


@prove
def prove(Eq):
    from axiom import algebra

    m, n = Symbol(integer=True, positive=True)
    a, b, c = Symbol(real=True, shape=(m, n))
    S = Symbol(etype=dtype.real * (m, n))
    Eq << apply(Element(a * b, S), a, 2 * c)

    Eq << algebra.eq.cond.imply.cond.subs.apply(Eq[2].reversed, Eq[1])


if __name__ == '__main__':
    run()
