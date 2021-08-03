from util import *


@apply
def apply(contains, sgm):
    fi, (i, m) = sgm.of(Sum[Tuple[0]])
    t, s = contains.of(Contains)
    assert s in Range(0, m)    

    return Equal(sgm, Sum[i:Range(0, m) - {t}](fi) + fi._subs(i, t))


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(integer=True, positive=True)
    x = Function.x(real=True)
    m = Symbol.m(integer=True, positive=True)
    y = Function.y(real=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    t = Symbol.t(integer=True, given=True)
    Eq << apply(Contains(t, Range(0, m)), Sum[j:m](y(j)))

    Eq << Eq[1].this.lhs.apply(algebra.sum.to.add.split, cond={t})
    Eq << algebra.cond.imply.eq.piecewise.apply(Eq[0], Eq[-1].lhs)


if __name__ == '__main__':
    run()