from util import *

@apply
def apply(given, old, new):
    cond, *limits = given.of(All)

    limitsDict = given.limits_dict
    assert old in limitsDict
    assert new in limitsDict[old]

    return given & cond._subs(old, new)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    n = Symbol.n(integer=True, positive=True)
    f = Function.f(shape=(), integer=True)
    s = Symbol.s(etype=dtype.integer)

    A = Symbol.A(etype=dtype.integer)
    x0 = Symbol.x0(domain=A)

    Eq << apply(All[x:A](Contains(f(x), s)), x, x0)

    Eq << algebra.et.given.conds.apply(Eq[1])

    Eq << algebra.all.imply.cond.subs.apply(Eq[0], x, x0)


if __name__ == '__main__':
    run()

