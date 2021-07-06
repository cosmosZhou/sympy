from util import *


@apply
def apply(given, old, new):
    from sympy.concrete.limits import limits_dict
    cond, *limits = given.of(All)

    domain_defined = new.domain
    domain = limits_dict(limits)[old]
    assert domain.is_set
    assert domain_defined in domain

    return cond._subs(old, new)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    n = Symbol.n(integer=True, positive=True)

    m = Symbol.m(domain=Range(0, n + 1))
    f = Function.f(shape=(), integer=True)
    s = Symbol.s(etype=dtype.integer)

    Eq << apply(All[x:0:n + 1](Contains(f(x), s)), x, m)

    Eq << algebra.cond.imply.all.apply(Eq[1])


if __name__ == '__main__':
    run()

