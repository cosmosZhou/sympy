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
    x = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)

    m = Symbol(domain=Range(0, n + 1))
    f = Function(shape=(), integer=True)
    s = Symbol(etype=dtype.integer)

    Eq << apply(All[x:0:n + 1](Element(f(x), s)), x, m)

    Eq << algebra.cond.imply.all.apply(Eq[1])


if __name__ == '__main__':
    run()

