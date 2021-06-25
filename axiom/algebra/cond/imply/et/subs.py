from util import *


@apply
def apply(given, old, new):
    assert old.is_given is None
    assert new in given.domain_defined(old)
    return And(given, given._subs(old, new))


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol.a(real=True, shape=(oo,))
    b = Symbol.b(real=True, shape=(oo,))
    n = Symbol.n(integer=True, negative=False)
    Eq << apply(Equal(a[n], b[n]), n, 0)

    Eq << algebra.et.given.conds.apply(Eq[-1])

    Eq << Eq[0].subs(n, 0)


if __name__ == '__main__':
    run()