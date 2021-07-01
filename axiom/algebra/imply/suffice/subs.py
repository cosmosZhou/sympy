from util import *



@apply(given=None)
def apply(given, old, new):
    assert old.is_symbol
    assert not old.is_given
    assert new in given.domain_defined(old)
    return Suffice(given, given._subs(old, new))


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, nonnegative=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    t = Function.t(shape=(), real=True)
    x = Symbol.x(real=True)

    Eq << apply(Equal(f[n](x), g[n](x)), x, t(x))

    Eq << Eq[0].this.lhs.apply(algebra.eq.imply.eq.subs, x, t(x))


if __name__ == '__main__':
    run()
