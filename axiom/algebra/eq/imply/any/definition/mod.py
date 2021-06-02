from util import *
import axiom



@apply
def apply(given, q=None):
    mod, r = given.of(Equal)
    n, d = mod.of(Mod)
    if q is None:
        q = Symbol.q(integer=True)

    return Exists[q](Equal(n, q * d + r))


@prove
def prove(Eq):
    from axiom import algebra
#     n = q * d + r
    n = Symbol.n(integer=True, given=True)

    d = Symbol.d(integer=True, given=True)

    r = Symbol.r(integer=True)

    Eq << apply(Equal(n % d, r))

    Eq << Eq[0].this.lhs.apply(algebra.mod.to.add)

    Eq << Eq[-1] + n // d * d

    q = Eq[1].variable

    Eq << algebra.any.given.any.subs.apply(Eq[1], q, n // d)

if __name__ == '__main__':
    run()
