from util import *
import axiom



@apply(given=None)
def apply(given):
    p, q = given.of(Necessary)
    return Equivalent(given, p | q.invert(), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(Necessary(x > y, f(x) > g(y)))

    Eq << algebra.equivalent.given.cond.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(algebra.necessary.imply.ou)

    Eq << Eq[-1].this.lhs.apply(algebra.necessary.given.ou)

if __name__ == '__main__':
    run()
