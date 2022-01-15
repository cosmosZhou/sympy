from util import *


@apply
def apply(given, index=-1):
    (p, q), r = given.of(Infer >> Boolean)
    return Infer(p.invert(), r), Infer(q, r)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, a, b = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(Infer((x > b) >> (x < a), f(x) > g(y)))

    Eq << Eq[0].this.lhs.apply(algebra.infer.imply.ou)
    Eq << algebra.infer.given.et.infer.split.ou.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-06-23
