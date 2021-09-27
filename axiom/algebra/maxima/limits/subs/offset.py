from util import *


@apply
def apply(self, offset):
    from axiom.algebra.sum.limits.subs.offset import limits_subs
    return Equal(self, limits_subs(Maxima, self, offset), evaluate=False)


@prove(proved=False)
def prove(Eq):
    m, n = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Maxima[n:1:m + 1](f(n)), 1)


if __name__ == '__main__':
    run()