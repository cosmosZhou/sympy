from util import *


@apply
def apply(self, offset):
    from axiom.algebra.sum.limits.subs.offset import limits_subs
    return Equal(self, limits_subs(Lamda, self, offset, simplify=False), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    a, b, i, d = Symbol(integer=True)
    f = Function(integer=True)
    Eq << apply(Lamda[i:a:b](f(i)), d)

    i = Symbol(domain=Range(b - a))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    


if __name__ == '__main__':
    run()
# created on 2021-12-29
