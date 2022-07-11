from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    a, b = domain.of(Interval)
    assert a >= 0
    return Element(sqrt(x), domain.copy(start=sqrt(a), stop=sqrt(b)))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(real=True)
    a, b = Symbol(real=True, nonnegative=True)
    Eq << apply(Element(x, Interval(a, b, right_open=True)))

    Eq << sets.el_interval.given.et.apply(Eq[1])

    Eq << sets.el_interval.imply.et.apply(Eq[0])

    Eq << algebra.ge.imply.ge.sqrt.apply(Eq[-2])

    Eq << algebra.ge.imply.ge.relax.apply(Eq[-2], lower=0)

    Eq << algebra.ge_zero.lt.imply.lt.sqrt.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()

from . import max
# created on 2019-06-28
