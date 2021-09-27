from util import *


@apply
def apply(is_negative):
    x = is_negative.of(Expr < 0)
    assert x in Interval(-1, 1)
    return Equal(asin(sqrt(1 - x ** 2)) - asin(x), S.Pi / 2)


@prove
def prove(Eq):
    from axiom import algebra, geometry

    x = Symbol(domain=Interval(-1, 1))
    Eq << apply(x < 0)

    Eq << algebra.is_negative.imply.is_nonpositive.apply(Eq[0])
    Eq << geometry.is_nonpositive.imply.eq.add.asin.apply(Eq[-1])

    #https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()