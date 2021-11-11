from util import *


@apply
def apply(lt, is_positive):
    x, R = is_positive.of(Element)
    assert R in Interval(0, oo, left_open=True)
    lhs, rhs = lt.of(Less)
    return Less(lhs / x, rhs / x)


@prove
def prove(Eq):
    from axiom import sets

    a, b = Symbol(real=True)
    x = Symbol(hyper_real=True)
    Eq << apply(a < b, Element(x, Interval(0, oo, left_open=True)))

    Eq << sets.is_positive.imply.is_positive.div.apply(Eq[1])
    Eq << sets.lt.is_positive.imply.lt.mul.apply(Eq[0], Eq[-1])

    
    


if __name__ == '__main__':
    run()
# created on 2021-10-02
# updated on 2021-10-03