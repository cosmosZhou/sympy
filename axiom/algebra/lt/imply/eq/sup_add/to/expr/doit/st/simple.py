from util import *


@apply
def apply(lt, fx, x=None, left_open=True, right_open=True):
    m, M = lt.of(Less)
    p = fx.as_poly(x)
    assert p.degree() == 1
    a = p.nth(1)
    b = p.nth(0)
    y0 = a * m + b
    y1 = a * M + b
    
    return Equal(Sup[x:Interval(m, M, left_open=left_open, right_open=right_open)](fx), Max(y0, y1))


@prove
def prove(Eq):
    from axiom import algebra

    x, m, M, a, b, c = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m < M, a * x + b, x)

    Eq << Eq[-1].this.rhs.apply(algebra.max.to.add)

    Eq << Eq[-1].this.lhs.apply(algebra.sup.to.add)


if __name__ == '__main__':
    run()