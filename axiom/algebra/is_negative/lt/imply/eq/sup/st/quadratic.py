from util import *


@apply
def apply(is_negative, lt, fx, x=None, left_open=True, right_open=True):
    from axiom.algebra.le.ge.imply.le.quadratic import quadratic_coefficient
    m, M = lt.of(Less)
    a = is_negative.of(Expr < 0)

    x, _a, b, c = quadratic_coefficient(fx, x=x)
    assert _a == a

    y0 = a * m ** 2 + b * m + c
    y1 = a * M ** 2 + b * M + c
    
    return Equal(Sup[x:Interval(m, M, left_open=left_open, right_open=right_open)](fx), 
                 Piecewise((c - b ** 2 / (4 * a), Element(-b / (2 * a), Interval(m, M))),
                           (Max(y0, y1), True)))


@prove
def prove(Eq):
    m, M, x, a, b, c = Symbol(real=True, given=True)
    Eq << apply(a < 0, m < M, a * x ** 2 + b * x + c, x)

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    

    


if __name__ == '__main__':
    run()