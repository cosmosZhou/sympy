from util import *


@apply
def apply(fx, interval, x=None):    
    assert fx._subs(x, -x) == fx    
    return Equal(Inf[x:-interval](fx), Inf[x:interval](fx))


@prove
def prove(Eq):
    from axiom import algebra

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(x ** 2, Interval(m, M, right_open=True), x)

    f = Function(real=True, eval=lambda x : x ** 2)
    Eq << Equal(f(x), f(-x), plausible=True)

    Eq << Eq[-1].this.lhs.defun()

    Eq << Eq[-1].this.rhs.defun()

    Eq << algebra.eq.imply.eq.inf.st.even_function.apply(Eq[-2], Eq[0].find(Interval), x)

    Eq << Eq[-1].this.find(f).defun()

    Eq << Eq[-1].this.find(f).defun().reversed


if __name__ == '__main__':
    run()