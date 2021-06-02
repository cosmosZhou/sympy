from util import *


@apply(simplify=False)
def apply(limits):
    from sympy.concrete.limits import limits_cond
    return ForAll(limits_cond(limits), *limits)


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True)
    f = Exists[x: Interval(0, n)](Equal(x * 2, 1)) 

    Eq << apply(f.limits)
    
    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()

