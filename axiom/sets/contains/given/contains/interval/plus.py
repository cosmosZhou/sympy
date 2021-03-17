from sympy import *
from axiom.utility import prove, apply
from axiom import sets, algebre


@apply
def apply(imply, c):
    assert imply.is_Contains    
    
    e, interval = imply.args    
    
    return Contains(e + c, interval + c)


@prove
def prove(Eq):
    x = Symbol.x(complex=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    c = Symbol.c(real=True)
    Eq << apply(Contains(x, Interval(a, b)), c=c)

    Eq << sets.contains.imply.le.having.interval.apply(Eq[1])
    
    Eq << sets.contains.imply.ge.having.interval.apply(Eq[1])
    
    Eq << sets.contains.given.et.having.interval.apply(Eq[0])
    
    Eq << algebre.et.given.cond.apply(Eq[-1])
    
    
    
if __name__ == '__main__':
    prove(__file__)

