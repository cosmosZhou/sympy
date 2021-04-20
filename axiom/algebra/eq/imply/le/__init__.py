from sympy import *
from axiom.utility import prove, apply


@apply
def apply(given):    
    assert given.is_Equal
    return LessEqual(*given.args)


@prove
def prove(Eq):
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(Equal(a, b))
    
    Eq << Eq[1].subs(Eq[0])
    
    
if __name__ == '__main__':
    prove()

from . import st