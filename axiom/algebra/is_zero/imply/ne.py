from util import *


@apply
def apply(given, y):
    x = given.of(Equal[0])
    assert y.is_nonzero
    
    return Unequal(x, y)


@prove
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    
    y = Symbol.y(real=True, zero=False)
    Eq << apply(Equal(a * b, 0), y)
    
    Eq << Eq[1].subs(Eq[0])
    

if __name__ == '__main__':
    run()