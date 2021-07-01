from util import *


@apply
def apply(given):
    (_x, B), (x, A) = given.of(Any[Contains])
    assert x == _x
    return Any[x:B](Contains(x, A))


@prove
def prove(Eq):
    
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)
    e = Symbol.e(real=True)

    Eq << apply(Any[e:A](Contains(e, B)))
    
    Eq << Eq[-1].simplify()
    
    Eq << Eq[0].simplify()


if __name__ == '__main__':
    run()

