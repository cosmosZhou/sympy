from util import *


@apply
def apply(self):    
    ((_x, a), expr), (x,) = self.of(Integral[Mul[Bool[LessEqual]]])
    assert _x == x
    return Equal(self, Integral[x:-oo:a](expr), evaluate=False)


@prove(proved=False)
def prove(Eq):
    x, a = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Integral[x](f(x) * Bool(x <= a)))

    


if __name__ == '__main__':
    run()