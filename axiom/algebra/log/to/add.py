from util import *


@apply
def apply(self, pivot=None):
    args = self.of(Log[Mul])    
    if pivot is None:    
        adds = []
        for arg in args:
            assert arg >= 0
            adds.append(Log(arg).simplify())
        rhs = Add(*adds)
    else:
        left = log(Mul(*args[:pivot]))
        right = log(Mul(*args[pivot:]))
        rhs = left + right
    
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol.a(real=True, positive=True)
    b = Symbol.b(real=True, positive=True)
    c = Symbol.c(real=True, positive=True)
    d = Symbol.d(real=True, positive=True)
    Eq << apply(Log(a * b * c * d), pivot=2)

    Eq << algebra.eq.given.eq.exp.apply(Eq[0])


if __name__ == '__main__':
    run()