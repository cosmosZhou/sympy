from util import *


@apply
def apply(self):    
    function, (i, a, b) = self.of(MatProduct)
    assert i.is_integer
    back = function._subs(i, b - 1)
#     b >= a => b + 1 >= a
    assert a <= b - 1
    return Equal(self, MatMul(MatProduct[i:a:b - 1](function), back), evaluate=False)


@prove(provable=False)
def prove(Eq):
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    f = Function.f(real=True, shape=(m, m))
    Eq << apply(MatProduct[i:0:n + 1](f(i)))

    


if __name__ == '__main__':
    run()