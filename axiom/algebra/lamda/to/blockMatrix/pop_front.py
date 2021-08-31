from util import *


@apply
def apply(self):
    function, (i, a, b) = self.of(Lamda)
    assert i.is_integer
    front = function._subs(i, a)
#     b >= a => b + 1 >= a
    assert a + 1 <= b
    return Equal(self, BlockMatrix(front, Lamda[i:a + 1:b](function)), evaluate=False)


@prove(proved=False)
def prove(Eq):
    i = Symbol(integer=True)
    n, m = Symbol(integer=True, positive=True)
    f = Function(real=True, shape=(m, m))
    Eq << apply(Lamda[i:0:n + 1](f(i)))


if __name__ == '__main__':
    run()
