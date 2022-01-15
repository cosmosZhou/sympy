from util import *


@apply
def apply(self):
    function, (i, a, b) = self.of(Lamda)
    assert i.is_integer
    back = function._subs(i, b - 1)
#     b >= a => b + 1 >= a
    assert a <= b - 1
    return Equal(self, BlockMatrix(Lamda[i:a:b - 1](function), back), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol(integer=True)
    n, m = Symbol(integer=True, positive=True)
    f = Function(real=True, shape=(m, m))
    Eq << apply(Lamda[i:0:n + 1](f(i)))

    i = Symbol(domain=Range(n + 1))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.to.kroneckerDelta)


if __name__ == '__main__':
    run()
# created on 2019-10-14
