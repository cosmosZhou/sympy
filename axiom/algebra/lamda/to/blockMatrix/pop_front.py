from util import *


@apply
def apply(self):    
    function, (i, a, b) = self.of(Lamda)
    assert i.is_integer
    front = function._subs(i, a)
#     b >= a => b + 1 >= a
    assert a + 1 <= b
    return Equal(self, BlockMatrix(front, Lamda[i:a + 1:b](function)), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, discrete

    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, nonnegative=True)
    m = Symbol.m(integer=True, positive=True)
    f = Function.f(real=True, shape=(m, m))
    Eq << apply(Lamda[i:0:n + 1](f(i)))

    Eq << algebra.cond.given.suffice.split.apply(Eq[0], cond=n > 0)

    Eq << Eq[2].this.lhs.apply(algebra.is_nonpositive.imply.is_zero)

    Eq << algebra.suffice.given.suffice.subs.apply(Eq[-1])

    Eq << algebra.suffice.given.all.apply(Eq[1])

    n_ = Symbol.n(integer=True, positive=True)
    Eq << algebra.all.given.cond.subs.apply(Eq[-1], Eq[-1].variable, n_)

    Eq << Eq[-1].this.lhs.apply(discrete.matProduct.to.matmul.pop_back)

    Eq << Eq[-1].this.rhs.args[1].apply(discrete.matProduct.to.matmul.pop_back)


if __name__ == '__main__':
    run()