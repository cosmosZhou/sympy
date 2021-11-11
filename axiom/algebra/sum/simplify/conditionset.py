from util import *


@apply
def apply(self):
    function, (x, (__x, (_x, (___x, fx)))), *limits = self.of(Sum[Tuple[Cup[FiniteSet, Tuple[Equal]]]])
    assert x == _x == __x == ___x

    function = function._subs(x, fx)
    return Equal(self, self.func(function, *limits))


@prove
def prove(Eq):
    from axiom import algebra
    i, j = Symbol(integer=True)

    C = Symbol(etype=dtype.integer, given=True)

    f = Function(integer=True)
    h = Function(real=True)

    Eq << apply(Sum[j:conditionset(j, Equal(j, f(i))), i:C](h(i, j)))

    Eq << Sum[j:conditionset(j, Equal(j, f(i)))](h(i, j)).this.simplify()

    Eq << Eq[-1].this.rhs.apply(algebra.sum.bool)

    Eq << Eq[-1].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << algebra.eq.imply.eq.sum.apply(Eq[-1], (i, C))



if __name__ == '__main__':
    run()

# created on 2019-09-14
# updated on 2019-09-14
