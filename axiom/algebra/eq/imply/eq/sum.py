from util import *
import axiom



@apply
def apply(given, *limits, simplify=True):
    lhs, rhs = given.of(Equal)
    assert limits
    lhs, rhs = Sum(lhs, *limits), Sum(rhs, *limits)
    if simplify:
        lhs = lhs.simplify()
        rhs = rhs.simplify()

    return Equal(lhs, rhs)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(domain=Range(0, n))
    assert i.is_integer
    f = Function.f(shape=(), complex=True)
    g = Function.g(shape=(), complex=True)

    Eq << apply(Equal(f(i), g(i)), (i, 0, n))

    Eq << Eq[0].forall((i,))

    Eq << algebra.all_eq.imply.eq.sum.apply(Eq[-1])


if __name__ == '__main__':
    run()

