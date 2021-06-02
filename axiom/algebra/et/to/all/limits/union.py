from util import *
import axiom


@apply(given=None)
def apply(self):
    from sympy.concrete.limits import limits_union
    limitsArr = []
    fnset = set()
    for forall in self.of(And):
        fn, *_limits = forall.of(ForAll)
        limitsArr.append(_limits)
        fnset.add(fn)
        assert len(fnset) == 1

    limits = limitsArr[0]
    for i in range(1, len(limitsArr)):
        limits = limits_union(limits, limitsArr[i])

    fn, *_ = fnset
    return Equivalent(self, ForAll(fn, *limits))


@prove
def prove(Eq):
    from axiom import algebra
    e = Symbol.e(real=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)

    Eq << apply(And(ForAll[e:g(e) > 0](f(e) > 0), ForAll[e:g(e) < 0](f(e) > 0)))

    Eq << Eq[-1].this.rhs.apply(algebra.all.to.et.dissect, cond=g(e) < 0)


if __name__ == '__main__':
    run()

