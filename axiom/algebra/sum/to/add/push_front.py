from util import *


@apply
def apply(self):
    import axiom 
    function, *limits = self.of(Sum)
    i, a, b = axiom.limit_is_Interval(limits)
    front = function._subs(i, a - 1)
#     b >= a => b >= a - 1
    return Equal(self, Sum[i:a - 1:b](function) - front, evaluate=False)


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)
    C = Symbol.C(etype=dtype.integer, given=True)
    
    f = Function.f(real=True)
    h = Function.h(real=True)
    
    Eq << apply(Sum[i:1:n](f(i) + h(i)))

    Eq << Eq[-1].this.rhs.find(Sum).split({0})

    
if __name__ == '__main__':
    run()
