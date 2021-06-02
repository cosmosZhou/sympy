from util import *
import axiom
# given: x != y
# x not in {y}


@apply
def apply(given):
    x, complement = given.of(Contains)
    U, y = complement.of(Complement)
    assert U.is_UniversalSet
    y = y.of(FiniteSet)
    return Unequal(x, y)

@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True, given=True)
    x = Symbol.x(complex=True, shape=(n,), given=True)
    y = Symbol.y(complex=True, shape=(n,), given=True)
    Eq << apply(Contains(x, y.universalSet // {y}))
    
    Eq << Eq[0].simplify()
        

if __name__ == '__main__':
    run()

