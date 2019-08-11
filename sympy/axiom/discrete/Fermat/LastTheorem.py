from sympy.core.symbol import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.utility import Ref, Sum, cout, Eq, plausible
from sympy.core.relational import Unequality
from sympy.logic.boolalg import plausibles_dict


def apply():
    n = Symbol('n', integer=True, domain=Interval(3, oo, integer=True))
    x = Symbol('x', integer=True, nonnegative=True)
    y = Symbol('y', integer=True, nonnegative=True)
    z = Symbol('z', integer=True, nonnegative=True)
    return Unequality(x ** n + y ** n, z ** n,
                    plausible=plausible(),
                    forall=(n, x, y, z))


from sympy.utility import check
@check
def prove():
    cout << apply()
    n, x, y, z = Eq[-1].forall


if __name__ == '__main__':
    prove()
    print('plausibles_dict:')
    for index, eq in plausibles_dict(Eq).items():
        print("Eq[%d] : %s" % (index, eq))
