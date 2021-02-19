from sympy import *
from axiom.utility import prove, apply
from axiom import sets
import axiom
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(self, evaluate=False):
    a, b = axiom.is_integer_Interval(self)
    assert not self.right_open
    return Equality(self, Interval(a, b + 1, left_open=self.left_open, right_open=True, integer=True), evaluate=evaluate)


@prove
def prove(Eq): 
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)    
    
    Eq << apply(Interval(a, b - 2, integer=True))
    
    b = Symbol.b(definition=b-1)
    Eq << b.this.definition
    
    Eq << Eq[-1].reversed + 1
    
    Eq << Eq[0].subs(Eq[-1])


if __name__ == '__main__':
    prove(__file__)

