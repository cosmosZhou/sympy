from util import *
import axiom


def simplify_common_terms(given):
    lhs, rhs = given.args
    
    if lhs.is_Add:
        lhs_args = lhs.args
    else:
        lhs_args = [lhs]
    
    if rhs.is_Add:
        rhs_args = rhs.args
    else:
        rhs_args = [rhs]
        
    common_terms = {*lhs_args} & {*rhs_args}
    assert common_terms
    lhs = {*lhs_args} - common_terms
    rhs = {*rhs_args} - common_terms
     
    return given.func(Add(*lhs), Add(*rhs))
    
@apply(given=None)
def apply(given):
    assert given.is_Equal    
    return Equivalent(given, simplify_common_terms(given))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(n,))
    y = Symbol.y(real=True, shape=(n,))
    
    a = Symbol.a(real=True, shape=(n,))
    
    Eq << apply(Equal(x + a, y + a))
    
    Eq << Eq[-1].this.lhs - a
    
        
if __name__ == '__main__':
    run()
