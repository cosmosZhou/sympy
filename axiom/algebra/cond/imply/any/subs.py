from util import *
import axiom



@apply
def apply(given, old, new):
    assert not given._has(new)
    assert old.free_symbols
    function = given._subs(old, new)
    assert function._has(new)
    return Exists[new](function)


@prove
def prove(Eq):
    e = Symbol.e(integer=True)
    x = Symbol.x(integer=True)
    f = Function.f(integer=True)
    g = Function.g(integer=True)
    Eq << apply(f(g(e)) > 0, g(e), x)
    
    Eq << ~Eq[-1]
    
    Eq << Eq[-1].simplify()
    
    Eq << Eq[-1].subs(x, g(e))
    
    Eq <<= Eq[-1] & Eq[0]
    
    
    
    
    
    
    
if __name__ == '__main__':
    run()

