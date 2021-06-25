from util import *


@apply
def apply(given):
    (function, (y, Sy)), (x, Sx) = given.of(All[Any])

    z = Dummy('z', **y.type.dict)
    function = function._subs(y, z)
    function = function._subs(x, y)
    function = function._subs(z, x)
    assert not Sy._has(x)
    
    return All[y:Sx](Any[x:Sy](function))


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(shape=(k,), etype=dtype.integer)
    y = Symbol.y(shape=(k,), etype=dtype.integer)
    
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    
    Sx = Symbol.S_x(etype=dtype.integer.set * k)
    Sy = Symbol.S_y(etype=dtype.integer.set * k)
        
    Eq << apply(All[x:Sx](Any[y:Sy](Equal(f(x), g(y)))))

    Eq << Eq[1].limits_subs(y, Dummy('y', **y.type.dict))


if __name__ == '__main__':
    run()

