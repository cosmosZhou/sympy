from util import *

# given: x != y
# x not in {y}


@apply
def apply(*given):
    inequality_a, inequality_b = given
    x, a = inequality_a.of(Unequal)
    _x, b = inequality_b.of(Unequal)

    if x != _x:
        if a == _x:
            x, a = a, x
        elif a == b:
            x, a = a, x
            _x, b = b, _x

    assert x == _x
    return NotContains(x, {a, b})


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    Eq << apply(Unequal(x, a), Unequal(x, b))

    Eq << sets.ne.imply.notcontains.apply(Eq[0], simplify=False)
    Eq << sets.ne.imply.notcontains.apply(Eq[1], simplify=False)

    Eq << sets.notcontains.notcontains.imply.notcontains.union.apply(Eq[-1], Eq[-2], simplify=False)


if __name__ == '__main__':
    run()

