from util import *

# given: x != y
# x not in {y}


@apply
def apply(inequality_a, inequality_b):
    x, a = inequality_a.of(Unequal)
    _x, b = inequality_b.of(Unequal)

    if x != _x:
        if a == _x:
            x, a = a, x
        elif a == b:
            x, a = a, x
            _x, b = b, _x

    assert x == _x
    return NotElement(x, {a, b})


@prove
def prove(Eq):
    from axiom import sets
    x, a, b = Symbol(integer=True, given=True)
    Eq << apply(Unequal(x, a), Unequal(x, b))

    Eq << sets.ne.imply.notin.apply(Eq[0], simplify=False)
    Eq << sets.ne.imply.notin.apply(Eq[1], simplify=False)

    Eq << sets.notin.notin.imply.notin.union.apply(Eq[-1], Eq[-2], simplify=False)


if __name__ == '__main__':
    run()

