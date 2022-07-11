from util import *


@apply
def apply(given, index=-1):
    e, domain = given.of(Element)
    s = domain.of(Intersection)
    if index is not None:
        first = s[:index]
        second = s[index:]
        return Element(e, Intersection(*first)), Element(e, Intersection(*second))
    else:
        return tuple(Element(e, s) for s in s)



@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Element(x, A & B))

    Eq << sets.el_intersect.imply.el.apply(Eq[0], 0)
    Eq << sets.el_intersect.imply.el.apply(Eq[0], 1)




if __name__ == '__main__':
    run()
# created on 2018-09-22
