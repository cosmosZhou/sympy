from util import *



@apply
def apply(imply):
    assert imply.is_Element

    e, interval = imply.args

    return Element(-e, -interval)


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol(integer=True)
    a, b = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << sets.el.imply.el.neg.apply(Eq[1])


if __name__ == '__main__':
    run()

