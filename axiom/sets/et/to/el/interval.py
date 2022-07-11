from util import *


@apply(given=None)
def apply(given):
    cond0, cond1 = given.of(And)
    x, y = cond0.args
    a, b = cond1.args

    if cond0.is_Less:
        #x < y
        if cond1.is_Greater:
            #a > b
            if x == a:
                e = x
                left_open = True
                right_open = True
                start = b
                stop = y
            else:
                ...
        elif cond1.is_Less:
            #a < b
            if y == a:
                e = a
                left_open = True
                right_open = True
                start = x
                stop = b
        #x < y
        if cond1.is_GreaterEqual:
            #a >= b
            if x == a:
                e = x
                left_open = False
                right_open = True
                start = b
                stop = y
            else:
                ...
    elif cond0.is_LessEqual:
        #x < y
        if cond1.is_GreaterEqual:
            #a >= b
            if x == a:
                e = x
                left_open = False
                right_open = False
                start = b
                stop = y
            else:
                ...



    return Equivalent(given, Element(e, Interval(start, stop, left_open=left_open, right_open=right_open)), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, sets

    x, a, b = Symbol(integer=True)
    Eq << apply((a < x) & (x < b))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.lt.lt.imply.el.interval)

    Eq << Eq[-1].this.rhs.apply(sets.el_interval.imply.et)



    Eq << Eq[-1].this.find(Greater).reversed




if __name__ == '__main__':
    run()
# created on 2022-01-07
