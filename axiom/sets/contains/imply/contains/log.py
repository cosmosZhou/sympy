from util import *


@apply
def apply(given):
    e, interval = given.of(Contains)
    assert interval.is_Interval
    left_open = interval.left_open
    right_open = interval.right_open
    
    start = interval.start
    if left_open:
        if start > 0:
            start = log(start)
        elif start == 0:
            start = -oo
        else:
            return
    else:
        assert start > 0
        start = log(start)
        
    stop = log(interval.stop)
      
    return Contains(log(e), Interval(start, stop, left_open=left_open, right_open=right_open))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol.x(real=True)
    a = Symbol.a(real=True, positive=True)
    b = Symbol.b(real=True)
    Eq << apply(Contains(x, Interval(a, b)))

    Eq << sets.contains.imply.et.split.interval.apply(Eq[0])

    Eq << algebra.ge.imply.ge.log.apply(Eq[-2])

    Eq << algebra.ge.imply.is_positive.apply(Eq[2])
    Eq << algebra.is_positive.le.imply.le.log.apply(Eq[-1], Eq[3])

    Eq << sets.contains.given.et.split.interval.apply(Eq[1])


if __name__ == '__main__':
    run()