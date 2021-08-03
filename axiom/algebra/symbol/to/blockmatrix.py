from util import *


def process_slice(index, self_start, self_stop):
    start, stop = index.start, index.stop
    if start is None:
        start = self_start
    else:
        start = sympify(start)
        
    if stop is None:
        stop = self_stop
    else:
        stop = sympify(stop)

    if stop == self_stop:
        if start == self_start:
            return
        if start < 0:
            start = self_stop + start
        mid = start            
    elif start == self_start:
        if stop < 0:
            stop = self_stop + stop
        mid = stop 
    else:
        return start, stop
    
    return mid        

def symbol_split(self, indices):
    assert self.shape
    return symbol_slice(self, indices, 0, self.shape[0])
    
def symbol_slice(self, index, self_start, self_stop, allow_empty=False): 
    mid = process_slice(index, self_start, self_stop)
    if mid is None:
        return self
    
    if allow_empty:
        assert mid >= self_start, "mid >= self_start => %s" % (mid >= self_start)
    else: 
        assert mid > self_start, "mid > self_start => %s" % (mid > self_start)
         
    assert mid < self_stop, "mid < self_stop => %s" % (mid < self_stop)
    
    if isinstance(mid, tuple):
        start, stop = mid
        assert start < stop, "start < stop => %s" % (start < stop)
        return BlockMatrix(self[self_start: start], self[start: stop], self[stop:self_stop])
    
    return BlockMatrix(self[self_start:mid], self[mid:self_stop])
     
        
    return self

@apply
def apply(self, index=-1):
    rhs = symbol_split(self, slice(0, index))
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(n + 1,))
    y = Symbol.y(real=True, shape=(oo,))
    Eq << apply(x)

    i = Symbol.i(domain=Range(0, n + 1))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)
    Eq << Eq[-1].this.rhs.apply(algebra.piecewise.to.kroneckerDelta)


if __name__ == '__main__':
    run()