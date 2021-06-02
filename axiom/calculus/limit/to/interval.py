from util import *


@apply
def apply(self, doit=True): 
    expr, (x, x0, dir) = self.of(Limit)
    start, stop = expr.of(Interval)
    start = Limit[x:x0:dir](start)
    stop = Limit[x:x0:dir](stop)
    if doit:
        start = start.doit()
        stop = stop.doit()
        
    return Equal(self, expr.copy(start=start, stop=stop))


@prove(surmountable=False)
def prove(Eq):
    n = Symbol.n(integer=True)
    
    Eq << apply(Limit[n:oo](Interval(0, n)))    

    
if __name__ == '__main__':
    run()
