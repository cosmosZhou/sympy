from util import *


@apply
def apply(self, rho=None, theta=None):    
    if rho is None:
        rho = Symbol.rho(real=True)
    if theta is None:
        theta = Symbol.theta(real=True)
        
    _x = rho * cos(theta)
    _y = rho * sin(theta)

    J = Matrix([_x, _y]).jacobian(Matrix([rho, theta]))
    J = J.det().trigsimp()
    
    x, y = (var for var, *_ in self.limits)
    function = self.function.subs({x:_x, y:_y}, simultaneous=True).trigsimp()
    limits = [(rho, 0, oo), (theta, -pi, pi)]
    rhs = self.func(J * function, *limits)

    return Equal(self, rhs, evaluate=False)


@prove(proved=False)
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    Eq << apply(Integral[x, y](E ** (-x ** 2 / 2 - y ** 2 / 2)))

    

    

    

    

    

    

    

    #https://ccjou.wordpress.com/2012/11/26/jacobian-矩陣與行列式/


if __name__ == '__main__':
    run()