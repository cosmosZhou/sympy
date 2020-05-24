from axiom.prove import prove
import sys
# to run this script, please install:
# pip install mpmath==1.1.0       

if __name__ == '__main__':
    if len(sys.argv) == 1:
        prove()
    else:        
        package = sys.argv[1]
        if package.startswith('axiom'):
            package = 'sympy.' + package
        package = eval(package)
        ret = package.prove(package.__file__)
        if ret is False:
            print(package, 'is unproven')
        elif ret is None:
            print(package, 'is erroneous')

