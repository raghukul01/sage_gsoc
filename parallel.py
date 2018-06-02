#from sage.schemes.generic.algebraic_scheme import AlgebraicScheme_subscheme
#rat_points = AlgebraicScheme_subscheme.rational_points

def func(Z, p):
    Xp = Z.change_ring(GF(p))
    L = Xp.rational_points()
    return [list(t) for t in L]


%time

from sage.parallel.ncpus import ncpus
from sage.parallel.use_fork import p_iter_fork

P.<x,y,z,q>=ProjectiveSpace(QQ,3)
Y=P.subscheme([x^2-3^2*y^2+z*q,x+z+4*q])
    
normalized_input = []

for q in primes(1,30):
    normalized_input.append(((Y, q, ), {}))
#    LL = func(Y,q)
    
p_iter = p_iter_fork(ncpus())

points_pair = list(p_iter(func, normalized_input))
points_pair.sort()

#print points_pair
modulo_points = []

for pair in points_pair:
    modulo_points.append(pair[1])
#print modulo_points