%time
m=[]
for i in range(N+1):
    w=[0 for j in range(N)]
    w.insert(i,D)
    m.extend(w)

M=matrix(ZZ,N+2,N+1,list(point) +m)

#######################################

bound=10
N=3 # dimension
B = (2**(N/4+1)*bound**2*sqrt(N+1)).n()
B

#######################################

2*5*7*11

#######################################

used_primes=[2,3]
prod_primes=6
LLL_c=1000
while prod_primes < LLL_c:
    p = next_prime(used_primes[-1])
    used_primes.append(p)
    prod_primes *= p
used_primes

#######################################

%time
def sieve(X, primes, bound):
    P = X.ambient_space()
    N = P.dimension()
    B = (2**(N/4+1)*bound**2*sqrt(N+1)).n()
    L=[]
    #this part is best done in parrellel - maybe later improvement...
    for p in primes:
        Xp=X.change_ring(GF(p))
        L.append(Xp.rational_points())
    t = [len(l) for l in L]
    print t
    D=prod(primes)
    print "D:",D,
    if D > B:
        print "good",B
    else:
        print "bad",B
    
    rat_points=set()
    count_lifted=0  
    for v in xmrange(t):
        point=[]
        for k in range(N+1):
            point.append(crt([L[j][v[j]][k].lift() for j in range(len(primes))],primes))
        count_lifted+=1
        m=[]
        for i in range(N+1):
            w=[0 for j in range(N)]
            w.insert(i,D)
            m.extend(w)

        M=matrix(ZZ,N+2,N+1,list(point) +m)
        A=M.LLL()
        try:
            rat_points.add(X(list(A[1])))
        except:
            pass
    return list(rat_points), count_lifted

#######################################

sage: FF = FiniteField(7)
            sage: P.<x> = PolynomialRing(FiniteField(7))
            sage: C = C.ambient_space().subscheme(x^8+x+1)
            sage: C.rational_points()

#######################################

prod(primes(1,13))

#######################################

2310/672.

#######################################

%time
#CPU time: 7.35 s,  Wall time: 7.49 s
P.<x,y,z,q>=ProjectiveSpace(QQ,3)
Y=P.subscheme([x^2-3^2*y^2+z*q,x+z+4*q])
sieve(Y, [2,3,5,7,11],10)

#######################################

Y(QQ).points()

#######################################

%time
#CPU time: 7.35 s,  Wall time: 7.49 s
P.<x,y,z,q>=ProjectiveSpace(QQ,3)
Y=P.subscheme([x^2-3^2*y^2+z*q,x+z+4*q])
sieve(Y, list(primes(1,12)),10)

#######################################

%time
P.<x,y,z>=ProjectiveSpace(QQ,2)
X=P.subscheme([y^2*z - x^3 -x*z^2+z^3])
prime_list = [2,3,5,7,13]
bound=50
rat=sieve(X,prime_list,bound)
len(rat[0]),rat[1]

#######################################

E=EllipticCurve([1,-1])
E.mwrank()

#######################################

Q=E(1,1,1)
[t*Q for t in range(1,6)]

#######################################

%time
X.rational_points()

#######################################

X.dimension()

#######################################

%time
P.<x,y,z,w>=ProjectiveSpace(QQ,3)
X=P.subscheme([x^2-85^2*y^2,x+z,w^2-9*x^2])
prime_list = [3,7,11,13,211,151]
bound=100
sieve(X,prime_list,bound)

#######################################

%time
X.rational_points()

#######################################

%time
P.<x,y,z,w>=ProjectiveSpace(QQ,3)
X=P.subscheme([x^2-85^2*y^2,x+z,w^2-9*x^2])
bound=100
sieve(X,list(primes(1,24)),bound)

#######################################

%time
P.<x,y,z>=ProjectiveSpace(QQ,2)
X=P.subscheme([x^2-25^2*y^2])
print X.dimension()
prime_list = [11,19,23]
bound=100
len(sieve(X,prime_list,bound))

#######################################

%time
P.<x,y,z>=ProjectiveSpace(QQ,2)
X=P.subscheme([x^2-25^2*y^2])
print X.dimension()
prime_list = [11,19,23]
bound=100
len(sieve(X,list(primes(1,13)),bound))

#######################################

def point_search(X, [p,q]):
    #does the work
    
    return points

#######################################