from sage.rings.all import RR
from sage.parallel.ncpus import ncpus
from sage.parallel.use_fork import p_iter_fork

def sieve(X, bound):
    r"""
    Returns the list of all projective, rational points on scheme ``X`` of
    height up to ``bound``.

    This algorithm algorithm works correctly only if dimension of given
    scheme is positive.

    INPUT:

    - ``X`` - a scheme with ambient space defined over projective sapce

    - ``bound`` - a positive integer bound

    OUTPUT:

     - a list containing the projective rational points of ``X`` of height
     up to ``B``, sorted

    EXAMPLES::
        
        sage: u = QQ['u'].0
        sage: K = NumberField(u^3 - 5, 'v')
        sage: P.<x,y,z> = ProjectiveSpace(K, 2)
        sage: X = P.subscheme([x - y])
        sage: sieve(X, 5)

        [(-5/3 : -5/3 : 1), (-1/2 : -1/2 : 1), (-3 : -3 : 1),
         (-4/5 : -4/5 : 1), (-2/5 : -2/5 : 1), (-4/3 : -4/3 : 1),
         (5 : 5 : 1), (-4 : -4 : 1), (4 : 4 : 1), (-3/5 : -3/5 : 1),
         (1 : 1 : 1), (2/3 : 2/3 : 1), (3/4 : 3/4 : 1), (-2/3 : -2/3 : 1),
         (1/5 : 1/5 : 1), (-3/4 : -3/4 : 1), (-1/5 : -1/5 : 1),
         (-5 : -5 : 1), (-2 : -2 : 1), (-1 : -1 : 1),
         (5/4 : 5/4 : 1), (4/3 : 4/3 : 1), (0 : 0 : 1), (-5/2 : -5/2 : 1),
         (1/4 : 1/4 : 1), (1/3 : 1/3 : 1), (-5/4 : -5/4 : 1),
         (1/2 : 1/2 : 1), (5/2 : 5/2 : 1), (5/3 : 5/3 : 1),
         (3/2 : 3/2 : 1), (1 : 1 : 0), (2 : 2 : 1), (-1/3 : -1/3 : 1),
         (3 : 3 : 1), (-3/2 : -3/2 : 1), (-1/4 : -1/4 : 1),
         (2/5 : 2/5 : 1), (4/5 : 4/5 : 1), (3/5 : 3/5 : 1)]
    
    ::

        sage: E = EllipticCurve('37a')
        sage: sieve(E, 25) # long time (5 s)
        [(-1 : -1 : 1), (-1 : 0 : 1), (0 : -1 : 1),
         (0 : 0 : 1), (0 : 1 : 0), (1/4 : -5/8 : 1),
         (1/4 : -3/8 : 1), (1 : -1 : 1), (1 : 0 : 1),
         (2 : -3 : 1), (2 : 2 : 1), (6 : -15 : 1),
         (6 : 14 : 1)]

    TESTS:

    This example illustrate speed of algorithm::

        sage: P.<x,y,z,q>=ProjectiveSpace(QQ,3)
        sage: Y=P.subscheme([x^2-3^2*y^2+z*q,x+z+4*q])
        sage: len(sieve(Y, 8))
        2
        sage: Y.rational_points(8) # long time (5 s)
        2

    """

    modulo_points = [] # list to store point modulo primes
    len_modulo_points = [] # stores number of points with respect to each prime
    primes = [] # list of good primes
    P = X.ambient_space()
    N = P.dimension()
    dim_scheme = X.dimension()

    # bound as per preposition - 4, in preperiodic points paper
    B = (2**(N/4+1)*bound**2*sqrt(N+1)).n()

    m = [0 for _ in range(N + 1)]

    def sufficient_primes(x):
        r"""
        Returns a list of primes whose product is > `x`
        """
        small_primes = [2,3]
        prod_primes = 6

        while prod_primes < x:
            p = next_prime(small_primes[-1])
            small_primes.append(p)
            prod_primes *= p
        return small_primes

    def good_primes(B):
        r"""
        Given the bound returns the prime whose product is greater than ``B``
        and which would take least amount of time to run main sieve algorithm

        Complexity of finding points modulo primes is assumed to be N^2 * P_max^{N}.
        Complexity of lifting points and LLL() function is assumed to
        be close to N^5 * (alpha^dim_scheme / P_max).
        where alpha is product of all primes, and P_max is largest prime in list.
        """

        M = dict() # stores optimal list of primes, corresponding to list size
        small_primes = sufficient_primes(B)
        max_length = len(small_primes)
        M[max_length] = small_primes
        current_count = max_length - 1
        
        while current_count > 1:
            current_list = [] # stores prime which are bigger than least
            updated_list = []
            best_list = []
            
            least = (B.n()**(1.00/current_count)).floor()
            for i in range(current_count):
                current_list.append(next_prime(least))
                least = current_list[-1]
            # improving list of primes by taking prime less than least
            # this part of algorithm is used to centralize primes around `least`
            prod_prime = prod(current_list)
            least = current_list[0]
            while least != 2 and prod_prime > B and len(updated_list) < current_count:
                best_list = updated_list + current_list[:current_count - len(updated_list)]
                updated_list.append(previous_prime(least))
                least = updated_list[-1]
                
                removed_prime = current_list[current_count - len(updated_list)]
                prod_prime = (prod_prime * least) / removed_prime

            M[current_count] = sorted(best_list)
            current_count = current_count - 1

        best_size = 2
        best_time = (N**2)*M[2][-1]**(N) + (N**5 * (prod(M[2])**dim_scheme / M[2][-1]).n() )
        for i in range(2, max_length + 1):
            current_time = (N**2)*M[i][-1]**(N) + (N**5 * (prod(M[i])**dim_scheme  / M[i][-1]).n() )
            if current_time < best_time:
                best_size = i
                best_time = current_time

        return M[best_size]

    def parallel_function(X, p):
        r"""
        Function used in parallel computation, computes a list of
        all rational points in modulo ring.
        """
        Xp = X.change_ring(GF(p))
        L = Xp.rational_points()

        return [list(_) for _ in L]

    def points_modulo_primes(X, primes):
        r"""
        Return a list of rational points modulo all `p` in primes,
        computed parallely.
        """
        normalized_input = []
        for p in primes:
            normalized_input.append(((X, p, ), {}))
        p_iter = p_iter_fork(ncpus())

        points_pair = list(p_iter(parallel_function, normalized_input))
        points_pair.sort()
        modulo_points = []
        for pair in points_pair:
            modulo_points.append(pair[1])

        return modulo_points

    def parallel_function_combination(point_p_max):
        r"""
        Function used in parallel computation, computes rational
        points lifted. 
        """
        rat_points = set()
        for tupl in xmrange(len_modulo_points):
            point = []
            for k in range(N + 1):
                # lift all dimensions of given point using chinese remainder theorem
                L = [modulo_points[j][tupl[j]][k].lift() for j in range(len_primes - 1)]
                L.append(point_p_max[k].lift())
                point.append( crt(L, primes) )

            for i in range(N+1):
                m[i] = point[i]

            M = matrix(ZZ, N+2, N+1, m)
            A = M.LLL()
            point = list(A[1])

            # check if all coordinates of this point satisfy height bound
            bound_satisfied = true
            for coordinate in point:
                if coordinate.abs() > bound:
                    bound_satisfied = false
            if not bound_satisfied:
                continue

            try:
                rat_points.add(X(list(A[1]))) # checks if this point lies on X or not
            except:
                pass

        return [list(_) for _ in rat_points]

    def lift_all_points():
        r"""
        Returns list of all rational points lifted parallely.
        """
        normalized_input = []
        points = modulo_points[-1]
        modulo_points.pop() # remove the list of points corresponding to largest prime
        len_modulo_points.pop() 

        for point in points:
            normalized_input.append(( (point, ), {}))
        p_iter = p_iter_fork(ncpus())
        points_satisfying = list(p_iter(parallel_function_combination, normalized_input))

        lifted_points = set()
        for pair in points_satisfying:
            L = pair[1]
            for point in L:
                lifted_points.add(X(point))

        return list(lifted_points)


    # start of main algorithm

    primes = good_primes(B.ceil())

    modulo_points = points_modulo_primes(X,primes)
    len_modulo_points = [len(_) for _ in modulo_points]
    len_primes = len(primes)
    prod_primes = prod(primes)

    # stores final result
    rat_points = set()

    for i in range(N + 1):
        w = [0 for _ in range(N + 1)]
        w[i] = prod_primes
        m.extend(w)

    rat_points = lift_all_points()

    return sorted(rat_points)