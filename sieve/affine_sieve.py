def sieve(X, bound):
    r"""
    Returns the list of all affine, rational points on scheme ``X`` of
    height up to ``bound``.

    This algorithm algorithm works correctly only if dimension of given
    scheme is positive.

    INPUT:

    - ``X`` - a scheme with ambient space defined over projective sapce

    - ``bound`` - a positive integer bound

    OUTPUT:

     - a list containing the affine rational points of ``X`` of height
     up to ``B``, sorted

    EXAMPLES::

    TESTS:

    This example illustrate speed of algorithm::

    """
    modulo_points = [] # list to store point modulo primes
    len_modulo_points = [] # stores number of points with respect to each prime
    primes = [] # list of good primes
    P = X.ambient_space()
    N = P.dimension()
    dim_scheme = X.dimension()

    # bound as per preposition - 4, in preperiodic points paper
    B = RR(2**(N/4+1)*bound**2*(N+1).sqrt())

    m = [0 for _ in range(N)]

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
            
            least = (RR(B)**(1.00/current_count)).floor()
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
        best_time = (N**2)*M[2][-1]**(N) + (N**5 * RR(prod(M[2])**dim_scheme / M[2][-1]) )
        for i in range(2, max_length + 1):
            current_time = (N**2)*M[i][-1]**(N) + (N**5 * RR(prod(M[i])**dim_scheme  / M[i][-1]) )
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
        rat_points = []
        for tupl in xmrange(len_modulo_points):
            point = []
            for k in range(N):
                # lift all dimensions of given point using chinese remainder theorem
                L = [modulo_points[j][tupl[j]][k].lift() for j in range(len_primes - 1)]
                L.append(point_p_max[k].lift())
                point.append( crt(L, primes) )

            for i in range(N):
                m[i] = point[i]

            M = matrix(ZZ, N+1, N, m)
            A = M.LLL()
            point = list(A[1])
            # point.normalize_coordinates()

            # check if all coordinates of this point satisfy height bound
            bound_log = bound.log()
            bound_satisfied = True
            for coordinate in point:
                if coordinate.global_height() > bound_log:
                    bound_satisfied = False
            if not bound_satisfied:
                continue

            try:
                rat_points.append(X(point))
                # rat_points.insert(X(list(A[1]))) # checks if this point lies on X or not
            except:
                pass
        print rat_points
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

        lifted_points = []
        for pair in points_satisfying:
            L = pair[1]
            for p1 in L:
                present = False
                for p2 in lifted_points:
                    are_same = True
                    for i in range(N):
                        if p1[i] != p2[i]:
                            are_same = False
                    if are_same:
                        present = True
                if not present:
                    lifted_points.append(X(tuple(p1)))

        return lifted_points


    # start of main algorithm

    primes = good_primes(B.ceil())

    modulo_points = points_modulo_primes(X,primes)
    len_modulo_points = [len(_) for _ in modulo_points]
    len_primes = len(primes)
    prod_primes = prod(primes)

    # stores final result
    rat_points = set()

    for i in range(N):
        w = [0 for _ in range(N)]
        w[i] = prod_primes
        m.extend(w)

    rat_points = lift_all_points()

    return sorted(rat_points)



def sieve_tivial(S, bound):
    r"""
    computes rational point less than bound for an affine scheme,
    but using the rational_point function of projective scheme
    """
    pi = S.projective_embedding(0)
    P = pi.codomain()

    AA = P.affine_patch(0)
    
    proj_L = P.rational_points(bound)
    LL = set()
    for point in proj_L:
        pt = []
        denom = point[0]
        if denom == 0:
            continue

        for i in range(1,len(point)):
            pt.append(point[i] / denom)
        LL.add(AA(pt))

    return sorted(list(LL))