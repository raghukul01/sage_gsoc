def parallel_function(X, p):
    r"""
    function to be used in parallel computation,
    returns a list of all rational points in modulo ring
    """
    Xp = X.change_ring(GF(p))
    L = Xp.rational_points()

    return [list(_) for _ in L]

def points_modulo_primes(X, primes):
    r"""
    Return a list of rational points modulo all p in primes
    parallel implementation
    """
    normalized_input = []
    for p in primes:
        normalized_input.append(((X, p, ), {}))
    p_iter = p_iter_fork(ncpus())

    points_pair = list(p_iter(parallel_function, normalized_input))
    points_pair.sort()
    modulo_points = dict()
    for i in range(len(primes)):
        modulo_points[primes[i]] = points_pair[i][1]

    return modulo_points

def primes_less_than_n(n):
    r"""
    returns all primes less than n
    """
    count = pari(n).primepi()
    return list(primes_first_n(count))

def count_points(K, bound):
    r"""
    count modulo points corresponding to all primes less than B
    """
    P = Z.ambient_space()
    N = P.dimension()
    B = B = (2**(N/4+1)*bound**2*sqrt(N+1)).n().ceil()
    primes = primes_less_than_n(B)

    modulo_points = points_modulo_primes(K, primes)

    for p in modulo_points:
        print p[0], len(p[1])


def sufficient_primes(x):
    r"""
    Returns a list of primes whose product is > `x`
    """
    primes = [2,3]
    prod_primes = 6

    while prod_primes < x:
        p = next_prime(primes[-1])
        primes.append(p)
        prod_primes *= p
    return primes



def good_primes(B, N):
    r"""
    Given the bound returns the prime whose product is greater than B
    and which would yeild most efficient complexity of sieve algorithm
    """
    # complexity of part 1 is assumed to be (N**2)*P_max^{N}
    # Complexity of part 2 is N^5 * (alpha / P_max) alpha is product of all primes

    M = dict() # stores the list of primes as value for no of primes as key.
    L = sufficient_primes(B)
    max_length = len(L)
    M[max_length] = L
    current_count = max_length - 1
    
    while current_count > 1:
        current_list = []
        least = (B.n()**(1.00/current_count)).ceil()
        for i in range(current_count):
            current_list.append(next_prime(least))
            least = current_list[-1]
        M[current_count] = current_list

        current_count = current_count - 1

    best_size = 2
    best_time = M[2][-1]**N + (N**5 * (prod(M[2]) / M[2][-1]).n() )
    for i in range(2, max_length + 1):
        current_time = M[i][-1]**N + (N**5 * (prod(M[i])  / M[i][-1]).n() )
        if current_time < best_time:
            best_size = i
            best_time = current_time

    return M[best_size]


    def good_primes(B, N):
        r"""
        Given the bound returns the prime whose product is greater than B
        and which would yeild most efficient complexity of sieve algorithm
        """
        # complexity of part 1 is assumed to be N^5*P_max^{N}
        # Complexity of part 2 is N^5 * (alpha / P_max) alpha is product of all primes

        M = dict() # stores the list of primes as value for no of primes as key.
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
            # imporving list of primes by taking prime less than least
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
        best_time = (N**2)*M[2][-1]**(N) + (N**5 * (prod(M[2]) / M[2][-1]).n() )
        for i in range(2, max_length + 1):
            current_time = (N**2)*M[i][-1]**(N) + (N**5 * (prod(M[i])  / M[i][-1]).n() )
            if current_time < best_time:
                best_size = i
                best_time = current_time

        return M[best_size]



def parallel_function_combination(point_p_max, p_max):
    r"""
    INPUT:
    - point_p_max : a point modulo p on given subscheme
              (point given in form of list, due to pickle error)
    - p     : the prime corresponding to which point is given

    OUTPUT:
    list of lifted points which are on subscheme 
    """
    rat_points = []
    for tupl in xmrange(len_modulo_points):
        point = []
        for k in range(N + 1):
            # list all dimensions of given point using chinese remainder theorem
            point.append( crt([ modulo_points[j][tupl[j]][k].lift() for j in range(len_primes - 1), point_p_max[k].lift() ], primes) )
        
        for i in range(N+1):
            m[i] = point[i]

        M = matrix(ZZ, N+2, N+1, m)
        A = M.LLL()
        point = list(A[1])

        # check if all coordinates of this point satisfy bound
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
    returns the list of all points which
    parallely computed
    """
    normalized_input = []
    p_max = primes[-1]
    points = modulo_points[-1]
    modulo_points.pop() # remove the list of points corresponding to largest prime
    len_modulo_points.pop() 

    for point in points:
        normalized_input.append(( (point, p_max, ), {}))
    p_iter = p_iter_fork(ncpus())

    points_satisfying = list(p_iter(parallel_function_combination, normalized_input))

    lifted_points = []
    for pair in points_satisfying:
        L = pair[1]
        for point in L:
            lifted_points.append(X(point))

    return sorted(lifted_points)