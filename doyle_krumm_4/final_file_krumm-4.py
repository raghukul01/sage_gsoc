from sage.rings.all import RR
from sage.rings.number_field.bdd_height import bdd_norm_pr_ideal_gens
from sage.rings.number_field.bdd_height import integer_points_in_polytope

def bdd_height(K, height_bound, tolerance=1e-2, precision=53):
    r""" 
    Computes all elements in the number field `K` which have relative
    multiplicative height at most ``height_bound``.

    The function will only be called for number fields `K` with positive unit
    rank. An error will occur if `K` is `QQ` or an imaginary quadratic field.

    This algorithm computes 2 list: L containing elements x in `K` such that
    H_k(x) <= B, and a list L' containing elements x in `K` such that
    abs(H_k(x) - B) < tolerance.

    In current implementation both lists (L,L') are merged and returned in
    form of iterator.


    ALGORITHM:

    This is an implementation of the revised algorithm (Algorithm 4) in
    [Doyle-Krumm].

    INPUT:

    - ``height_bound`` - real number
    - ``tolerance`` - a rational number in (0,1]
    - ``precision`` - (default: 53) positive integer

    OUTPUT:

    - an iterator of number field elements

    .. TODO::
    
        Need to add support for the case when `r=0` and
        `K` is `QQ`

    EXAMPLES:

    There are no elements of negative height::

        sage: from sage.rings.number_field.bdd_height import bdd_height
        sage: K.<g> = NumberField(x^5 - x + 7)
        sage: list(bdd_height(K,-3))
        []

    The only nonzero elements of height 1 are the roots of unity::

        sage: from sage.rings.number_field.bdd_height import bdd_height
        sage: K.<g> = QuadraticField(3)
        sage: list(bdd_height(K,1))
        [0, -1, 1]

    ::

        sage: from sage.rings.number_field.bdd_height import bdd_height
        sage: K.<g> = QuadraticField(36865)
        sage: len(list(bdd_height(K,101))) # long time (4 s)
        131

    ::

        sage: from sage.rings.number_field.bdd_height import bdd_height
        sage: K.<g> = NumberField(x^3 - 197*x + 39)
        sage: len(list(bdd_height(K, 200))) # long time (5 s)
        451

    ::

        sage: from sage.rings.number_field.bdd_height import bdd_height
        sage: K.<g> = NumberField(x^6 + 2)
        sage: len(list(bdd_height(K,60))) # long time (5 s)
        1899

    ::

        sage: from sage.rings.number_field.bdd_height import bdd_height
        sage: K.<g> = NumberField(x^4 - x^3 - 3*x^2 + x + 1)
        sage: len(list(bdd_height(K,10)))
        99

    TESTS:

    Check that :trac:`22771` is fixed::

        sage: from sage.rings.number_field.bdd_height import bdd_height
        sage: K.<v> = NumberField(x^3 + x + 1)
        sage: len(list(bdd_height(K,3)))
        23
    """

    # global values, used in internal function
    B = height_bound
    theta = tolerance
    if B < 1:
        return iter([])
    embeddings = K.places(prec=precision)
    O_K = K.ring_of_integers()
    r1, r2 = K.signature(); r = r1 + r2 -1
    RF = RealField(precision)
    lambda_gens_approx = dict()
    class_group_rep_norm_log_approx = []
    unit_log_dict = dict()

    def rational_in(x,y):
        r"""
        Computes a rational number q, such that x<q<y using Archimedes' axiom
        """
        z = y - x
        if z == 0:
            n = 1
        else:
            n = RR(1/z).ceil() + 1
        if RR(n*y).ceil() is n*y:
            m = n*y - 1
        else:
            m = RR(n*y).floor()
        return m/n

    def delta_approximation(x,delta):
        r"""
        Computes a rational number in range (x-delta,x+delta)
        """
        return rational_in(x-delta,x+delta)

    def vector_delta_approximation(v,delta):
        r"""
        Computes a rational vector w=(w1,...,wn)
        such that |vi-wi|<delta for all i in [1,n]
        """
        n = len(v)
        w = []
        for i in range(n):
            w.append(delta_approximation(v[i],delta))
        return w

    def log_map(number):
        r"""
        Computes the image of an element of `K` under the logarithmic map.
        """
        x = number
        x_logs = []
        for i in range(r1):
            sigma = embeddings[i] # real embeddings
            x_logs.append(abs(sigma(x)).log())
        for i in range(r1, r + 1):
            tau = embeddings[i] # Complex embeddings
            x_logs.append(2*abs(tau(x)).log())
        return vector(x_logs)

    def log_height_for_generators_approx(alpha,beta,Lambda):
        r"""
        Computes the rational approximation of logarithmic height function
        Returns a lambda approximation h_K(alpha/beta)
        """
        delta = Lambda / (r+2)
        norm_log = delta_approximation(RR(O_K.ideal(alpha,beta).norm()).log(),delta)
        log_ga = vector_delta_approximation(log_map(alpha),delta)
        log_gb = vector_delta_approximation(log_map(beta),delta)
        arch_sum = sum([max(log_ga[k], log_gb[k]) for k in range(r + 1)])
        return (arch_sum - norm_log)

    def packet_height(n, pair, u):
        r"""
        Computes the height of the element of `K` encoded by a given packet.
        """
        gens = generator_lists[n]
        i = pair[0] ; j = pair[1]
        Log_gi = lambda_gens_approx[gens[i]]; Log_gj = lambda_gens_approx[gens[j]]
        Log_u_gi = vector(Log_gi) + unit_log_dict[u]
        arch_sum = sum([max(Log_u_gi[k], Log_gj[k]) for k in range(r + 1)])
        return (arch_sum - class_group_rep_norm_log_approx[n])
    

    # Computes ideal class representative and their rational approx norm
    t = theta / (3*B)
    delta_1 = t / (6*r+12)

    class_group_reps = []
    class_group_rep_norms = []

    for c in K.class_group():
        a = c.ideal()
        a_norm = a.norm()
        log_norm = RF(a_norm).log()
        log_norm_approx = delta_approximation(log_norm,delta_1)
        class_group_reps.append(a)
        class_group_rep_norms.append(a_norm)
        class_group_rep_norm_log_approx.append(log_norm_approx)
    class_number = len(class_group_reps)


    # Find generators for principal ideals of bounded norm
    possible_norm_set = set([])
    for n in range(class_number):
        for m in range(1,B+1):
            possible_norm_set.add(m*class_group_rep_norms[n])
    bdd_ideals = bdd_norm_pr_ideal_gens(K, possible_norm_set)

    # Stores it in form of an dictionary and gives lambda(g)_approx for key g 
    for norm in possible_norm_set:
        gens = bdd_ideals[norm]
        for g in gens:
            lambda_g_approx = vector_delta_approximation(log_map(g),delta_1)
            lambda_gens_approx[g] = lambda_g_approx


    # Find a list of all generators corresponding to each ideal a_l
    generator_lists = []
    for l in range(class_number):
        this_ideal = class_group_reps[l]
        this_ideal_norm = class_group_rep_norms[l]
        gens = []
        for i in range(1, B + 1):
            for g in bdd_ideals[i*this_ideal_norm]:
                if g in this_ideal:
                    gens.append(g)
        generator_lists.append(gens)


    # Finds all relevent pair and thier height
    gen_height_approx_dictionary = dict()
    relevant_pair_lists = []

    for n in range(class_number):
        relevant_pairs = []
        gens = generator_lists[n]
        l = len(gens)
        for i in range(l):
            for j in range(i+1,l):
                if K.ideal(gens[i], gens[j]) == class_group_reps[n]:
                    relevant_pairs.append([i,j])
                    gen_height_approx_dictionary[(n,i,j)] = log_height_for_generators_approx(gens[i],gens[j],t/6)
        relevant_pair_lists.append(relevant_pairs)

    b = rational_in(t/12 + RR(B).log(), t/4 + RR(B).log())
    maximum = 0
    for n in range(class_number):
        for p in relevant_pair_lists[n]:
            maximum = max(maximum,gen_height_approx_dictionary[(n,p[0],p[1])])
    d_tilde = b + t/6 + maximum

    # computes fundamental units and their value under log map
    fund_units = UnitGroup(K).fundamental_units()
    fund_unit_logs = [log_map(fund_units[i]) for i in range(r)]
    S = column_matrix(fund_unit_logs).delete_rows([r])
    S_inverse = S.inverse()
    S_norm = S.norm(Infinity)
    S_inverse_norm = S_inverse.norm(Infinity)

    upper_bound = (r^2) * max(S_norm,S_inverse_norm)
    m = RR(upper_bound).ceil() + 1

    # Variables needed for rational approximation
    lambda_tilde = (t/12) / (d_tilde*r*(1+m))
    delta_tilde = min(lambda_tilde/((r^2)*((m^2)+m*lambda_tilde)), 1/(r^2))
    M = d_tilde * (upper_bound+lambda_tilde*RR(r).sqrt())
    M = RR(M).ceil()
    delta_2 = min(delta_tilde,(t/6)/(r*(r+1)*M))

    # Computes relevant points in polytope
    fund_unit_log_approx = [vector_delta_approximation(fund_unit_logs[i],delta_2) for i in range(r)]
    S_tilde = column_matrix(fund_unit_log_approx).delete_rows([r])
    S_tilde_inverse = S_tilde.inverse()
    U = integer_points_in_polytope(S_tilde_inverse, d_tilde)

    # tilde suffixed list are used for computing second list (L_primed)
    LL = [K(0)]
    U0 = []
    U0_tilde = []
    L0 = []
    L0_tilde = []

    # Computes unit height
    unit_height_dict = dict()
    U_copy = copy(U)
    inter_bound = b - (5*t)/12

    for u in U:    
        u_log = sum([u[j]*vector(fund_unit_log_approx[j]) for j in range(r)])
        unit_log_dict[u] = u_log
        u_height = sum([max(u_log[k], 0) for k in range(r + 1)])
        unit_height_dict[u] = u_height
        if u_height < inter_bound:
                U0.append(u)
        if inter_bound <= u_height and u_height < b - (t/12):
            U0_tilde.append(u)
        if u_height > t/12 + d_tilde:
            U_copy.remove(u)
    U = U_copy

    relevant_tuples = set(U0+U0_tilde)

    # check for relevant packets
    for n in range(class_number):
        for pair in relevant_pair_lists[n]:
            i = pair[0]; j = pair[1]
            u_height_bound = b + gen_height_approx_dictionary[(n,i,j)] + t/4
            for u in U:
                if unit_height_dict[u] < u_height_bound:
                    candidate_height = packet_height(n,pair,u)
                    if candidate_height <= b - (7/12)*t:
                        L0.append([n,pair,u])
                        relevant_tuples.add(u);
                    if candidate_height > b - (7/12)*t and candidate_height < b + t/4:
                        L0_tilde.append([n,pair,u])
                        relevant_tuples.add(u);

        
    # forms a dictionary of all_unit_tuples and thier value
    tuple_to_unit_dict = dict()
    for u in relevant_tuples:
        unit = K(1)
        for k in range(r):
            unit *= (fund_units[k]^u[k])
        tuple_to_unit_dict[u] = unit

    # Build all output numbers
    L_primed = [] # This list contain points such that abs(H_k(u)-B) < tolerance
    roots_of_unity = K.roots_of_unity()
    for u in U0:
        for zeta in roots_of_unity:
            LL.append(zeta*tuple_to_unit_dict[u])
    for u in U0_tilde:
        for zeta in roots_of_unity:
            L_primed.append(zeta*tuple_to_unit_dict[u])
    for p in L0:
        gens = generator_lists[p[0]]
        i = p[1][0]; j = p[1][1]
        u = p[2]
        c_p = tuple_to_unit_dict[u] * (gens[i]/gens[j])
        for zeta in roots_of_unity:
            LL.append(zeta*c_p)
            LL.append(zeta/c_p)
    for p in L0_tilde:
        gens = generator_lists[p[0]]
        i = p[1][0]; j = p[1][1]
        u = p[2]
        c_p = tuple_to_unit_dict[u] * (gens[i]/gens[j])
        for zeta in roots_of_unity:
            L_primed.append(zeta*c_p)
            L_primed.append(zeta/c_p)

    return iter(LL + L_primed)