from sage.rings.all import RR
from sage.rings.number_field.bdd_height import bdd_norm_pr_ideal_gens
from sage.rings.number_field.bdd_height import integer_points_in_polytope

def bdd_height(K, height_bound, tolerance=1e-5, precision=53):
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
    	sage: len(list(bdd_height(K,3,1e-5)))
    	23
	"""

	B = height_bound
	theta = tolerance
	embeddings = K.places(prec=precision)
	O_K = K.ring_of_integers()
	r1, r2 = K.signature(); r = r1 + r2 -1
	fund_units = UnitGroup(K).fundamental_units()
	RF = RealField(precision)

	# #CHECK there is some difference between this implementation 
	# and notebook implementation
	def rational_in(x,y):
		r"""
		Computes a rational number q, such that x<q<y using Archimedes' axiom
		"""
		z = y - x
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
		Returns a lambda approximation h_K(alpha/beta) using lemma 4.1
		"""
		delta = Lambda / (r+2)
		norm_log = delta_approximation(RR(O_K.ideal(alpha,beta).norm()).log(),delta)
		log_ga = vector_delta_approximation(log_map(alpha),delta)
		log_gb = vector_delta_approximation(log_map(beta),delta)
		arch_sum = sum([max(log_ga[k], log_gb[k]) for k in range(r + 1)]) # In notebook, sum is till r, #CHECK
		return (arch_sum - norm_log)

	# ignore if not needed
	# def lambda(x,K):
	# 	r"""
	# 	Computes an (r+1)-tuple of absolute values of x under
	# 	different embeddings of K into RR and CC
	# 	"""


	# start of main algorithm
	

	r"""
	need to add support when r = 0
	case I: when it is imagenary quadratic field
		this case is done bdd_height_iq() function exists
	case II: when it is field of rational numbers (Q)
		need to discuss this #TODO
	"""

	# Step 1
	t = theta / (3*B)
	delta_1 = t / (6*r+12)

	class_group_reps = []
    class_group_rep_norms = []
    class_group_rep_norm_log_approx = []

    for c in K.class_group():
    	a = c.representative_prime() # in algorithm 3 this is replaced by .ideal() #CHECK
    	a_norm = a.norm()
    	log_norm = RF(a_norm).log()
    	log_norm_approx = delta_approximation(log_norm,delta_1)
    	class_group_reps.append(a)
    	class_group_rep_norms.append(a_norm)
    	class_group_rep_norm_log_approx.append(log_norm_approx)
    h = len(class_group_reps) # Replace this by a better name (maybe class_number) #TODO

    # Step 2

    # Find generators for principal ideals of bounded norm
    possible_norm_set = set([])
    for n in range(h): # replace this h with better name #TODO
        for m in range(1,B+1):
            possible_norm_set.add(m*class_group_rep_norms[n])
    bdd_ideals = bdd_norm_pr_ideal_gens(K, possible_norm_set)

    # Find the delta_1 approximation of lambda (used log_map() instead) #CHECK
    # stores it in form of an dictionary and gives lambda(g)_approx for key g 
    lambda_gens_approx = dict()
    for norm in possible_norm_set:
    	gens = bdd_ideals[norm]
    	for g in gens:
    		lambda_g_approx = vector_delta_approximation(log_map(g),delta_1)
    		lambda_gens_approx[g] = lambda_g_approx

    # Step 3

    # Find a list of all generators corresponding to each ideal a_l
    # list s stores the count of generators corresponding to a_l
    # #TODO remove this s if not needed
    s = []
    generator_lists = []
	for l in range(h): # replace this h with better name #TODO
		this_ideal = class_group_reps[l]
		this_ideal_norm = class_group_rep_norms[l]
		gens = []
		for i in range(1, B + 1):
		    for g in bdd_ideals[i*this_ideal_norm]:
		        if g in this_ideal:
		            gens.append(g)
		s.append(len(gens))
		generator_lists.append(gens)

	# Step 4

	# Finds all relevent pair which satisfy 4(a)
	gen_height_approx_dictionary = dict() # stores height for further use
    relevant_pair_lists = []

    for n in range(h): # replace h with better name #TODO
    	relevant_pairs = []
    	gens = generator_lists[n]
    	l = len(gens)
    	for i in range(l):
    		for j in range(i+1,l):
    			if K.ideal(gens[i], gens[j]) == class_group_reps[n]:
    				relevant_pairs.append([i,j])
    				gen_height_approx_dictionary[(n,i,j)] = log_height_for_generators_approx(gens[i],gens[j],t/6)
    	relevant_pair_lists.append(relevant_pairs)

    # Step 5
    # Computes the value of b, d_tilde which is need in further steps
    b = rational_in(t/12 + RR(B).log(), t/4 + RR(B).log())
    maximum = 0
   	for n in range(h): # replace with a better name #TODO
   		for p in relevant_pair_lists[n]:
   			maximum = max(maximum,gen_height_approx_dictionary[(n,p[0],p[1])])
   	d_tilde = b + t/6 + maximum

