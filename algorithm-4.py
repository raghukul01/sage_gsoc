def bdd_height(K, height_bound, tolerance=1e-5):
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

	def rational_in(x,y):
		r"""
		Computes a rational number q, such that x<q<y using Archimedes' axiom
		"""
		n = (1/(y-x)).ceil() + 1
		if (n*y).ceil() is n*y:
			m = n*y - 1
		else:
			m = (n*y).floor()
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

	# ignore if not needed
	# def lambda(x,K):
	# 	r"""
	# 	Computes an (r+1)-tuple of absolute values of x under
	# 	different embeddings of K into RR and CC
	# 	"""


	# start of main algorithm
	O_K = K.ring_of_integers()
	r1, r2 = K.signature(); r = r1 + r2 -1
	fund_units = UnitGroup(K).fundamental_units()

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
