from sage.rings.all import RR
from sage.parallel.ncpus import ncpus
from sage.parallel.use_fork import p_iter_fork

def sieve(X, bound=0):
	r"""
	Returns the list of all rational points on given subscheme (`X`).
	#TODO this function only works if dimension of given subscheme > 0
	"""

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
		modulo_points = []
		for pair in points_pair:
		    modulo_points.append(pair[1])

		return modulo_points

	# start of main algorithm

	P = X.ambient_space()
	N = P.dimension()

	# bound as per preposition - 4, in preperiodic points paper
	B = (2**(N/4+1)*bound**2*sqrt(N+1)).n()
	primes = sufficient_primes(B.ceil())

	modulo_points = points_modulo_primes(X,primes)
	len_modulo_points = [len(_) for _ in modulo_points]
	len_primes = len(primes)
	prod_primes = prod(primes)
	bound_log = RR(bound).log()

	rat_points = set()

	# list which stores entries needed to form matrix
	m = [0 for _ in range(N + 1)]

	for i in range(N + 1):
		w = [0 for _ in range(N+1)]
		w[i] = prod_primes
		m.extend(w)

	for tupl in xmrange(len_modulo_points):
		point = []
		for k in range(N + 1):
			# list all dimensions of given point using chinese remainder theorem
			point.append( crt([ modulo_points[j][tupl[j]][k].lift() for j in range(len_primes) ], primes) )
		
		for i in range(N+1):
			m[i] = point[i]

		M = matrix(ZZ, N+2, N+1, m)
		A = M.LLL()
		point = list(A[1])

		# check if all coordinates of this point satisfy bound
		bound_satisfied = true
		for coordinate in point:
			if coordinate.global_height() > bound_log:
				bound_satisfied = false
		if not bound_satisfied:
			continue

		try:
			rat_points.add(X(list(A[1]))) # checks if this point lies on X or not
		except:
			pass

	return sorted(list(rat_points))