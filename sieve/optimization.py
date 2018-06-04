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