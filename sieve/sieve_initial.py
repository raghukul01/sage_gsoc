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

	def good_primes(B, N):
		r"""
		Given the bound returns the prime whose product is greater than B
		and which would yeild most efficient complexity of sieve algorithm
		"""
		# complexity of part 1 is assumed to be N^5*P_max^{N}
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
		best_time = (N**2)*M[2][-1]**(N) + (N**5 * (prod(M[2]) / M[2][-1]).n() )
		for i in range(2, max_length + 1):
			current_time = (N**2)*M[i][-1]**(N) + (N**5 * (prod(M[i])  / M[i][-1]).n() )
			if current_time < best_time:
				best_size = i
				best_time = current_time

		return M[best_size]

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
	primes = good_primes(B.ceil(), N)

	modulo_points = points_modulo_primes(X,primes)
	len_modulo_points = [len(_) for _ in modulo_points]
	len_primes = len(primes)
	prod_primes = prod(primes)

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
			if coordinate.abs() > bound:
				bound_satisfied = false
		if not bound_satisfied:
			continue

		try:
			rat_points.add(X(list(A[1]))) # checks if this point lies on X or not
		except:
			pass

	return sorted(list(rat_points))