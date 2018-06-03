from sage.rings.all import RR

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

	def sieve_util(Z, primes, bound):
		r"""
		Returns the rational point on subscheme `Z` using the sieve algorithm
		"""
		P = Z.ambient_space()
		N = P.dimension()

		modulo_points = []
		for p in primes:
			ring_modulo_p = Z.change_ring(GF(p))
			# find rational point modulo given primes
			modulo_points.append(ring_modulo_p.rational_points())

		len_modulo_points = [len(_) for _ in modulo_points]
		len_primes = len(primes)
		prod_primes = prod(primes)

		rat_points = set()

		for tupl in xmrange(len_modulo_points):
			point = []
			for k in range(N + 1):
				# list all dimensions of given point using chinese remainder theorem
				point.append( crt([ modulo_points[j][tupl[j]][k].lift() for j in range(len_primes) ], primes) )
			m = point
			for i in range(N + 1):
				w = [0 for _ in range(N+1)]
				w[i] = prod_primes
				m.extend(w)

			M = matrix(ZZ, N+2, N+1, m)
			A = M.LLL()
			point = list(A[1])

			# check if all coordinates of this point satisfy bound

			try:
				rat_points.add(X(list(A[1]))) # checks if this point lies on Z or not
			except:
				pass
		final_points = []
		for point in rat_points:
			bound_satisfied = true
			for coordinate in point:
				if RR(coordinate).abs() > bound:
					bound_satisfied = false
			if bound_satisfied:
				final_points.append(point)


		return list(final_points)

	# start of main algorithm
	N = X.ambient_space().dimension()

	B = (2**(N/4+1)*bound**2*sqrt(N+1)).n()
	p = sufficient_primes(B.ceil())

	return sieve_util(X, p, bound)