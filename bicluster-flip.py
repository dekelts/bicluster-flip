#!/usr/bin/python3
from math import ceil
import sys
import scipy.optimize
import bitarray.util

# compute the branching number of V
def compute(V, init = 10):
	if len(V) <= 1:
		return
	def h(x):
		return sum([x**(-v) for v in V])-1
	return scipy.optimize.brenth(h,1,init)

def compute2(V, D, init = 10):
	def h(x):
		return sum(D[i]/x**V[i] for i in range(len(V)))-1
	return scipy.optimize.brenth(h,1,init)

# compute the branching number if it is less than bn
def compute_conditional(V, bn):
	if sum([bn**(-v) for v in V]) < 1:
		return compute(V)
	else:
		return bn+1000

# check if the branching number of V is below bn
def below_bn(V, bn):
	return sum([bn**(-v) for v in V]) <= 1

def concatenate(L):
	R = []
	for x in L:
		R += x
	return R

def all_sequences2(T):
	n = len(T)
	S = (0,)*n
	yield S
	while 1:
		i = 0
		while i < n and S[i] == T[i]-1:
			i += 1
		if i == n:
			return
		S = (0,)*i+(S[i]+1,)+S[i+1:]
		yield S

def all_sequences2_classes(T, k):
	if k == 0:
		for S in all_sequences2(T):
			yield S,1
	else:
		for S in all_sequences2(T[:-k]):
			for S1,k1 in all_sequences_classes(k, T[-1]):
				yield S+tuple(S1),k1

# Return a list of all strings of length n over the alphabet {0,...,sigma-1}
def all_sequences(n, sigma):
	return all_sequences2([sigma]*n)

# Return all equivalence classes of strings of length n over alphabet sigma,
# where two strings are equivalent if one is a permutation of the other
# For each equivalence class, the procedure returns a pair X,k where
# X is one string from the equivalence class and
# k is the size of the class.
def all_sequences_classes(n, sigma):
	for S in all_partitions(n, [n]*sigma):
		X = concatenate([[i]*S[i] for i in range(sigma)])
		k = fact(n)
		for i in range(sigma):
			k = k//fact(S[i])
		yield X,k

def fact(n):
	return 1 if n <= 1 else n*fact(n-1)

# All orderered partitions of n into |L| parts, where the i-th part is at most L[i] for all i
def all_partitions(n, L, i = 0):
	if i == len(L)-1:
		if n >= 0:
			yield (n,)
		return
	for x in range(min(n,L[i])+1):
		for Y in all_partitions(n-x, L, i+1):
			yield (x,)+Y

def all_permutations(L):
	n = len(L)
	if n == 1:
		yield L
		return
	for X in all_permutations(L[1:]):
		for i in range(n-1,-1,-1):
			yield X[:i]+L[0]+X[i:]

def choose(L, k, n = None):
	if n == None:
		n = len(L)
	if k == 0:
		yield []
		return
	for i in range(k-1,n):
		for S in choose(L, k-1, i):
			yield S+[L[i]]

def all_subsets(L):
	for i in range(1, len(L)+1):
		for x in choose(L, i):
			yield x

def to_bit_vector(A, m):
	A2 = bitarray.util.zeros(m)
	for e in A:
		A2[e] = True
	return A2

def contains_subset(R, A):
	for i in range(min(300,len(R))):
		B = R[i][1]
		if bitarray.util.subset(B, A):
			return True
	return False

def remove_supersets(L, B):
	L = sorted(L, key = lambda x: len(x))

	if type(L[0][0]) != type(0):
		M = {}
		L2 = []
		for A in L:
			for e in A:
				if e not in M:
					M[e] = len(M)
			A2 = [M[e] for e in A]
			L2.append((A,A2))
		m = max(max(A2) for A,A2 in L2)+1
		R = []
		for A,A2 in L2:
			A3 = to_bit_vector(A2, m)
			if not contains_subset(R, A3):
				R.append((A,A3))
		R = [x[0] for x in R]
		return R

	m = max(max(A) for A in L)+1
	R = []
	for A in L:
		A2 = to_bit_vector(A, m)
		if not contains_subset(R, A2):
			R.append((A,A2))
	R = [x[0] for x in R]
	return R

# all non-empty proper subsets of a set from L
def adjust_subsets(L):
	S = set()
	for B in L:
		for B2 in all_subsets(list(B)):
			if 0 < len(B2) < len(B):
				S.add(tuple(B2))
	return list(S)

def adjust(L, Bdict):
	V = [len(x) for x in L]
	if below_bn(V, bmax):
		return L,V

	cache = {}
	V,D = apply_deg1_rule(L, [1]*len(L), Bdict, cache)
	if below_bn(V, bmax):
		return L,V

	if verbose: print("before remove",len(L),compute([len(x) for x in L]))
	L = remove_supersets(L, Bdict)
	if verbose: print("after  remove",len(L),compute([len(x) for x in L]))
	V,D = apply_deg1_rule(L, [1]*len(L), Bdict, cache)
	bn = compute(V)

	flag = True
	i = 1
	while bn > bmax and flag:
		if verbose: print(f"adjust round {i} {bn:.3f}")
		flag = False
		best_bn = bn
		best_L = L
		best_V = V
		for A in adjust_subsets(L):
			As = set(A)
			L2 = [A] + [B for B in L if not As.issubset(B)]
			V2,D = apply_deg1_rule(L2, [1]*len(L2), Bdict, cache)
			bn2 = compute_conditional(V2, best_bn)
			if bn2 < best_bn:
				best_bn = bn2
				best_L = L2
				best_V = V2
		if best_bn < bn:
			bn = best_bn
			L = best_L
			V = best_V
			flag = True
			i += 1
	return L,V

##################################################################################
# Functions for Bicluster Editing

VR = [1,1]

def apply_deg1_rule(V, D, B, cache):
	if not bicluster or sum(D[i]/2.15**len(V[i]) for i in range(len(V))) < 1:
		return [len(x) for x in V],D

	Vertices = [x for x in B.keys() if len(x) == 1]
	# Vertices = the vertices in V1 on which the rule is applied

	if cache != None and "g" in cache:
		Adj = cache["g"]
	else:
		Vertices2 = []
		for x in B.keys():
			Vertices2 += [(x,i) for i in range(B[x])]
		# Vertices2 = the set of all neighbors of vertices in Vertices

		# Create the subgraph G2 induced by Vertices ∪ Vertices2
		Adj = {x:set() for x in Vertices+Vertices2}
		# Adj = adjacency lists of G2
		for p in Vertices2:
			for x in p[0]:
				Adj[x].add(p)
				Adj[p].add(x)
		if cache != None:
			cache["g"] = Adj

	V2 = []
	D2 = []
	for i,F in enumerate(V):
		deg1 = False
		if cache != None and F in cache:
			if cache[F]:
				V2 += [len(F)+x for x in VR]
				D2 += [D[i]]*len(VR)
			else:
				V2.append(len(F))
				D2.append(D[i])
			continue

		# build G2△F
		for e in F:
			p = (e[1],e[2])
			if p in Adj[e[0]]:
				Adj[e[0]].remove(p)
				Adj[p].remove(e[0])
			else:
				Adj[e[0]].add(p)
				Adj[p].add(e[0])

		flag = False
		if check_deg1(Adj, Vertices): # check if degree-1 rules can be applied
			V2 += [len(F)+x for x in VR]
			D2 += [D[i]]*len(VR)
			flag = True
		else:
			V2.append(len(F))
			D2.append(D[i])
		if cache != None:
			cache[F] = flag

		# Revert the changes of F to obtain G2 back
		for e in F:
			p = (e[1],e[2])
			if p in Adj[e[0]]:
				Adj[e[0]].remove(p)
				Adj[p].remove(e[0])
			else:
				Adj[e[0]].add(p)
				Adj[p].add(e[0])

	return V2,D2

# Check if the degree-1 rule can be applied.
# Adj is the adjacency list in the graph G' = G2△F
def check_deg1(Adj, Vertices):
	for u in Vertices:
		if len(Adj[u]) == 1: # if deg_G'(u) = 1
			x = list(Adj[u])[0]	# x is the single neighbor of u
			if x[0] == u:
				return True
				# x is adjacent only to u among the vertices in Vertices (in the original graph G)
				# In this case there is an induced path uxvy.
			elif [v for v in Adj[x] if v != u and len(Adj[v]) > 1] != []:
				return True
				# check if in G' there is a neighbor v of x (where v != u) with deg_G'(v) > 1
	return False

def calc_bn_Habc_bicluster(a, b, c, R_u = 1):
	# a = |N(u)\N(v)|, b = |N(v)\N(u)|, c = |N(u)∩N(v)|
	# R_u = the number of twins of u

	deg_u = a+c
	deg_v = b+c
	assert deg_u > 1 or deg_v > 1

	V = []
	# V is a list of sets of edges
	# Each edge is a triplet (x,y,i), where x is one endpoint of the edge,
	# and (y,i) is the other end of the edge.
	# x is either "u", "v", or "z", where "z" is a twin of "u".
	# When u does not have a twin:
	#	The vertices in N(u)\N(v) are represented by ("u",0), ("u",1), ...
	#	The vertices in N(v)\N(u) are represented by ("v",0), ("v",1), ...
	#	The vertices in N(u)∩N(v) are represented by ("uv",0), ("uv",1), ...
	# when u has a twin:
	#	The vertices in N(u)\N(v) are represented by ("uz",0), ("u",1), ...
	#	The vertices in N(v)\N(u) are represented by ("v",0), ("v",1), ...
	#	The vertices in N(u)∩N(v) are represented by ("uvz",0), ("uvz",1), ...
	# The representation above was used in order to have the following property:
	#   there is an edge in G between x and (y,i) iff the character x appears in the string y

	D = []

	# Check the case that u and v are in different connected component
	u = "uz" if R_u == 2 else "u"
	for S_u,p_u in all_sequences_classes(a, 2):
		# The string S_u determines for vertex (y,i) in N(u)\N(v) whether
		# the edge between u and this vertex is deleted by F, or an edge between v and this vertex is added by F.
		# However, if a string S_u is a permutation of S_u2 then the two strings yield sets F and F2 that
		# generate isomorphic graphs.
		# Therefore, we do not need to enumerate all binary strings of length a.
		# Instead, we can use one representative string from each permutation class.
		for S_v,p_v in all_sequences_classes(b, 2):
			# The string S_v determines for vertex (y,i) in N(v)\N(u) whether
			# the edge between v and this vertex is deleted by F, or an edge between u and this vertex is added by F.

			# Generate the edges of F that are incident on u
			del_u = [("u",  u , i) for i in range(len(S_u)) if S_u[i] == 0]
			add_u = [("u", "v", i) for i in range(len(S_v)) if S_v[i] == 1]
			mod_u = del_u+add_u
			if len(mod_u) > deg_u or (len(mod_u) == deg_u and len(add_u) > 0):
				# If this condition is satisfied, the case corresponds to a set F that is not good
				# so we can skip this case.
				continue
			# Generate the edges of F that are incident on v
			del_v = [("v", "v", i) for i in range(len(S_v)) if S_v[i] == 0]
			add_v = [("v",  u , i) for i in range(len(S_u)) if S_u[i] == 1]
			mod_v = del_v+add_v
			if len(mod_v) > deg_v or (len(mod_v) == deg_v and len(add_v) > 0):
				# If this condition is satisfied, the case corresponds to a set F that is not good
				# so we can skip this case.
				continue
			if R_u == 2:
				mod_u += [("z",x[1],x[2]) for x in mod_u]
			V.append(tuple(mod_u+mod_v))
			D.append(p_u*p_v)

	uv = "uvz" if R_u == 2 else "uv"
	for S,p in all_sequences_classes(c, 2):
		del_u = [("u", uv, i) for i in range(len(S)) if S[i] == 1]
		del_v = [("v", uv, i) for i in range(len(S)) if S[i] == 0]
		if R_u == 2:
			del_u += [("z",x[1],x[2]) for x in del_u]
		V.append(tuple(del_u+del_v))
		D.append(p)

	if R_u == 2:
		# Do not apply the deg-1 rule if there are twins
		return compute2([len(x) for x in V],D)
	else:
		# Create a dictionary B such that B[y] is the number of vertices of the form (y,i)
		B = {"u": a, "v": b, "uv": c}
		if verbose:
			print()
			print(f"before deg1 {compute2([len(x) for x in V],D):.3f}")
			print(strV(V),D)
		V2,D2 = apply_deg1_rule(V,D,B,{})
		if verbose:
			print()
			print(f"after deg1 {compute2(V2,D2):.3f}")
			print(V2,D2)
		return compute2(V2,D2)

def beta(c,d):
	return compute2([c,d],[2**c,2**d])

def Range(a):
	while 1:
		yield a
		a += 1

def calc_L2_bicluster():
	L = []
	L2twins = []
	for c in Range(1):
		if verbose: print("c = ",c,beta(c,1))
		if beta(c,1) <= bmax:
			break
		for d in Range(1):
			if verbose: print("c,d = ",c,d,beta(c,d))
			if beta(c,d) <= bmax:
				break
			for a in range(int(ceil(d/2)), d+1):
				b = d-a
				if c+b == 1:
					# Skip this case since v has degree 1, and this cannot occur since
					# the extended rule is applied when the degree-1 rule cannot be applied
					continue
				print("checking",a,b,c,calc_bn_Habc_bicluster(a,b,c))
				if calc_bn_Habc_bicluster(a,b,c) > bmax:
					L.append((a,b,c))
					if calc_bn_Habc_bicluster(a,b,c,2) > bmax:
						L2twins.append((a,b,c))
					if calc_bn_Habc_bicluster(b,a,c,2) > bmax:
						L2twins.append((b,a,c))

	print("L2twins",L2twins)
	return L

def check_color_monotonicity(S,k):
	k -= 1
	if S[0] != k:
		return False
	for i in range(1, len(S)):
		if S[i] < k-1:
			return False
		k = min(k, S[i])
	if k != 0:
		return False
	return True

def all_colorings(n):
	for k in range(1, n+1):
		for x in all_sequences(n, k):
			if check_color_monotonicity(x,k):
				yield x

def calc_bn_H_bicluster(A):
	B = A_to_B(A)
	B_keys = [y for y in B.keys() if B[y] > 0]
	B_keys.sort(key = lambda x:B[x])
	vertices = sorted([y for y in B.keys() if len(y) == 1])
	n = len(vertices)

	# Try to find A (or A after permuting the vertices) in the cache
	for perm in all_permutations("".join(vertices)):
		Ap = A_permute(A, perm)
		if Ap in Cache:
#			print("cache")
			return 0

	# Compute a list of all pairs of vertices that do not have a common neighbor
	non_intersecting = []
	for j in range(1, len(vertices)):
		for i in range(j):
			if not intersect(B,vertices[i]+vertices[j]):
				non_intersecting.append((i,j))

	X = []
	for coloring in all_colorings(n):
	# Go over all possible way to partition the elements of vertices into subsets
	# (each subset are vertices that are in the same connected component, after applying some optimal solution).
	# The partition is represented by the vector coloring, where coloring[i] is the subset index of vertices[i]
		if [1 for i,j in non_intersecting if coloring[i] == coloring[j]] != []:
		# Check if there are two vertices with no common neighbor that has the same color.
		# If F is good thenthis case does not occur, so we skip it.
			continue

		if verbose >= 2:
			print("\n",coloring)

		coloring_map = {x:coloring[i] for i,x in enumerate(vertices)} # coloring_map[v] is the color of v.
		color_sets = [set(i for i in range(n) if coloring[i] == col) for col in range(n)]
		# color_sets[col] is a set of all indices of elements of coloring that are equal to col
		num_col = [len(x) for x in color_sets]
		# num_col[col] is the number of vertices with color col
		T = []
		data = []
		for y in B_keys:
			y_colors = [coloring_map[x] for x in y] # The colors of vertices in y (y_colors[i] is the color of y[i])
			y_colors_s = set(y_colors) # A set of the different colors that appear in the vertices of y
			y_colors_map = {x:i for i,x in enumerate(y_colors_s)} # map the colors in y_colors_s to the range 0,1,...len(y_colors_s)-1
			S_start = len(T)
			if [col for col in y_colors_s if y_colors.count(col) == num_col[col]] != []:
			# Check if there is a color such that all the vertices with this color are in y
				if len(y_colors_s) == 1:
					case = 1
				else:
					T += [len(y_colors_s)]*B[y]
					case = 3
			else:
				T += [len(y_colors_s)+1]*B[y]
				case = 2
			if case != 1:
				data.append((y,case,S_start,y_colors_map))
		X.append((data,T,coloring_map,y_colors_map))

	if B[B_keys[-1]] <= 4:
		bn,V = calc_bn_H_bicluster2(B, B_keys, X)
	else:
		bn,V = calc_bn_H_bicluster2fast(B, B_keys, X)
		if bn > bmax and B[B_keys[-1]] <= 8:
			bn,V = calc_bn_H_bicluster2(B, B_keys, X)

	Cache[A] = bn
	return bn

def calc_bn_H_bicluster2(B, B_keys, X):
	vertices = sorted([y for y in B.keys() if len(y) == 1])
	Deg = {z:sum(B[y] for y in B_keys if z in y) for z in vertices}
	# Deg[z] = the degree of z.

	V = []
	for data,T,coloring_map,y_colors_map in X:
		for S in all_sequences2(T):
			Del = {z:[] for z in vertices}
			Add = {z:[] for z in vertices}
			Mod = {}
			for y,case,S_start,y_colors_map in data:
				for z in vertices:
					if z in y:
						Del[z] += [(z, y, i) for i in range(B[y]) if S[S_start+i] != y_colors_map[coloring_map[z]] ]
					elif coloring_map[z] in y_colors_map:
					# Check if the color of z is one of the colors that appear in the vertices of y
						Add[z] += [(z, y, i) for i in range(B[y]) if S[S_start+i] == y_colors_map[coloring_map[z]] ]

			flag = False
			for z in vertices:
				Mod[z] = Del[z]+Add[z]
				if len(Mod[z]) > Deg[z] or (len(Mod[z]) == Deg[z] and len(Add[z]) > 0):
					flag = True
					break
			if flag:
				continue
			V.append(tuple(concatenate(Mod[z] for z in vertices)))
			if verbose >= 2: print(S,strV(V[-1:]))

	if verbose:
		print()
		print(f"before adjust {compute([len(x) for x in V]):.3f} {len(V)}")
		print(strV(V))
	V,V2 = adjust(V, B)
	bn = compute(V2)
	if verbose:
		print(f"after adjust {compute([len(x) for x in V]):.3f} {bn:.3f} {len(V)}")
		print(strV(V))
	return bn,V2

def calc_bn_H_bicluster2fast(B, B_keys, X):
	vertices = sorted([y for y in B.keys() if len(y) == 1])
	Deg = {z:sum(B[y] for y in B_keys if z in y) for z in vertices}
	# Deg[z] = the degree of z.

	V = []
	D = []
	X1 = [x for x in X if x[0][-1][0] != B_keys[-1]]
	X2 = [x for x in X if x[0][-1][0] == B_keys[-1]]
	X = X1+X2
	Small_F = []
	for data,T,coloring_map,y_colors_map in X:
		k = 0
		if data[-1][0] == B_keys[-1]:
			k = B[data[-1][0]]
		for S,p in all_sequences2_classes(T,k):
			Del = {z:[] for z in vertices}
			Add = {z:[] for z in vertices}
			Mod = {}
			for y,case,S_start,y_colors_map in data:
				for z in vertices:
					if z in y:
						Del[z] += [(z, y, i) for i in range(B[y]) if S[S_start+i] != y_colors_map[coloring_map[z]] ]
					elif coloring_map[z] in y_colors_map:
					# Check if the color of z is one of the colors that appear in the vertices of y
						Add[z] += [(z, y, i) for i in range(B[y]) if S[S_start+i] == y_colors_map[coloring_map[z]] ]

			flag = False
			for z in vertices:
				Mod[z] = Del[z]+Add[z]
				if len(Mod[z]) > Deg[z] or (len(Mod[z]) == Deg[z] and len(Add[z]) > 0):
					flag = True
					break
			if flag:
				continue

			F = set(concatenate(Mod[z] for z in vertices))
			if [F2 for F2 in Small_F if F2.issubset(F)] != []:
				continue
			V.append(len(F))
			D.append(p)
			if len(F) <= 4 and len(data[-1][0]) != len(vertices):
				Small_F.append(F)

	bn = compute2(V,D)
	return bn,V

##################################################################################
# Functions for Flip Consensus Tree

def calc_bn_Habc_flip(a, b, c):
	deg_u = a+c
	deg_v = c+b

	V = []
	D = []
	for S,p in all_sequences_classes(a, 2):
		del_u = a-sum(S)
		add_v = sum(S)
		if verbose >= 2: print("1?",S,p,f"\t{add_v} >= {deg_v}-1 ?")
		if add_v >= deg_v-1:
			continue
		# We assume that the solution F is f-good: it has at most deg(v)-1 pairs incident on v,
		# and if there are exactly deg(v)-1 such pairs then these pairs are edges in G.
		# If this does not occur we can skip the case.
		# We don't need to check whether del_u >= deg-1 since del_u <= a < a+c = deg_u

		if del_u == deg_u-1:
			continue
		# If this condition is satisfied then c = 1 and del_u = a.
		# We assume that f(u) is one of the vertices in N(u)\N(v), so
		# the set of of selected pairs in this case is not f-good.

		V.append(del_u+add_v)
		D.append(p)
		if verbose: print("1:",S,V[-1],D[-1])

	for S,p in all_sequences_classes(b, 2):
		del_v = b-sum(S)
		add_u = sum(S)
		if verbose >= 2: print("2?",S,p,f"\t{add_u} >= {deg_u}-1 ? {del_v} = {deg_v}-1")
		if add_u >= deg_u-1:
			continue
		if del_v == deg_v-1:
			continue
		V.append(del_v+add_u)
		D.append(p)
		if verbose: print("2:",S,V[-1],D[-1])

	for S,p in all_sequences_classes(c, 2):
		del_u = sum(S)
		del_v = c-del_u
		if verbose >= 2: print("3?",S,p,f"\t{del_u} = {deg_u}-1 ? {del_v} = {deg_v}-1 ?")
		if del_u == deg_u-1 and c > 1:
			continue
		# If this condition is satisfied then a = 1 and del_u = c.
		# since c > 1, we assume that f(u) is one of the vertices in N(u)∩N(v), so
		# the set of of selected pairs in this case is not f-good.
		# (if c = 1 then above we defined f(u) to be one of the vertices in N(u)\N(v))

		if del_v == deg_v-1 and c > 1:
			continue

		V.append(del_u+del_v)
		D.append(p)
		if verbose: print("3:",S,V[-1],D[-1])

	if verbose:
		print(V,D)
	bn = compute2(V,D)
	if verbose >= 2:
		print(f"{ceil(bn*1000)/1000:.3f}", a,b,c,V if len(V) < 20 else [])
	return bn

def gamma(a,b,c):
	return compute2([a,b,c],[2**a,2**b,2**c])

def calc_L2_flip():
	L = []
	for a in Range(1):
		if verbose: print(a,1,1,gamma(a,1,1),calc_bn_Habc_flip(a,1,1))
		if gamma(a,2,1) <= bmax:
			break
		for b in range(1, a+1):
			if a == b == 1:
				continue
			if verbose: print(a,b,1,gamma(a,b,1))
			if gamma(a,b,1) <= bmax:
				break
			for c in Range(1):
				if b == c == 1:
					continue
				if verbose: print(a,b,c,gamma(a,b,c))
				if gamma(a,b,c) <= bmax:
					break
				print("Checking",a,b,c)
				if (bn := calc_bn_Habc_flip(a,b,c)) > bmax:
					L.append((a,b,c))
					print("Added",a,b,c,bn)
	for c in range(2,20):
		L.append((1,1,c))
	return L

def ancestors(parent_array, v):
	R = [v]
	while parent_array[v] != None:
		v = parent_array[v]
		R.append(v)
	return R

def calc_all_arcs(E, vertices):
	L = [[]]
	for edges,X in E:
		for p in all_permutations(vertices):
			if [1 for i,j in X if p[i] > p[j]] != []:
				continue
			edges2 = [(p[e[0]],p[e[1]]) for e in edges]
			L.append(edges2)
	return L

E3 = [	([(1,2)],			[]),
		([(0,2),(1,2)],	[(0,1)]),
		([(0,1),(1,2)],	[])	]

E4 = [	([(2,3)],				[(0,1)]),
		([(1,3),(2,3)],			[(1,2)]),
		([(0,1),(2,3)],			[(0,2)]),
		([(1,2),(2,3)],			[]),
		([(0,3),(1,3),(2,3)],	[(0,1),(1,2)]),
		([(0,1),(1,3),(2,3)],	[]),
		([(0,2),(1,2),(2,3)],	[(0,1)]),
		([(0,1),(1,2),(2,3)],	[]) ]

all_arcs3 = calc_all_arcs(E3, "uvw")
all_arcs4 = calc_all_arcs(E4, "uvwx")

def calc_bn_H_flip(A):
	B = A_to_B(A)
	B_keys = [y for y in B.keys() if B[y] > 0]
	B_keys.sort(key = lambda x:B[x])
	vertices = sorted([y for y in B.keys() if len(y) == 1])
	assert len(vertices) <= 4

	for perm in all_permutations("".join(vertices)):
		Ap = A_permute(A, perm)
		if Ap in Cache:
			return 0

	N = {z:[] for z in vertices}
	for z in vertices:
		for y in B_keys:
			if z in y:
				N[z] += [(z,y,i) for i in range(B[y])]
		if verbose >= 2:
			print(f"f({z}) = {N[z][-1]}")
		N[z] = N[z][:-1]
	# N[z] is a list of all neighbors of z, except one neighbor

	# Compute a list of all pairs of vertices that do not have a common neighbor
	non_intersecting = []
	for j in range(1, len(vertices)):
		for i in range(j):
			if not intersect(B,vertices[i]+vertices[j]):
				non_intersecting.append((i,j))

	all_arcs = all_arcs3 if len(vertices) == 3 else all_arcs4
	X = []
	for arcs in all_arcs:
		parent_array = {v:None for v in vertices}
		for e in arcs:
			parent_array[e[0]] = e[1]
		Ancestors = {v:ancestors(parent_array,v) for v in vertices}
		Ancestors["*"] = []

		if [1 for i,j in non_intersecting if vertices[i] in Ancestors[vertices[j]] or vertices[j] in Ancestors[vertices[i]] ] != []:
		# Check if there are two vertices with no common neighbor such that one is an ancestor of the other.
		# In an f-good set this case does not occur, so we skip it.
			continue

		if verbose >= 2:
			print("\n",arcs)

		T = []
		data = []
		for y in B_keys:
			y2 = [] # y2 are the "important" vertices in y.
			for z in y:
				if [x for x in y if x != z and parent_array[x] == z] == []:
					# z is important if y doesn't contain a child of z
					y2.append(z)

			S_start = len(T)
			if [z for z in y2 if [x for x in Ancestors[z] if x not in y] == [] ] != []:
			# Check if there is a vertex z in y2 such that all the ancestor of z are in y
				if len(y2) == 1:
					case = 1
				else:
					T += [len(y2)]*B[y]
					case = 3
			else:
				T += [len(y2)+1]*B[y]
				y2 += "*"
				case = 2
			if verbose >= 2: print(y,B[y],y2,"case",case)
			if case != 1:
				data.append((y,case,S_start,y2))
		X.append((data,T,Ancestors))

	if B[B_keys[-1]] <= 4:
		bn,V = calc_bn_H_flip2(B, B_keys, N, X)
	else:
		bn,V = calc_bn_H_flip2fast(B, B_keys, N, X)
		if bn > bmax and B[B_keys[-1]] <= 13:
			bn,V = calc_bn_H_flip2(B, B_keys, N, X)

	Cache[A] = bn
	return bn

def calc_bn_H_flip2(B, B_keys, N, X):
	vertices = sorted([y for y in B.keys() if len(y) == 1])
	Deg = {z:sum(B[y] for y in B_keys if z in y) for z in vertices}

	M = {}
	V = []
	for data,T,Ancestors in X:
		for S in all_sequences2(T):
			Del = {z:[] for z in vertices}
			Add = {z:[] for z in vertices}
			Mod = {}
			for y,case,S_start,y2 in data:
				for z in vertices:
					if z in y:
						Del[z] += [(z, y, i) for i in range(B[y]) if z not in Ancestors[y2[S[S_start+i]]] ]
					else:
						Add[z] += [(z, y, i) for i in range(B[y]) if z in Ancestors[y2[S[S_start+i]]] ]

			for z in vertices:
				Mod[z] = Del[z]+Add[z]

			flag = False
			for z in vertices:
				if len(Mod[z]) > Deg[z]-1 or (len(Mod[z]) == Deg[z]-1 and len(Add[z]) > 0):
					flag = True
					if verbose >= 2: print("skip1",z,S,strV([concatenate(Mod[zz] for zz in Mod.keys())]))
					break
				if len(Mod[z]) == Deg[z]-1:
					if Mod[z] != N[z]:
						flag = True
						break
					# Recall that the solution F is good.
					# We assume that if F has deg(v)-1 edges incident on v, then
					# these edges are edges in G, and moreover, these edges are the edges between v and N(v)

			if flag:
				continue

			X = []
			for z in vertices:
				for e in Mod[z]:
					if e not in M:
						M[e] = len(M)
					X.append(M[e])
			V.append(X)
			if verbose >= 2: print(S,strV(V[-1:]))
	if verbose:
		print()
		print(f"before adjust {compute([len(x) for x in V]):.3f} {len(V)}")
		print(strV(V))
	V,V2 = adjust(V, B)
	bn = compute(V2)
	if verbose:
		print(f"after adjust {compute([len(x) for x in V]):.3f} {len(V)}")
		print(strV(V))
	return bn,V2

def calc_bn_H_flip2fast(B, B_keys, N, X):
	vertices = sorted([y for y in B.keys() if len(y) == 1])
	Deg = {z:sum(B[y] for y in B_keys if z in y) for z in vertices}

	V = []
	D = []
	X1 = [x for x in X if x[0][-1][0] != B_keys[-1]]
	X2 = [x for x in X if x[0][-1][0] == B_keys[-1]]
	X = X1+X2
	Small_F = []
	for data,T,Ancestors in X:
		k = 0
		if data[-1][0] == B_keys[-1]:
			k = B[data[-1][0]]
		for S,p in all_sequences2_classes(T,k):
			Del = {z:[] for z in vertices}
			Add = {z:[] for z in vertices}
			Mod = {}
			for y,case,S_start,y2 in data:
				for z in vertices:
					if z in y:
						Del[z] += [(z, y, i) for i in range(B[y]) if z not in Ancestors[y2[S[S_start+i]]] ]
					else:
						Add[z] += [(z, y, i) for i in range(B[y]) if z in Ancestors[y2[S[S_start+i]]] ]

			for z in vertices:
				Mod[z] = Del[z]+Add[z]

			flag = False
			for z in vertices:
				if len(Mod[z]) > Deg[z]-1 or (len(Mod[z]) == Deg[z]-1 and len(Add[z]) > 0):
					flag = True
					break

			if flag:
				continue

			F = set(concatenate(Mod[z] for z in vertices))
			if [F2 for F2 in Small_F if F2.issubset(F)] != []:
				continue
			V.append(len(F))
			D.append(p)
			if len(F) <= 4 and len(data[-1][0]) != len(vertices):
				Small_F.append(F)

	bn = compute2(V,D)
	return bn,V

##################################################################################

def strV(V):
	if type(V[0][0]) == type(0):
		return " ".join("("+",".join(str(x) for x in y)+")" for y in V)
	else:
		return " ".join("("+",".join(f"{x[0]}.{x[1]}.{x[2]}" for x in y)+")" for y in V)

A3_order = [''.join(x) for x in all_subsets("uvw")]
A4_order = [''.join(x) for x in all_subsets("uvwx")]
A5_order = [''.join(x) for x in all_subsets("uvwxy")]
A6_order = [''.join(x) for x in all_subsets("uvwxyz")]

def A_to_B(A):
	A_order = {7:A3_order, 15:A4_order, 31:A5_order, 63:A6_order}[len(A)]
	return {x:A[i] for i,x in enumerate(A_order)}

def B_to_A(B):
	A_order = {7:A3_order, 15:A4_order, 31:A5_order, 63:A6_order}[len(B)]
	return tuple(B[x] for x in A_order)

# Return whether z[0] and z[1] have a common neighbor
def intersect(B, z):
	return sum(B[y] for y in B.keys() if z[0] in y and z[1] in y) != 0

def conflict_bicluster(B, z):
	a,b,c = B_to_A2(B, z)
	return c > 0 and a+b > 0

def conflict_flip(B, z):
	A = B_to_A2(B, z)
	return min(A) > 0

def B_to_A2(B, z):
	a = sum(B[y] for y in B.keys() if z[0] in y and z[1] not in y)
	b = sum(B[y] for y in B.keys() if z[0] not in y and z[1] in y)
	c = sum(B[y] for y in B.keys() if z[0] in y and z[1] in y)
	return (a,b,c)

def B_to_B3(B, z):
	u,v,w = z
	B3 = {}
	B3["u"] = sum(B[y] for y in B.keys() if u in y and v not in y and w not in y)
	B3["v"] = sum(B[y] for y in B.keys() if v in y and u not in y and w not in y)
	B3["w"] = sum(B[y] for y in B.keys() if w in y and u not in y and v not in y)
	B3["uv"] = sum(B[y] for y in B.keys() if u in y and v in y and w not in y)
	B3["uw"] = sum(B[y] for y in B.keys() if u in y and w in y and v not in y)
	B3["vw"] = sum(B[y] for y in B.keys() if v in y and w in y and u not in y)
	B3["uvw"] = sum(B[y] for y in B.keys() if u in y and v in y and w in y)
	return B3

def B_to_B4(B, z):
	u,v,w,x = z
	B4 = {}
	B4["u"] = sum(B[y] for y in B.keys() if u in y and v not in y and w not in y and x not in y)
	B4["v"] = sum(B[y] for y in B.keys() if v in y and u not in y and w not in y and x not in y)
	B4["w"] = sum(B[y] for y in B.keys() if w in y and u not in y and v not in y and x not in y)
	B4["x"] = sum(B[y] for y in B.keys() if x in y and u not in y and v not in y and w not in y)
	B4["uv"] = sum(B[y] for y in B.keys() if u in y and v in y and w not in y and x not in y)
	B4["uw"] = sum(B[y] for y in B.keys() if u in y and w in y and v not in y and x not in y)
	B4["vw"] = sum(B[y] for y in B.keys() if v in y and w in y and u not in y and x not in y)
	B4["ux"] = sum(B[y] for y in B.keys() if u in y and x in y and v not in y and w not in y)
	B4["vx"] = sum(B[y] for y in B.keys() if v in y and x in y and u not in y and w not in y)
	B4["wx"] = sum(B[y] for y in B.keys() if w in y and x in y and u not in y and v not in y)
	B4["uvw"] = sum(B[y] for y in B.keys() if u in y and v in y and w in y and x not in y)
	B4["uvx"] = sum(B[y] for y in B.keys() if u in y and v in y and x in y and w not in y)
	B4["uwx"] = sum(B[y] for y in B.keys() if u in y and w in y and x in y and v not in y)
	B4["vwx"] = sum(B[y] for y in B.keys() if v in y and w in y and x in y and u not in y)
	B4["uvwx"] = sum(B[y] for y in B.keys() if u in y and v in y and w in y and x in y)
	return B4

def A_permute(A, p):
	return B_to_A(B_permute(A_to_B(A), p))

def B_permute(B, perm):
	M = {"u":perm[0], "v":perm[1], "w":perm[2]}
	if len(perm) >= 4:
		M["x"] = perm[3]
	if len(perm) >= 5:
		M["y"] = perm[4]
	return {x:B[''.join(sorted(M[y] for y in x))] for x in B.keys()}

# D is a list of strings (e.g. ["u", "v", "uv"])
# perm is a permutation (e.g. "uwv")
def permute(D, perm):
	M = {"u":perm[0], "v":perm[1], "w":perm[2]}
	if len(perm) >= 4:
		M["x"] = perm[3]
	if len(perm) >= 5:
		M["y"] = perm[4]
	return [''.join(sorted(M[y] for y in x)) for x in D]

def L2_from_Lr(L):
	vertices = sorted([y for y in A_to_B(L[0]).keys() if len(y) == 1])
	L2 = set()
	for A in L:
		B = A_to_B(A)
		for j in range(1, len(vertices)):
			for i in range(len(vertices)-j):
				if conflict(B, vertices[i]+vertices[i+j]):
					A2 = B_to_A2(B, vertices[i]+vertices[i+j])
					L2.add(A2)
	return list(L2)

def check_in_L(L, B, vertices):
	if B_to_A(B) in L:
		return True
	for p in all_permutations(vertices):
		if p != vertices and B_to_A(B_permute(B, p)) in L:
			return True
	return False

def check_in_L3(L, B): return check_in_L(L, B, "uvw")
def check_in_L4(L, B): return check_in_L(L, B, "uvwx")
def check_in_L5(L, B): return check_in_L(L, B, "uvwxy")

def max_degree(B):
	vertices = sorted([y for y in B.keys() if len(y) == 1])
	max_d = 0
	for i in range(len(vertices)):
		d = sum(int(conflict(B, vertices[i]+vertices[j])) for j in range(len(vertices)) if j != i)
		max_d = max(max_d, d)
	return max_d

def configuration_string(B):
	vertices = sorted([y for y in B.keys() if len(y) == 1])
	X = []
	for i in range(len(vertices)-1):
		a,b,c = B_to_A2(B, vertices[i]+vertices[i+1])
		X.append(f"{a}{b}{c}")
	s = "-".join(X)
	if conflict(B, vertices[0]+vertices[-1]):
		a,b,c = B_to_A2(B, vertices[0]+vertices[-1])
		s += f":{a}{b}{c}"
	s += " "
	for j in range(1, len(vertices)):
		for i in range(len(vertices)-j):
			s += str(int(conflict(B, vertices[i]+vertices[i+j])))
	return s

def B2_from_B(B2_base, B):
	B2 = {z:B2_base[z] for z in B2_base.keys()}
	A_order = {3:A3_order, 7:A4_order, 15:A5_order}[len(B)]
	keys = [z for z in A_order if z not in B2]
	x = A_order[-1][-1]
	for z in keys:
		if x in z:
			z2 = ''.join(y for y in z if y != x)
			B2[z] = B[z2]-B2[z2]
		else:
			B2[z] = B[z]-B2[''.join(sorted(z+x))]
	return B2

def calc_L3_case1(A2, a,b,c, L2s):
# If forbid_uw is true then w cannot be adjacent to u
	if A2[1]+A2[2] != a+c:
		# If the degree of v according to A2 is not equal to the degree of v according to a,b,c,
		# we can skip the case
		return []

	B2 = {"u": A2[0], "v": A2[1], "uv": A2[2]}
	L3 = []
	B30 = {}
	for B30["v"],B30["uv"] in all_partitions(a, [B2["v"], B2["uv"]]):
		for B30["w"],B30["uw"] in all_partitions(b, [99, B2["u"]]):
			B3 = B2_from_B(B30, B2)
			A3 = B_to_A(B3)
			if min(A3) < 0:
				continue

			# check that the configuration of v,w is a,b,c
			if B_to_A2(B3, "vw") != (a,b,c):
				continue

			# check that the configuration of u,v is A2
			if B_to_A2(B3, "uv") != A2:
				continue

#			print("??",configuration_string(B3),B3,A2,(a,b,c),B_to_A(B3))

			A = B_to_A2(B3, "uw")
			if A[0] == A[1] == 0:
				# check that u,w are twins
				continue

			if conflict(B3, "uw"):
				# If u,w are in conflict, check that the configuration of u,w is in L2
				if A not in L2s:
					continue

			if not bicluster and A2[0] == A2[1] == 1 and a == b == 1:
				L3.append(A3)
				print("Added",configuration_string(B3),B3)

			else:
				print("Checking",configuration_string(B3),B3,B_to_A(B3))
				if (bn := calc_bn_H(A3)) > bmax:
					# If an equivalent configuration was already processed then calc_bn_H returns 0
					# so A3 will not be added to L3
					L3.append(A3)
					print("Added",configuration_string(B3),B3,bn)
	return L3

def L2_to_L2star(L2):
	L2s = []
	for A in L2:
		L2s.append(A)
		if A[0] != A[1]:
			L2s.append((A[1],A[0],A[2]))
	return L2s

def calc_L3(L2):
	# Generate L3.
	L2s = L2_to_L2star(L2)
	L3 = []
	for A in L2s:
		for a,b,c in L2s:
			L3 += calc_L3_case1(A, a,b,c, L2s)

	return L3

# Check whether 3 vertices induces a connected subgraph
def connected3(Ebot, x):
	return Ebot[x[0]+x[1]]+Ebot[x[0]+x[2]]+Ebot[x[1]+x[2]] >= 2

def calc_L4_case1(A3, a,b,c, L3):
	L4 = []
	B3 = A_to_B(A3)
#	print("#", A3, a,b,c)
	B40 = {}
	for B40["w"],B40["uw"],B40["vw"],B40["uvw"] in all_partitions(a, [B3["w"],B3["uw"],B3["vw"],B3["uvw"]]):
		for B40["x"],B40["ux"],B40["vx"],B40["uvx"] in all_partitions(b, [99,B3["u"],B3["v"],B3["uv"]]):
			B4 = B2_from_B(B40, B3)
			A4 = B_to_A(B4)
			if min(A4) < 0:
				continue

			# check that the configuration of w,x is a,b,c
			if B_to_A2(B4, "wx") != (a,b,c):
				continue

			# check that the configuration of u,v,w is A3
			if B_to_A(B_to_B3(B4, "uvw")) != A3:
				continue

			Pairs = [''.join(x) for x in choose("uvwx", 2)]
			Ebot = {x:int(conflict(B4, x)) for x in Pairs}

			if connected3(Ebot, "vwx") and not check_in_L3(L3, B_to_B3(B4, "vwx")):
				continue
			if connected3(Ebot, "uvx") and not check_in_L3(L3, B_to_B3(B4, "uvx")):
				continue
			if connected3(Ebot, "uwx") and not check_in_L3(L3, B_to_B3(B4, "uwx")):
				continue

			print("Checking",configuration_string(B4),B4,sum(A4))
			if (bn := calc_bn_H(A4)) > bmax:
				L4.append(A4)
				print("Added",configuration_string(B4),B4,bn)

	return L4

def calc_L4(L3):
	L2s = L2_to_L2star(L2_from_Lr(L3))
	L3set = set(L3)
	L4 = []
	for A in L3:
		for a,b,c in L2s:
			L4 += calc_L4_case1(A, a,b,c, L3set)

			A2 = A_permute(A, "wvu")
			if A2 != A:
				L4 += calc_L4_case1(A2, a,b,c, L3set)

			A2 = A_permute(A, "uwv")
			if A2 != A:
				L4 += calc_L4_case1(A2, a,b,c, L3set)

	return L4

# Check whether 4 vertices induces a connected subgraph
def connected4(Ebot, x):
	e = sum(Ebot[x[i]+x[j]] for i,j in choose([0,1,2,3],2))
	if e <= 2: return False
	if e >= 4: return True
	if Ebot[x[0]+x[1]]+Ebot[x[0]+x[2]]+Ebot[x[0]+x[3]] == 0: return False
	if Ebot[x[0]+x[1]]+Ebot[x[1]+x[2]]+Ebot[x[1]+x[3]] == 0: return False
	if Ebot[x[0]+x[2]]+Ebot[x[1]+x[2]]+Ebot[x[2]+x[3]] == 0: return False
	if Ebot[x[0]+x[3]]+Ebot[x[1]+x[3]]+Ebot[x[2]+x[3]] == 0: return False
	return True

def calc_L5_case1(A4, a,b,c, L4):
	L5 = []
	B4 = A_to_B(A4)
#	print("#", A4, a,b,c)
	B50 = {}
	for B50["x"],B50["ux"],B50["vx"],B50["wx"],B50["uvx"],B50["uwx"],B50["vwx"],B50["uvwx"] in all_partitions(a, [B4["x"],B4["ux"],B4["vx"],B4["wx"],B4["uvx"],B4["uwx"],B4["vwx"],B4["uvwx"]]):
		for B50["y"],B50["uy"],B50["vy"],B50["wy"],B50["uvy"],B50["uwy"],B50["vwy"],B50["uvwy"] in all_partitions(b, [99,B4["u"],B4["v"],B4["w"],B4["uv"],B4["uw"],B4["vw"],B4["uvw"]]):
			B5 = B2_from_B(B50, B4)
			A5 = B_to_A(B5)
			if min(A5) < 0:
				continue

			# check that the configuration of x,y is a,b,c
			if B_to_A2(B5, "xy") != (a,b,c):
				continue

			# check that the configuration of u,v,w,x is A4
			if B_to_A(B_to_B4(B5, "uvwx")) != A4:
				continue

			# We are not interested in the graphs H in L5 such that H_bot has maximum degree at least 3.
			# Therefore, such graphs are skipped
			if bicluster and max_degree(B5) == 2:
				continue

			Pairs = [''.join(x) for x in choose("uvwxy", 2)]
			Ebot = {x:int(conflict(B5, x)) for x in Pairs}

			if connected4(Ebot, "vwxy") and not check_in_L4(L4, B_to_B4(B5, "vwxy")):
				continue
			if connected4(Ebot, "uvwy") and not check_in_L4(L4, B_to_B4(B5, "uvwy")):
				continue
			if connected4(Ebot, "uvxy") and not check_in_L4(L4, B_to_B4(B5, "uvxy")):
				continue
			if connected4(Ebot, "uwxy") and not check_in_L4(L4, B_to_B4(B5, "uwxy")):
				continue

			print("Checking",configuration_string(B5),B5,sum(A5))
			bn = calc_bn_H(A5)
			if bn > bmax:
				L5.append(A5)
				print("Added",configuration_string(B5),B5,bn)

	return L5

def calc_L5(L4):
	L2s = L2_to_L2star(L2_from_Lr(L4))
	L4set = set(L4)

	L5 = []
	for A in L4:
		for a,b,c in L2s:
			L5 += calc_L5_case1(A, a,b,c, L4set)

			A2 = A_permute(A, "xwvu")
			if A2 != A:
				L5 += calc_L5_case1(A2, a,b,c, L4set)

			A2 = A_permute(A, "uvxw")
			if A2 != A:
				L5 += calc_L5_case1(A2, a,b,c, L4set)

			A2 = A_permute(A, "uxwv")
			if A2 != A:
				L5 += calc_L5_case1(A2, a,b,c, L4set)

	return L5

def calc():
	L2 = calc_L2()
	print("L2:",L2)
	if rmax == 2: return

	print("generating L3")
	L3 = calc_L3(L2)
	print("L3:",L3)
	if rmax == 3 or L3 == []: return

	print("generating L4")
	L4 = calc_L4(L3)
	print("L4:",L4)
	if L4 != []: print("max degree:", max(max_degree(A_to_B(A)) for A in L4))
	if rmax == 4 or L4 == []: return

	print("generating L5")
	L5 = calc_L5(L4)
	print("L5:",L5)
	if L5 != []: print("max degree:", max(max_degree(A_to_B(A)) for A in L5))

Cache = {}

bicluster = True
rmax = 5
bmax = 2.22
verbose = 0

calc_L2 = calc_L2_bicluster
calc_bn_H = calc_bn_H_bicluster
conflict = conflict_bicluster

args = []
for x in sys.argv[1:]:
	if x == "-f":
		bicluster = False
		bmax = 3.24
	elif x == "-v":
		verbose = 1
	elif x == "-vv":
		verbose = 2
	elif x[0] == "-":
		rmax = int(x[1:])
	elif x[0] == "+":
		bmax = float(x[1:])
	else:
		args.append(x)

if len(args) == 1:
	bmax = float(args[0])

if not bicluster:
	calc_L2 = calc_L2_flip
	calc_bn_H = calc_bn_H_flip
	conflict = conflict_flip

calc()
