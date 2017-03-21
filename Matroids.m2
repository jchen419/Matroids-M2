needsPackage "Graphs"
newPackage("Matroids",
	Headline => "Matroids",
	Version => "0.2",
	Date => "July 1, 2015",
	Authors => {{Name => "Justin Chen"}},
	DebuggingMode => true
)
export {
	"Matroid",
	"matroid",
		"EntryMethod",
		"TargetRank",
	"isValid",
	"ground",
	"groundSet",
	"indicesOf",
	"bases",
	"nonbases",
	"circuits",
	"fundamentalCircuit",
	"loops",
	"coloops",
	"independents",
	"isDependent",
	"rk",
	"closure",
	"flats",
	"hyperplanes",
	"fvector",
	"dualMatroid",
	"restriction",
	"deletion",
	"contraction",
	"minor",
	"hasMinor",
	"directsum",
	"componentsOf",
	"representationOf",
	"isRepresentable",
	"isomorphic",
	"tuttePolynomial",
	"tutte2",
	"tutteEvaluate",
	"chromaticPolynomial",
	"characteristicPolynomial",
	"uniformMatroid",
	"getCycles",
	"getClosedWalks",
	"graphCircuits",
	"matroidPolytope",
	"greedyAlgorithm",
	"idealCohomologyRing",
	"cogeneratorCohRing",
	"specificMatroids"
}
needsPackage "Graphs"

hasAttribute = value Core#"private dictionary"#"hasAttribute"
getAttribute = value Core#"private dictionary"#"getAttribute"
ReverseDictionary = value Core#"private dictionary"#"ReverseDictionary"

Matroid = new Type of HashTable

globalAssignment Matroid
net Matroid := X -> (
	if hasAttribute(X, ReverseDictionary) then toString getAttribute(X, ReverseDictionary)
	else "Matroid"
)

Matroid == Matroid := (M, M') -> set bases M === set bases M' and M.ground === M'.ground

matroid = method(Options => {symbol EntryMethod => "bases", symbol TargetRank => -1})
matroid (List, List) := Matroid => opts -> (E, B) -> (
	if #B > 0 and not instance(B#0, Set) then B = B/(l -> set l);
	r := if opts.TargetRank >= 0 then opts.TargetRank else if #B > 0 then #(B#0) else -1;
	E' := set(0..<#E);
	N := {};
	B' := if opts.EntryMethod == "nonbases" then ( 
		if r < 0 then error "Target rank needs to be specified" else toList(set subsets(E', r) - B)
	) else if opts.EntryMethod == "bases" then (
		if #B == 0 then error "There must be at least one basis element" else B
	) else if opts.EntryMethod == "circuits" then (
		if #B == 0 then {E'}
		else (
			(N, r) = nonbasesFromCircuits(B, #E, TargetRank => opts.TargetRank);
			toList(set subsets(E', r) - N)
		)
	);
	M := new Matroid from {
		symbol ground => E',
		symbol groundSet => E,
		symbol bases => B',
		cache => new CacheTable
	};
	if opts.EntryMethod == "circuits" then (
		M.cache.circuits = B;
		M.cache.nonbases = N;
	) else if opts.EntryMethod == "nonbases" then M.cache.nonbases = B;
	M
)
matroid List := Matroid => opts -> B -> (
	if opts.EntryMethod == "nonbases" then error "You must specify a ground set when using 'EntryMethod => \"nonbases\"'.";
	matroid(unique flatten B, B)
)
matroid Matrix := Matroid => opts -> A -> (
	E := entries transpose A/(v -> transpose matrix{v});
	k := rank A;
	B := {};
	for s in subsets(#E, k) do (
		if (rank(A_s) == k) then B = join(B, {s});
	);
	matroid(E, B)
)
matroid Graph := Matroid => opts -> G -> (
	E := edgesAddLoops G;
	matroid(E, graphCircuits G/(c -> indicesOf(E, c)), EntryMethod => "circuits", TargetRank => #(vertices G) - numberOfComponents G)
)

isValid = method()
isValid Matroid := Boolean => M -> (
	if #(bases M) == 0 then return false;
	if rk M > #(M.ground)/2 then return isValid dualMatroid M;
	checkValid := false;
	for A in bases M do (
		for B in bases M do (
			for a in toList(A - B) do (
				checkValid = false;
				for b in toList(B - A) do (
					if member(A - set{a} + set{b}, bases M) then (
						checkValid = true;
						break;
					);
				);
				if checkValid == false then return false;
			);
		);
	);
	true
)

groundSet = method()
groundSet Matroid := List => M -> M.groundSet
groundSet (Matroid, List) := List => (M, S) -> (M.groundSet)_S
groundSet (Matroid, Set) := List => (M, S) -> (M.groundSet)_(toList S)

indicesOf = method()
indicesOf (List, List) := List => (E, F) -> F/(f -> position(E, e -> (e === f)))
indicesOf (Matroid, List) := List => (M, F) -> indicesOf(groundSet M, F)
indicesOf (Matroid, Set) := List => (M, F) -> indicesOf(groundSet M, toList F)

bases = method()
bases Matroid := List => M -> M.bases

nonbases = method()
nonbases Matroid := List => M -> (
	if not M.cache.?nonbases then (
		M.cache.nonbases = toList(set subsets(M.ground, rk M) - M.bases)
	);
	M.cache.nonbases
)

nonbasesFromCircuits = method(Options => {symbol TargetRank => -1})
nonbasesFromCircuits (List, ZZ) := (List, ZZ) => opts -> (C, n) -> (
	E := set(0..<n);
	t := if opts.TargetRank >= 0 then opts.TargetRank + 1 else max(C/(c -> #c));
	N := toList set flatten((select(C, c -> #c < t))/(c -> subsets(E - c, t - 1 - #c)/(s -> c + s)));
	if opts.TargetRank >= 0 then return (N, opts.TargetRank);
	D := toList set flatten(N/(c -> subsets(E - c, 1)/(s -> c + s)));
	Cmax := select(C, c -> #c == t);
	if #D + #Cmax == binomial(#E, t) then return (N, t-1) else N = join(D, Cmax);
	for i from t+1 to #E do (
		D = toList set flatten(N/(c -> subsets(E - c, 1)/(s -> c + s)));
		if #D == binomial(#E, i) then return (N, i-1) else N = D;
	)
)

circuits = method()
circuits Matroid := List => M -> (
	if not M.cache.?circuits then (
		E' := set flatten(bases M/(b -> toList b));
		t := rk M - 1;
		dependents := minimals(select(nonbases M, b -> isSubset(b, E')), subsets(E', t + 2));
		newDependents := {};
		for i from 0 to t - 2 do (
			newDependents = (set subsets(E', t-i)) - independents(M, t-i);
			if #newDependents == 0 then break;
			dependents = minimals(toList newDependents, dependents);
		);
		M.cache.circuits = join(dependents, subsets(set loops M, 1));
	);
	M.cache.circuits
)

fundamentalCircuit = method()
fundamentalCircuit (Matroid, List, ZZ) := List => (M, B, e) -> (
	if member(e, B) then error "The element e cannot be in the basis B.";
	select(circuits M, c -> isSubset(c, append(B, e)))
)
fundamentalCircuit (Matroid, Set, ZZ) := List => (M, B, e) -> fundamentalCircuit(M, toList B, e)

loops = method()
loops Matroid := List => M -> toList(M.ground - flatten(bases M/(b -> toList b)))

coloops = method()
coloops Matroid := List => M -> loops dualMatroid M

minimals = method()
minimals (List, List) := List => (L, L') -> join(L, select(L', b -> not any(L, a -> isSubset(a, b))))

independents = method()
independents (Matroid, ZZ) := List => (M, r) -> unique flatten(bases M/(b -> subsets(b, r)))

isDependent = method()
isDependent (Matroid, Set) := Boolean => (M, S) -> (
	if #S > rk M then return true;
	not any(bases M, b -> isSubset(S, b))
)
isDependent (Matroid, List) := Boolean => (M, S) -> isDependent_M set S

rkFromCircuitsAlg = method()
rkFromCircuitsAlg Matroid := ZZ => M -> (
	local x;
	x = symbol x;
	C := circuits M;
	n := #M.ground;
	R := QQ[x_0..x_(n-1)];
	ind := toList(0..<n);
	I := monomialIdeal(C/(c -> R_(ind/(i -> if member(i, keys c) then 1 else 0))));
	time pdim module dual I
)

rk = method()
rk Matroid := ZZ => M -> #(M.bases#0)
rk (Matroid, List) := ZZ => (M, S) -> rk(M, set S)
rk (Matroid, Set) := ZZ => (M, S) -> (
	currentRank := 0;
	maxRank := min(#S, rk M);
	for b in bases M do (
		currentRank = max(currentRank, #(b*S));
		if currentRank == maxRank then return currentRank;
	);
	currentRank
)

closure = method(Options => {symbol TargetRank => -1})
closure (Matroid, List) := List => opts -> (M, A) -> toList closure(M, set A)
closure (Matroid, Set) := Set => opts -> (M, A) -> (
	r := if opts.TargetRank >= 0 then opts.TargetRank else rk(M, A);
	if r == rk M then return M.ground;
	limits := set{};
	for a in toList(M.ground - A) do (
		if r == rk(M, A + set{a}) then limits = limits + set{a};
	);
	A + limits
)

flats = method()
flats (Matroid, ZZ) := List => (M, r) -> ( -- returns flats of rank r
	if r > rk M or r < 0 then return {};
	if r == rk M then return {M.ground};
	if r == 0 then return {set loops M};
	toList set (select(subsets(M.ground, r), s -> rk_M s == r)/(s -> closure(M, s, TargetRank => r)))
)
flats Matroid := List => M -> join(toList(0..rk M-2)/(i -> flats(M, i)), {hyperplanes M, {M.ground}})

hyperplanes = method()
hyperplanes Matroid := List => M -> (circuits dualMatroid M)/(c -> M.ground - c)

fvector = method()
fvector Matroid := List => M -> flats M/(f -> #f)

dualMatroid = method()
dualMatroid Matroid := Matroid => M -> matroid(groundSet M, (bases M)/(b -> M.ground - b))

restriction = method()
restriction (Matroid, Set) := Matroid => (M, S) -> (
	newrank := rk_M S;
	newbases := unique select((bases M)/(b -> S*b), b -> #b == newrank); S = toList S;
	matroid(groundSet_M S, newbases/(b -> indicesOf(S, toList b)))
)
restriction (Matroid, List) := Matroid => (M, S) -> restriction(M, set S)

deletion = method()
deletion (Matroid, Set) := Matroid => (M, S) -> restriction(M, M.ground - S)
deletion (Matroid, List) := Matroid => (M, S) -> deletion(M, set S)

contraction = method()
contraction (Matroid, Set) := Matroid => (M, S) -> if #S == 0 then M else dualMatroid(deletion(dualMatroid M, S))
contraction (Matroid, List) := Matroid => (M, S) -> contraction(M, set S)

minor = method()
minor (Matroid, List, List) := Matroid => (M, X, Y) -> deletion(contraction(M, X), Y/(y -> y - #select(X, x -> x < y)))
minor (Matroid, Set, Set) := Matroid => (M, X, Y) -> minor(M, toList X, toList Y)

hasMinor = method()
hasMinor (Matroid, Matroid) := Boolean => (M, N) -> (
	n := #N.ground;
	m := #M.ground;
	if n > m or #bases N > #bases M then return false;
	for X in independents(M, rk M - rk N) do (
		MX := contraction_M X;
		for Y in independents(dualMatroid MX, m - n - rk M + rk N) do (
			if isomorphic(N, deletion(MX, Y)) then (
				print("Contract "|toString X|", delete "|toString (Y/(y -> y + #select(toList X, x -> x < y))));
				return true;
			);
		);
	);
	false
)

directsum = method()
directsum (Matroid, Matroid) := Matroid => (M, M') -> (
	n := #M.ground;
	B' := bases M'/(b -> set((toList b)/(i -> i + n)));
	E1 := groundSet M/(e -> (e, 0));
	E2 := groundSet M'/(e -> (e, 1));
	matroid(join(E1, E2), unique flatten(bases M/(b -> B'/(b' -> b' + b))))
)

componentsOf = method()
componentsOf (List, List) := List => (S, C) -> (
	if #S == 0 then return {}
	else if #(set S*set flatten(C/(c -> toList c))) == 0 then return subsets(S, 1);
	comp0 := select(S, s -> any(C, c -> isSubset(set{s, S#0}, c)));
	C = select(C, c -> #(c*set comp0) == 0);
	join({comp0}, componentsOf(toList(set S - comp0), C))
)
componentsOf Matroid := List => M -> (
	singles := join(loops M, coloops M);
	join(subsets(singles, 1), componentsOf(toList(M.ground - singles), circuits M))/restriction_M
)

representationOf = method()
representationOf Matroid := Thing => M -> (
	if instance(M.groundSet#0, Matrix) then return transpose matrix((groundSet M)/(v -> flatten entries v))
	else if all(groundSet M, c -> instance(c, Set) and #c <= 2) then (
		return graph(join(groundSet M, (flatten(select(groundSet M, c -> #c == 1)/toList))/(v -> {v,v})))
	) else print "No representation found.";
)

isRepresentable = method() -- Determines if M is representable over a finite extension of k
isRepresentable (Matroid, Ring) := Boolean => (M, k) -> (
	r := rk M;
	b := #bases M;
	n := #M.ground;
	x := symbol x, y := symbol y;
	S := k[x_{1,1}..x_{r,n},y_1..y_b];
	A := genericMatrix(S, r, n);
	I := ideal(0_S);
	for N in nonbases M do I = I + ideal(det A_(toList N));
	for i from 1 to b do I = I + ideal(y_i*det A_(toList((bases M)#(i-1))) - 1);
	not 1_S % I == 0_S
)

isomorphic = method() -- Looks for permutation inducing bijection on smallest of bases/nonbases/circuits, if precomputed
isomorphic (Matroid, Matroid) := Boolean => (M, M') -> (
	r := rk M;
	b := #bases M;
	e := #M.ground;
	if not (r == rk M' and b == #bases M' and e == #M'.ground) then return false;
	if M == M' then ( print "Isomorphism: matroids are equal"; return true );
	local A, local A';
	n := binomial(e, r) - b;
	if M.cache.?circuits and #circuits M < min(b, n) then ( A = circuits M; A' = circuits M' ) 
	else if n < b then ( A = nonbases M; A' = nonbases M' ) 
	else ( A = bases M, A' = bases M' );
	if #A <= 1 then ( print "Isomorphism: at most 1 basis/nonbasis/circuit"; return true );
	validPerm := true;
	for p in permutations e do (
		validPerm = true;
		for a in A do (
			if not member(a/(i -> p#i), A') then (
				validPerm = false;
				break;
			);
		);
		if validPerm == true then ( print("Isomorphism: "|toString p); return true );
	);
	false
)

tuttePolynomial = method() -- Computes using deletion-contraction recurrence (fast)
tuttePolynomial (Matroid, Ring) := RingElement => (M, R) -> (
	a := coloops M;
	b := loops M;
	if #a + #b == #M.ground then return R_0^#a*R_1^#b
	else (
		c := {(toList(M.ground - a - b))#0};
		return tuttePolynomial(deletion_M c, R) + tuttePolynomial(contraction_M c, R)
	)
)
tuttePolynomial Matroid := RingElement => M -> (
	if not M.cache.?tuttePolynomial then (
		M.cache.tuttePolynomial = tuttePolynomial(M, ZZ(monoid[getSymbol "x", getSymbol "y"]));
	);
	M.cache.tuttePolynomial
)

tutte2 = method() -- Non-recursive computation, computing ranks of all subsets of ground set (slow)
tutte2 Matroid := RingElement => M -> (
	R := ZZ(monoid[getSymbol "x", getSymbol "y"]);
	r := rk M;
	sum(subsets(M.ground)/(S -> (R_0-1_R)^(r - rk_M S)*(R_1-1_R)^(#S - rk_M S)))
)

tutteEvaluate = method()
tutteEvaluate (Matroid, Thing, Thing) := Thing => (M, a, b) -> (
	T := tuttePolynomial M;
	sub(T, {(ring T)_0 => a, (ring T)_1 => b})
)

characteristicPolynomial = method()
characteristicPolynomial Matroid := RingElement => M -> (
	T := tuttePolynomial M;
	(-1)^(rk M)*sub(T, {(ring T)_0 => 1 - (ring T)_0, (ring T)_1 => 0})
)

chromaticPolynomial = method()
chromaticPolynomial (Graph, Ring) := RingElement => (G, R) -> (
	k := #connectedComponents G;
	return (-1)^(#vertices G - k)*(R_0)^k*sub(tuttePolynomial(matroid G, R), {R_0 => 1 - R_0, R_1 => 0})
)
chromaticPolynomial Graph := RingElement => G -> chromaticPolynomial(G, ZZ(monoid[getSymbol "x", getSymbol "y"]))

uniformMatroid = method()
uniformMatroid (ZZ, ZZ) := Matroid => (k, n) -> (
	if k > n or k < 0 then error(toString k | " is not an integer between 0 and " | toString n);
	matroid(toList (0..<n), subsets(n, k), EntryMethod => "bases")
)

getCycles = method()
getCycles Graph := List => G -> (
	if not isConnected G then return flatten((connectedComponents G)/(c -> getCycles inducedSubgraph(G, c)));
	if #edges G < #vertices G then return {}; -- G is a tree
	possibleVertices := select(vertices G, v -> #neighbors(G, v) > 1);
	if #possibleVertices < #vertices G then G = inducedSubgraph(G, possibleVertices);
	if all(vertices G, v -> #neighbors(G,v) == 2) then return {append(vertices G, (vertices G)#0)}; -- G is a cycle
	cycles := {};
	while #vertices G > 2 do (
		cycles = join(cycles, select(getClosedWalks(G, (vertices G)#0, #vertices G), p -> p#1 < p#(#p - 2)));
		G = deleteVertices(G, {(vertices G)#0});
	);
	cycles
)

getClosedWalks = method()
getClosedWalks (Graph, Thing, ZZ) := List => (G, v, l) -> ( -- Returns walks at v of length <= l
	N := toList(neighbors(G, v));
	paths := N/(n -> {v, n});
	walks := {};
	for i from 2 to l - 1 do (
		paths = flatten(paths/(p -> (toList(neighbors(G, last p) - set{v} - set p))/(n -> append(p, n))));
		walks = join(walks, (select(paths, p -> member(last p, N)))/(w -> append(w, v)));
	);
	walks
)

cycleEdges = method()
cycleEdges List := List => C -> ( 
	cycle := {};
	for i from 0 to #C-2 do cycle = append(cycle, set {C#i, C#(i+1)});
	cycle
)

edgesAddLoops = method()
edgesAddLoops Graph := List => G -> join(edges G, select(vertices G, v -> member(v, neighbors(G, v)))/(v -> set{v}))

graphCircuits = method()
graphCircuits Graph := List => G -> (
	loops := select(vertices G, v -> member(v, neighbors(G, v)));
	join(loops/(v -> {set{v}}), (getCycles G)/(c -> cycleEdges c))
)

matroidPolytope = method()
matroidPolytope Matroid := Matrix => M -> (
	initVector := toList M.ground;
	transpose matrix(bases M/(b -> initVector/(i -> if member(i, b) then 1 else 0)))
)

greedyAlgorithm = method()
greedyAlgorithm (Matroid, List) := List => (M, w) -> (
	maxWeightSol := {};
	local candidates, local maxWeight;
	while not member(set maxWeightSol, bases M) do (
		candidates = select(toList(M.ground - maxWeightSol), c -> not isDependent_M(append(maxWeightSol, c)));
		maxWeight = max(candidates/(c -> w#c));
		maxWeightSol = append(maxWeightSol, (select(candidates, c -> w#c == maxWeight))#0);
	);
	maxWeightSol
)

idealCohomologyRing = method()
idealCohomologyRing Matroid := Ideal => M -> (
	x := symbol x;
	F := delete({}, delete(toList M.ground, (flatten flats M)/(f -> toList f)));
	R := QQ[x_1..x_#F];
	incomparablePairs := select(subsets(toList(0..<#F), 2), s -> not isSubset(F#(s#0), F#(s#1)));
	I2 := ideal(incomparablePairs/(pair -> R_(pair#0)*R_(pair#1)));
	linearPairs := subsets(#M.ground, 2)/(s -> {select(F, f -> member(s#0, f)), select(F, f -> member(s#1,f))});
	I1 := ideal(linearPairs/(pair -> sum(indicesOf(F,pair#0)/(i -> R_i)) - sum(indicesOf(F,pair#1)/(i -> R_i))));
	I1 + I2
)

--needsPackage "Dmodules"
cogeneratorCohRing = method()
cogeneratorCohRing Matroid := RingElement => M -> (
	t := symbol t;
	I := trim idealCohomologyRing M;
	L := toList(1..#(gens ring I));
	print("Computed defining ideal in " | #L | " variables.");
	W := (ring I)[L/(i -> t_i)];
	p := value last factor((sum(L/(i -> t_i*(gens ring I)_(i-1))))^(rk M - 1) % (map(W, ring I))(I));
	(map(QQ[gens ring p], ring p)) p
	{*W := QQ[join(L/(i -> t_i), L/(i -> x_i)), WeylAlgebra => L/(i -> t_i => x_i)];
	phi := map(W, ring I, L/(i -> x_i));
	time last PolySols phi I*}
)

specificMatroids = method()
specificMatroids String := Matroid => name -> (
	if name == "fano" then return (
		matroid(toList (1..7), {{0,1,2},{0,4,5},{0,3,6},{1,3,5},{1,4,6},{2,3,4},{2,5,6}}, EntryMethod => "nonbases")
	) else if name == "nonfano" then return (
		matroid(toList (1..7), {{0,1,2},{0,4,5},{0,3,6},{1,4,6},{2,3,4},{2,5,6}}, EntryMethod => "nonbases")
	) else if name == "vamos" then return (
		matroid(toList (1..8), {{0,1,2,3},{0,1,4,5},{2,3,4,5},{2,3,6,7},{4,5,6,7}}, EntryMethod => "nonbases")
	) else if name == "nonpappus" then return (
		matroid(toList (1..9), {{0,1,2},{6,7,8},{0,3,7},{0,4,8},{1,3,6},{1,5,8},{2,4,6},{2,5,7}}, EntryMethod => "nonbases")
	);
)

beginDocumentation()

---Documentation---
--<<docTemplate
doc ///
	Key
		Matroids
	Headline
		a package for computations with matroids
	Description
		Text
			A matroid is a combinatorial structure abstracting the notion of (linear algebraic, graph-theoretic) independence. This package provides methods to perform computations with matroids in Macaulay2. @BR{}@ @BR{}@
			Matroids are stored as pairs (E, B) of a ground set E and a list of bases, which are sets of elements of the ground set. Internally, a ground set of size n is always identified with the list $\{0, ..., n-1\}$, and thus all subsets of the ground set (e.g. bases, circuits, flats) also must be subsets of $\{0, ..., n-1\}$. However, the actual elements of the ground set are stored separately, and allowed to be arbitrary (e.g. integers, variables, vectors, edges in a graph). @BR{}@ @BR{}@
			The package provides capabilities for converting between various representations of matroids, directly creating linear and graphic matroids from a matrix or graph, creating and detecting existence of minors, computing Tutte polynomials, and some additional functions for matroid applications in other areas. @BR{}@ @BR{}@
			The user can specify a matroid can by either its bases, nonbases, circuits, from a matrix or graph, or via a collection of predefined matroids. For more on how to construct a matroid, see @TO matroid@. @BR{}@ @BR{}@
			{\bf Reference} Oxley, Matroid Theory, second edition. Oxford University Press, 2011.
///

doc ///
	Key
		Matroid
	Headline
		the class of all matroids
	Description
		Text
			To see how to specify a matroid, see @TO matroid@. @BR{}@ @BR{}@
			In this package, the ground set of the matroid is always (internally) assumed to be of the form $\{0, ..., n-1\}$. This means that although the actual elements of the ground set can be arbitrary, all subsets of the ground set are specified by their indices, i.e. as a subset of $\{0, ..., n-1\}$ (this includes bases, circuits, flats, loops, etc.). If you prefer to enter subsets as actual elements in the ground set, remember to use the function @TO indicesOf@ before calling any of the built-in methods. Conversely, to view the elements given the indices, use @TO groundSet@.
///

doc ///
	Key
		matroid
		(matroid, List, List)
		(matroid, List)
		(matroid, Matrix)
		(matroid, Graph)
	Headline
		constructs a matroid
	Usage
		M = matroid(E, B)
		M = matroid(B)
		M = matroid(E, C, EntryMethod => "circuits", TargetRank => r)
		M = matroid(A)
		M = matroid(G)
	Inputs
		E:List
			a ground set
		B:List
			a list of bases
		C:List
			a list of circuits
		A:Matrix
			whose column vectors forms the ground set
		G:Graph
	Outputs
		M:Matroid
	Description
		Text
			The default representation of a matroid in this package is by its ground set and set of bases. If no ground set is provided, the ground set is taken to be the union of the basis/circuit elements (this does not work with the option `EntryMethod => "nonbases"'). This function does not check if (E,B) defines a matroid - see @TO isValid@. @BR{}@ @BR{}@
			If a list of circuits is provided, the bases are automatically computed in the process of creation. The target rank may be specified when entering a list of circuits, to speed up computation. @BR{}@ @BR{}@
			If a matrix is provided, then the realizable matroid on the columns of the matrix is returned. @BR{}@ @BR{}@
			If a graph is provided, then the graphic matroid is returned.
		Example
			M1 = matroid({{0,1},{0,2}})
			peek M1
			M2 = matroid({a,b,c},{}, EntryMethod => "nonbases", TargetRank => 2)
			peek M2
			M3 = matroid completeGraph 3
			peek M3
			M4 = matroid random(ZZ^3, ZZ^5)
			peek M4
	SeeAlso
		isValid
		bases
		indicesOf
		specificMatroids
	Caveat
		The bases are not stored as subsets of the ground set - the indices (with respect to the ground set) are stored instead.
///

doc ///
	Key
		EntryMethod
	Headline
		select method of specifying matroid
	Usage
		M = matroid({a,b,c},{{1,2}}, EntryMethod => "nonbases")
///

doc ///
	Key
		TargetRank
	Headline
		specify target rank
	Usage
		M1 = matroid({a,b,c},{}, EntryMethod => "nonbases", TargetRank => 2)
		M2 = matroid({a,b,c},{{1,2}}, EntryMethod => "circuits", TargetRank => 2)
		closure(M2, {2}, TargetRank => 2)
///

doc ///
	Key
		(net, Matroid)
	Usage
		net(M)
	Inputs
		M:Matroid
	Outputs
		:Net
	Description
		Text
			Shortens default output for an object of type Matroid.
		Example
			net matroid completeGraph 3
///

doc ///
	Key
		(symbol ==, Matroid, Matroid)
	Usage
		M == M'
	Inputs
		M:Matroid
		M':Matroid
	Outputs
		:Boolean
			whether the two matroids are equal
	Description
		Text
			Two matroids are considered equal if they have the same set of (indexed) bases and same size grounds sets (in particular, the ground sets need not be identical). This happens iff the identity permutation is an isomorphism. @BR{}@ @BR{}@
			The strong comparison operator === should not be used, as bases (and ground sets) are internally stored as lists rather than sets, so the same matroid with a different ordering on the list of bases (or ground set) will be treated as different under ===.
		Example
			M = matroid completeGraph 3
			M' = uniformMatroid(2, 3)
			M == M'
	SeeAlso
		isomorphic
///

doc ///
	Key
		[matroid, EntryMethod]
	Headline
		select method of specifying matroid
	Usage
		matroid(..., EntryMethod => "bases")
		matroid(..., EntryMethod => "nonbases")
		matroid(..., EntryMethod => "circuits")
	Description
		Text
			A matroid is determined by its set of bases, i.e. maximal (with respect to inclusion) independent sets, which are all of the same size (namely, the rank of the matroid). However, many interesting matroids have relatively few dependencies, and thus it may be easier to specify the matroid by its nonbases, i.e. dependent subsets of the ground set, with size equal to the rank of the matroid. @BR{}@ @BR{}@
			Similarly, a matroid can be specified by its circuits, i.e. minimal dependent sets. This is implicitly done when creating a graphical matroid.
		Example
			fano = matroid(toList (1..7), {{0,1,2},{0,4,5},{0,3,6},{1,3,5},{1,4,6},{2,3,4},{2,5,6}}, EntryMethod => "nonbases")
///

doc ///
	Key
		[matroid, TargetRank]
	Headline
		specify target rank
	Usage
		matroid(..., TargetRank => ZZ)
	Description
		Text
			When constructing a matroid, if the rank of matroid is known beforehand, then it can be specified with this option. This option is necessary when using EntryMethod => "nonbases" and specifying an empty set of nonbases, in which case the uniform matroid of the given rank is constructed. @BR{}@ @BR{}@
			This option may be used when specifying a matroid by its circuits, to speed up computation time. This is done automatically when creating a graphical matroid, as the rank equals the number of vertices minus the number of components of the graph.
		Example
			matroid({a,b,c},{{1,2}}, EntryMethod => "circuits", TargetRank => 2)
			matroid({a,b,c},{},EntryMethod => "nonbases", TargetRank => 1)
///

doc ///
	Key
		[closure, TargetRank]
	Headline
		specify target rank of closure
	Usage
		closure(..., TargetRank => ZZ)
	Description
		Text
			When taking a closure of a subset of the ground set, if the desired rank of the closure is known beforehand, then specifying it with this option can speed up computation time.
		Example
			M = matroid({a,b,c},{{0,1},{0,2}})
			closure(M, {0,1}, TargetRank => 2)
///

doc ///
	Key
		isValid
		(isValid, Matroid)
	Headline
		checks the basis exchange property
	Usage
		isValid M
	Inputs
		M:Matroid
	Outputs
		:Boolean
			whether or not a set of subsets satisfies the basis exchange property
	Description
		Text
			The basis exchange property states that if A, B are basis elements and a is in $A \setminus B$, then there exists $b in B \setminus A$ such that $A \setminus {a} \cup {b}$ is a basis element. A set of subsets B of a ground set E is a basis for a matroid on E iff it satisfies the basis exchange property.
		Example
			isValid matroid({a,b,c,d},{{0,1},{2,3}})
			isValid matroid({a,b,c,d},{{0,1},{0,2}})
///

doc ///
	Key
		ground
	Headline
		ground set
	Usage
		M.ground
	Description
		Text
			Returns the ground set as a set, instead of a list
		Example
			M = matroid({a,b,c},{{0,1},{0,2}})
			M.ground
	SeeAlso
		groundSet
///

doc ///
	Key
		groundSet
		(groundSet, Matroid)
		(groundSet, Matroid, List)
		(groundSet, Matroid, Set)
	Headline
		subset of the ground set
	Usage
		groundSet M
		groundSet(M, S)
	Inputs
		M:Matroid
		S:Set
	Outputs
		:List
			of elements of the ground set
	Description
		Text
			Converts a list of indices to the list of elements of the ground set with those indices. The inverse of this function is @TO indicesOf@.
		Example
			M = matroid({a,b,c},{{0,1},{0,2}})
			groundSet_M {0,2}
	SeeAlso
		ground
		indicesOf
///

doc ///
	Key
		indicesOf
		(indicesOf, List, List)
		(indicesOf, Matroid, List)
		(indicesOf, Matroid, Set)
	Headline
		indices of a sublist
	Usage
		indicesOf(E, F)
		indicesOf(M, F)
	Inputs
		E:List
		M:Matroid
			equivalent to calling E = groundSet M
		F:List
			a sublist of E
	Outputs
		:List
			of indices
	Description
		Text
			Converts a sublist F of a list E to the list of corresponding indices. When called with a matroid, the ambient list E is taken as the ground set of the matroid, in which case the inverse is @TO groundSet@.
		Example
			indicesOf(toList (a..z),{m,a,t,r,o,i,d})
			M = matroid({a,b,c},{{0,1},{0,2}})
			indicesOf_M {a, c}
	SeeAlso
		groundSet
	Caveat
		No attempt is made to check that F is actually a sublist of E.
///

doc ///
	Key
		bases
		(bases, Matroid)
	Headline
		bases of matroid
	Usage
		bases M
	Inputs
		M:Matroid
	Outputs
		:List
			of basis elements
	Description
		Text
			Returns a list of bases of the matroid. The basis elements are represented as sets of nonnegative integers, which are the indices of the elements in the ground set that make up a basis element. To get the subset of the ground set corresponding to a set of indices, use @TO groundSet@.
		Example
			M = matroid({a,b,c},{{0,1},{0,2}})
			bases M
			groundSet_M (bases M)#0
	SeeAlso
		nonbases
		groundSet
///

doc ///
	Key
		nonbases
		(nonbases, Matroid)
	Headline
		nonbases of matroid
	Usage
		nonbases M
	Inputs
		M:Matroid
	Outputs
		:List
	Description
		Text
			The nonbases of a matroid are the dependent subsets of the ground set of size equal to that of a basis element. The same convention for storing @TO bases@ is used for nonbases, i.e. the indices (rather than the elements themselves) are stored.
		Example
			M = matroid({a,b,c},{{0,1},{0,2}})
			nonbases M
	SeeAlso
		bases
///

doc ///
	Key
		circuits
		(circuits, Matroid)
	Headline
		circuits of matroid
	Usage
		circuits M
	Inputs
		M:Matroid
	Outputs
		:List
	Description
		Text
			The circuits of a matroid are the minimal dependent subsets of the ground set.
		Example
			M = matroid({a,b,c},{{0,1},{0,2}})
			circuits M
///

doc ///
	Key
		fundamentalCircuit
		(fundamentalCircuit, Matroid, List, ZZ)
		(fundamentalCircuit, Matroid, Set, ZZ)
	Headline
		fundamental circuit of basis
	Usage
		fundamentalCircuit(M, B, e)
	Inputs
		M:Matroid
		B:List
		e:ZZ
	Outputs
		:List
	Description
		Text
			The fundamental circuit of a basis B with respect to an element e not in B of the ground set is the unique circuit contained in $B \cup e$. Note that e is specified by its index in the ground set, not as an element.
		Example
			M = matroid({a,b,c},{{0,1},{0,2}})
			fundamentalCircuit(M, (bases M)#0, 2)
	Caveat
		An error is thrown if the element e is in the basis B.
	SeeAlso
		circuits
///

doc ///
	Key
		loops
		(loops, Matroid)
	Headline
		loops of matroid
	Usage
		loops M
	Inputs
		M:Matroid
	Outputs
		:List
	Description
		Text
			The loops of a matroid are the one-element circuits.
		Example
			M = matroid({a,b,c,d},{{0,1},{0,2}})
			loops M
	SeeAlso
		coloops
///

doc ///
	Key
		coloops
		(coloops, Matroid)
	Headline
		coloops of matroid
	Usage
		coloops M
	Inputs
		M:Matroid
	Outputs
		:List
	Description
		Text
			The coloops of a matroid M are the loops of the dual matroid. The set of coloops of M equals both the intersection of the bases of M, and the complement of the union of the circuits of M.
		Example
			M = matroid({a,b,c,d},{{0,1},{0,2}})
			coloops M
	SeeAlso
		loops
///

doc ///
	Key
		independents
		(independents, Matroid, ZZ)
	Headline
		independent sets of a given size
	Usage
		independents(M, s)
	Inputs
		M:Matroid
		s:ZZ
	Outputs
		:List
			the independent sets in M of size s
	Description
		Text
			Returns all independent subsets of the ground set of a fixed size s.
		Example
			M = matroid({a,b,c},{{0,1},{0,2}})
			independents(M, 2)
///

doc ///
	Key
		isDependent
		(isDependent, Matroid, Set)
		(isDependent, Matroid, List)
	Headline
		checks dependence of a subset
	Usage
		isDependent(M, S)
	Inputs
		M:Matroid
		S:List
	Outputs
		:Boolean
			whether S is dependent in M
	Description
		Text
			Checks dependence of a subset of the ground set.
		Example
			M = matroid({a,b,c},{{0,1},{0,2}})
			isDependent_M {0,1}
///

doc ///
	Key
		rk
		(rk, Matroid)
		(rk, Matroid, List)
		(rk, Matroid, Set)
	Headline
		rank of a subset of a matroid
	Usage
		rk M
		rk(M, S)
	Inputs
		M:Matroid
		S:List
		S:Set
	Outputs
		:ZZ
	Description
		Text
			The rank of a subset S of a matroid is the size of a maximal independent subset of S. The map $2^E \to \mathbb{N}$, $S \mapsto rk(S)$, is called the rank function, and completely determines the matroid.
		Example
			M = matroid({a,b,c},{{0,1},{0,2}})
			rk M
			rk_M {0,1}
///

doc ///
	Key
		closure
		(closure, Matroid, List)
		(closure, Matroid, Set)
	Headline
		closure of a subset of a matroid
	Usage
		closure(M, A)
	Inputs
		M:Matroid
		A:List
	Outputs
		:List
	Description
		Text
			The closure of a subset A of a matroid (E, B) is the set $cl(A) := \{x \in E \mid rk(A) = rk(A \cup \{x\}) \}$. The closure operator $2^E -> 2^E$, $A \mapsto cl(A)$, completely determines the matroid. 
		Example
			M = matroid({a,b,c},{{0,1},{0,2}})
			closure_M {0,1}
///

doc ///
	Key
		flats
		(flats, Matroid, ZZ)
		(flats, Matroid)
	Headline
		flats of a matroid
	Usage
		flats(M, r)
		flats M
	Inputs
		M:Matroid
		r:ZZ
			the target rank (optional)
	Outputs
		:List
	Description
		Text
			A flat, or closed subspace, of a matroid is a subset A of the ground set which equals its @TO closure@. The set of flats, partially ordered by inclusion, forms a lattice, which is atomistic (i.e. every element is a join of atoms = rank 1 elements) and semimodular. Conversely, every atomistic semimodular lattice is the lattice of flats of a matroid.
		Example
			M = matroid({a,b,c},{{0,1},{0,2}})
			flats_M 1
			netList flats M
	SeeAlso
		closure
		hyperplanes
		fvector
///

doc ///
	Key
		hyperplanes
		(hyperplanes, Matroid)
	Headline
		hyperplanes of a matroid
	Usage
		hyperplanes M
	Inputs
		M:Matroid
	Outputs
		:List
	Description
		Text
			The hyperplanes of a matroid are the flats of rank equal to rk M - 1. The complements of the hyperplanes are precisely the circuits of the dual matroid, and thus a matroid is determined by its hyperplanes.
		Example
			M = matroid({a,b,c},{{0,1},{0,2}})
			hyperplanes M
	SeeAlso
		flats
		rk
///

doc ///
	Key
		fvector
		(fvector, Matroid)
	Headline
		f-vector of a matroid
	Usage
		fvector M
	Inputs
		M:Matroid
	Outputs
		:List
	Description
		Text
			The f-vector of a matroid M is the invariant (f_0, f_1, ..., f_r), where f_i is the number of rank i flats of M, and r is the rank of M. Note that f_0 = f_r = 1.
		Example
			M = matroid({a,b,c},{{0,1},{0,2}})
			fvector M
	SeeAlso
		flats
		rk
	Caveat
		This is not the same as the f-vector of the independence complex of the matroid M.
///

doc ///
	Key
		dualMatroid
		(dualMatroid, Matroid)
	Headline
		dual matroid
	Usage
		dualMatroid M
	Inputs
		M:Matroid
	Outputs
		:Matroid
			the dual matroid of M
	Description
		Text
			The dual matroid of a matroid M has the same ground set as M, and bases equal to the complements of bases of M.
		Example
			M = matroid({a,b,c},{{0,1},{0,2}})
			D = dualMatroid M
			peek D
			M == dualMatroid D
///

doc ///
	Key
		restriction
		(restriction, Matroid, Set)
		(restriction, Matroid, List)
	Headline
		restriction of matroid to subset
	Usage
		restriction(M, S)
	Inputs
		M:Matroid
		S:Set
		S:List
	Outputs
		:Matroid
			the restriction of M to S
	Description
		Text
			The restriction of M to S, M|S, has ground set S and independent sets equal to the independent sets of M contained in S.
		Example
			M = matroid({a,b,c},{{0,1},{0,2}})
			peek restriction_M {0,1}
	SeeAlso
		deletion
///

doc ///
	Key
		deletion
		(deletion, Matroid, Set)
		(deletion, Matroid, List)
	Headline
		deletion of subset of matroid
	Usage
		deletion(M, S)
	Inputs
		M:Matroid
		S:Set
		S:List
	Outputs
		:Matroid
			the deleted matroid M - S
	Description
		Text
			The deleted matroid M - S is obtained by restricting to the complement of S.
		Example
			M = matroid({a,b,c},{{0,1},{0,2}})
			peek deletion_M {0}
	SeeAlso
		restriction
		contraction
///

doc ///
	Key
		contraction
		(contraction, Matroid, Set)
		(contraction, Matroid, List)
	Headline
		contraction of matroid by subset
	Usage
		contraction(M, S)
	Inputs
		M:Matroid
		S:Set
		S:List
	Outputs
		:Matroid
			the contraction of M by S
	Description
		Text
			The contraction of M by S is given by M/S := (M* - S)*, where * stands for dual, and - is deletion.
		Example
			M = matroid({a,b,c},{{0,1},{0,2}})
			peek contraction_M {0}
	SeeAlso
		deletion
		dualMatroid
///

doc ///
	Key
		minor
		(minor, Matroid, List, List)
		(minor, Matroid, Set, Set)
	Headline
		minor of matroid
	Usage
		minor(M, X, Y)
	Inputs
		M:Matroid
		X:List
		Y:List
	Outputs
		:Matroid
			the minor M / X - Y
	Description
		Text
			The minor M / X - Y of M is given by contracting X and deleting Y. The resulting matroid is independent of the order in which deletion and contraction is done. 
		Example
			M = matroid random(ZZ^3,ZZ^6)
			groundSet M
			peek minor(M, {3}, {0,1})
	Caveat
		X and Y are assumed to be disjoint. Also, the indices of X and Y are taken with respect to the ground set of M, so e.g. the indices of Y are not taken with respect to the ground set of M/X. 
	SeeAlso
		deletion
		contraction
		hasMinor
///

doc ///
	Key
		hasMinor
		(hasMinor, Matroid, Matroid)
	Headline
		checks if matroid has given minor
	Usage
		hasMinor(M, N)
	Inputs
		M:Matroid
		N:Matroid
	Outputs
		:Boolean
			whether N is a minor of M
	Description
		Text
			Determines if N is a minor of M, i.e. can be obtained from M by a contraction followed by a deletion. Since deletion and contraction by disjoint subsets commute, every sequence of deletion and contraction operations can be written as a single contraction and deletion. @BR{}@ @BR{}@
			If a minor is found that is isomorphic to N, then the sets to be contracted and deleted are printed (along with the isomorphism with N).
		Example
			hasMinor(matroid completeGraph 4, uniformMatroid(2,4))
			hasMinor(matroid completeGraph 4, matroid completeGraph 3)
	SeeAlso
		minor
///

doc ///
	Key
		directsum
		(directsum, Matroid, Matroid)
	Headline
		direct sum of two matroids
	Usage
		directsum(M, M')
	Inputs
		M:Matroid
		M':Matroid
	Outputs
		:Matroid
			the direct sum of M and M'
	Description
		Text
			The direct sum of M and M' has ground set equal to the disjoint union of those of M and M', and bases equal to the union of bases of M and M'.
		Example
			peek directsum(uniformMatroid(2,3), uniformMatroid(1,3))
	Caveat
		The elements of the ground set of the direct sum will receive a placeholder index to ensure disjointness. As this method is binary, repeated applications of this function will result in nested placeholder indices. Since the bases are stored as indices, the bases of M will not change, but those of M' will be shifted up by the size of the ground set of M.
///

doc ///
	Key
		componentsOf
		(componentsOf, Matroid)
		(componentsOf, List, List)
	Headline
		connected components of matroid
	Usage
		componentsOf M
	Inputs
		M:Matroid
	Outputs
		:List
			the connected components of M
	Description
		Text
			Define an equivalence relation ~ on the ground set of M, by e ~ f iff e = f or $\{e,f\}$ is contained in a circuit. The equivalence classes under ~ are the connected components of M. A matroid is the direct sum of its connected components.
		Example
			M = matroid graph({{0,1},{0,2},{1,2},{3,4},{4,5}})
			componentsOf M
	Caveat
		The connected components of the graphic matroid M(G) need not be the same as the connected components of the graph G.
	SeeAlso
		directsum
///

doc ///
	Key
		representationOf
		(representationOf, Matroid)
	Headline
		represents a realizable/graphic matroid
	Usage
		representationOf M
	Inputs
		M:Matroid
	Outputs
		:Thing
			a representation of M (either a matrix or a graph)
	Description
		Text
			Given a realizable matroid whose ground set elements are vectors, returns the matrix with those column vectors. If the matroid is graphical, then the graph with edge set equal to the ground set is returned.
		Example
			A = random(ZZ^3,ZZ^5)
			M = matroid A
			A == representationOf M
			representationOf matroid completeGraph 4
	SeeAlso
		isRepresentable
///

doc ///
	Key
		isRepresentable
		(isRepresentable, Matroid, Ring)
	Headline
		determines representability of a matroid
	Usage
		isRepresentable(M, k)
	Inputs
		M:Matroid
		k:Ring
			a field or ZZ
	Outputs
		:Boolean
	Description
		Text
			Determines if a matroid is representable. If the ring provided is ZZ, determines if there is a field over which the matroid is representable. If the ring provided is a field, determines if the matroid is representable over a (finite) extension of the field.
		Example
			M = matroid({a,b,c},{{0,1},{0,2},{1,2}})
			isRepresentable(M, ZZ/2)
	Caveat
		When k is a field, this function does NOT determine if the matroid is representable over k itself. Also, this algorithm may take longer than you expect to finish.
	SeeAlso
		representationOf
///

doc ///
	Key
		isomorphic
		(isomorphic, Matroid, Matroid)
	Headline
		checks if two matroids are isomorphic
	Usage
		isomorphic(M, M')
	Inputs
		M:Matroid
		M':Matroid
	Outputs
		:Boolean
			whether M and M' are isomorphic matroids
	Description
		Text
			Two matroids are isomorphic if there is a bijection between their ground sets which induces a bijection between bases. If an isomorphism is found, then the permutation of [0, ..., n-1] inducing the isomorphism is printed, unless there is a trivial reason for existence of an isomorphism (e.g. if the matroids are equal, or have <= 1 basis/nonbasis).
		Example
			M = matroid({a,b,c},{{0,1},{0,2},{1,2}})
			isomorphic(M, uniformMatroid(2,3))
///

doc ///
	Key
		tuttePolynomial
		(tuttePolynomial, Matroid)
		(tuttePolynomial, Matroid, Ring)
	Headline
		computes Tutte polynomial
	Usage
		tuttePolynomial M
		tuttePolynomial(M, R)
	Inputs
		M:Matroid
		R:Ring
	Outputs
		:RingElement
			the Tutte polynomial of M
	Description
		Text
			The Tutte polynomial is an invariant of a matroid that is universal with respect to satisfying a deletion-contraction recurrence. Many invariants of a matroid can be determined by substituting values into its Tutte polynomial - see @TO tutteEvaluate@. @BR{}@ @BR{}@
			This function computes the Tutte polynomial using the deletion-contraction recurrence.
		Example
			M = matroid({a,b,c},{{0,1},{0,2},{1,2}})
			T = tuttePolynomial M
	SeeAlso
		tutte2
		tutteEvaluate
///

doc ///
	Key
		tutte2
		(tutte2, Matroid)
	Headline
		non-recursive computation of Tutte polynomial
	Usage
		tutte2(M)
	Inputs
		M:Matroid
	Outputs
		:RingElement
			the Tutte polynomial of M
	Description
		Text
			An alternative algorithm to compute the Tutte polynomial, involving a sum over all subsets of the ground set (as opposed to the recursive method used in @TO tuttePolynomial@).
		Example
			M = matroid({a,b,c},{{0,1},{0,2},{1,2}})
			tutte2 M
	Caveat
		This algorithm is in general much slower than the recursive method.
	SeeAlso
		tuttePolynomial
///

doc ///
	Key
		tutteEvaluate
		(tutteEvaluate, Matroid, Thing, Thing)
	Headline
		evaluate Tutte polynomial
	Usage
		tutteEvaluate(M, a, b)
	Inputs
		M:Matroid
		a:Thing
		b:Thing
	Outputs
		:Thing
			the evaluation of the Tutte polynomial of M at (a, b)
	Description
		Text
			Provides a method to evaluate the Tutte polynomial at given values. For example, the value of the Tutte polynomial at (1,1) is the number of bases of the matroid.
		Example
			M = matroid({a,b,c},{{0,1},{0,2},{1,2}})
			tutteEvaluate(M, 1, 1)
			tutteEvaluate(M, 2, 0)
	SeeAlso
		tuttePolynomial
///

doc ///
	Key
		chromaticPolynomial
		(chromaticPolynomial, Graph)
		(chromaticPolynomial, Graph, Ring)
	Headline
		computes chromatic polynomial of a graph
	Usage
		chromaticPolynomial G
		chromaticPolynomial(G, R)
	Inputs
		G:Graph
		R:Ring
	Outputs
		:RingElement
			the chromatic polynomial of G
	Description
		Text
			The chromatic polynomial is a graph invariant that counts the number of vertex colorings. @BR{}@ @BR{}@
			This function computes the chromatic polynomial as an evaluation of the Tutte polynomial. If the Tutte polynomial of the graphic matroid has already been computed, then this function should return the chromatic polynomial instantaneously.
		Example
			factor chromaticPolynomial completeGraph 4
	SeeAlso
		tuttePolynomial
///

doc ///
	Key
		uniformMatroid
		(uniformMatroid, ZZ, ZZ)
	Headline
		uniform matroid
	Usage
		U = uniformMatroid(n, k)
	Inputs
		k:ZZ
		n:ZZ
	Outputs
		:Matroid
			the uniform matroid of rank k on n elements
	Description
		Text
			The uniform matroid of rank k has as bases all size k subsets. The ground set is $\{0, ..., n-1\}$.
		Example
			peek uniformMatroid(3,5)
///

doc ///
	Key
		getCycles
		(getCycles, Graph)
	Headline
		find cycles of graph
	Usage
		getCycles(G)
	Inputs
		G:Graph
	Outputs
		:List
			a list of (simple) cycles of G
	Description
		Text
			A cycle of G is a connected, 2-regular subgraph of G (i.e. every vertex has degree 2). For this function, only cycles of length at least 3 are considered (for loops, see @TO graphCircuits@). Each cycle gives rise to 2 closed walks, by reversing orientation. @BR{}@ @BR{}@
			Note that existence of Hamiltonian cycles can be simply read off from the output of this function. Since detection of Hamiltonian cycles is NP-complete, it should not be a surprise that this function may take a long time to complete. @BR{}@ @BR{}@
			This function returns cycles as ordered lists of vertices, whereas graphCircuits returns the list of edges.
		Example
			getCycles completeGraph 4
	SeeAlso
		graphCircuits
///

doc ///
	Key
		getClosedWalks
		(getClosedWalks, Graph, Thing, ZZ)
	Headline
		find closed walks of graph
	Usage
		getClosedWalks(G, v, l)
	Inputs
		G:Graph
		v:Thing
			a vertex of G
		l:ZZ
			the maximum length of a walk
	Outputs
		:List
			of all closed walks centered at v of length at most l
	Description
		Text
			A closed walk of G centered at v is a path of edges in G starting and ending at v. The length of a closed walk is the number of edges appearing in it. This function discards walks which revisit previous edges - to get all paths of a certain length, with repeated edges, use @TO findPaths@. @BR{}@ @BR{}@
			For a fixed vertex v, each cycle passing through v gives rise to exactly 2 closed walks at v, by reversing orientations. 
		Example
			getClosedWalks(completeGraph 5, 0, 4)
	SeeAlso
		getCycles
///

doc ///
	Key
		graphCircuits
		(graphCircuits, Graph)
	Headline
		circuits of graphic matroid
	Usage
		graphCircuits G
	Inputs
		G:Graph
	Outputs
		:List
			the circuits of the graphic matroid M(G)
	Description
		Text
			This function returns the output of @TO getCycles@, along with the loops of G. The circuits are represented as ordered lists of edges (which in turn are given by sets of pairs of vertices). 
		Example
			graphCircuits completeGraph 4
			netList oo
	SeeAlso
		getCycles
///

doc ///
	Key
		matroidPolytope
		(matroidPolytope, Matroid)
	Headline
		matroid polytope
	Usage
		matroidPolytope M
	Inputs
		M:Matroid
	Outputs
		:Matrix
	Description
		Text
			The matroid polytope of a matroid on n elements lives in R^n, and is the convex hull of the indicator vectors of the bases. This function returns a 0-1 matrix, such that the convex hull of the column vectors equals the matroid polytope. The actual polytype can be found using the function convexHull in the Polyhedra package.
		Example
			M = matroid({{0,1},{0,2},{0,3},{1,2},{2,3}})
			matroidPolytope M
///

doc ///
	Key
		greedyAlgorithm
		(greedyAlgorithm, Matroid, List)
	Headline
		finds maximum weight basis
	Usage
		greedyAlgorithm(M, w)
	Inputs
		M:Matroid
		w:List
			a weight function
	Outputs
		:List
			a maximum-weight basis obtained by the greedy algorithm
	Description
		Text
			For a matroid M on ground set E, a weight function on M is a function $w : E -> \mathbb{R}$, extended to all subsets of E by setting $w(X) := \sum_{x \in X} w(x)$. The greedy algorithm for finding a maximum-weight independent subset of E starts with the empty set, and proceeds by successively adding elements of E of maximum weight, which together with the elements already added, form an independent set. @BR{}@ @BR{}@
			In this function, a weight function is specified by its list of values on E. Thus if $E = {e_1, ..., e_n}$, then w is represented as the list ${w(e_1), ..., w(e_n)}$. @BR{}@ @BR{}@
			Matroids can be characterized via the greedy algorithm as follows: a set $\mathcal{I}$ of subsets of E is the set of independent sets of a matroid on E iff $\mathcal{I}$ is nonempty, downward closed, and for every weight function $w : E -> \mathbb{R}$, the greedy algorithm returns a maximal member of $\mathcal{I}$ of maximum weight.
		Example
			M = matroid completeGraph 4
			w = (groundSet M)/(e -> (toList e)#1)
			greedyAlgorithm(M, w)
///

doc ///
	Key
		idealCohomologyRing
		(idealCohomologyRing, Matroid)
	Headline
		the defining ideal of the cohomology ring
	Usage
		idealCohomologyRing M
	Inputs
		M:Matroid
	Outputs
		:Ideal
			the defining ideal of the cohomology ring of M
	Description
		Text
			The cohomology ring of M is the ring R := Z[x_F]/(I1 + I2), where $I1 = (\sum_{i_1 \in F} x_F - \sum_{i_2 \in F} x_F : i_1, i_2 \in M)$ and $I2 = (x_Fx_{F'} : F, F' incomparable)$, as $F$ runs over all proper nonempty flats of $M$. This ring is an Artinian standard graded Gorenstein ring, by a result of Adiprasito, Katz, and Huh.
		Example
			M = matroid completeGraph 4
			I = idealCohomologyRing M
			(0..<rk M)/(i -> hilbertFunction(i, I))
///

doc ///
	Key
		cogeneratorCohRing
		(cogeneratorCohRing, Matroid)
	Headline
		cogenerator of the cohomology ring of a matroid
	Usage
		cogeneratorCohRing M
	Inputs
		M:Matroid
	Outputs
		:Ring
			the dual socle generator of the cohomology ring of M
	Description
		Text
			If R is an Artinian Gorenstein k-algebra, then the Macaulay inverse system of R is generated by a single polynomial (in differential variables), called the cogenerator of R. By a result of Adiprasito, Katz, and Huh, the cohomology ring of a matroid is always Artinian standard graded Gorenstein. This function computes the cogenerator of the cohomology ring.
		Example
			M = matroid completeGraph 4
			cogeneratorCohRing M
	SeeAlso
		idealCohomologyRing
///

doc ///
	Key
		specificMatroids
		(specificMatroids, String)
	Headline
		creates built-in matroid
	Usage
		specificMatroids(S)
	Inputs
		S:String
			the name of the matroid
	Outputs
		:Matroid
	Description
		Text
			Returns one of the named matroids below. Notice that the ground set is a subset of {1, ..., n}.
		Example
			peek specificMatroids "fano"
			peek specificMatroids "nonfano"
			peek specificMatroids "vamos"
			peek specificMatroids "nonpappus"
///

TEST ///
M = matroid({a,b,c,d},{{0,1},{0,2}})
assert(isValid M)
///

TEST ///
M = matroid({a,b,c,d},{{0,1},{0,2}})
assert(bases M === {set{0,1},set{0,2}})
///

TEST ///
M = matroid({a,b,c,d},{{0,1},{0,2}})
assert(nonbases M === {set {2, 3}, set {0, 3}, set {1, 3}, set {1, 2}})
///

TEST ///
M = matroid({a,b,c,d},{{0,1},{0,2}})
assert(circuits M === {set {1, 2}, set {3}})
///

TEST ///
M = matroid({a,b,c,d},{{0,1},{0,2}})
assert(not isDependent_M {1})
///

TEST ///
M = matroid({a,b,c,d},{{0,1},{0,2}})
assert(independents(M, 1) === {set{0},set{1},set{2}})
///

TEST ///
M = matroid({a,b,c,d},{{0,1},{0,2}})
assert(loops M === {3})
///

TEST ///
M = matroid({a,b,c,d},{{0,1},{0,2}})
assert(coloops M === {0})
///

TEST ///
M = matroid({a,b,c,d},{{0,1},{0,2}})
assert(rk_M {0,3} === 1)
///

TEST ///
M = matroid({a,b,c,d},{{0,1},{0,2}})
assert(closure_M {2,3} === {1, 2, 3})
///

TEST ///
M = matroid({a,b,c,d},{{0,1},{0,2}})
assert(flats M === {{set {3}}, {set {0, 3}, set {1, 2, 3}}, {set {0, 1, 2, 3}}})
///

TEST ///
M = matroid({a,b,c,d},{{0,1},{0,2}})
assert(hyperplanes M === {set {0, 3}, set {1, 2, 3}})
///

TEST ///
M = matroid({a,b,c,d},{{0,1},{0,2}})
assert(fvector M === {1,2,1})
///

TEST ///
U = uniformMatroid(2,4)
assert(#bases U == 6)
///

TEST ///
M = matroid matrix{{0,4,-1,6},{0,2/3,7,1}}
assert(isomorphic(M, matroid({a,b,c,d},{{0,1},{0,2}})))
///

TEST ///
M5 = matroid completeGraph 5
assert(#bases M5 === 125)
///

TEST ///
M = matroid({a,b,c,d},{{0,1},{0,2}})
assert(M == matroid({a,b,c,d},{{1,2},{3}}, EntryMethod => "circuits"))
///

TEST ///
assert(uniformMatroid(2,4) == matroid({a,b,c,d}, {}, EntryMethod => "nonbases", TargetRank => 2))
///

TEST ///
S = directsum(uniformMatroid(2,4), matroid completeGraph 3)
C = componentsOf S
assert(S == directsum(C#0, C#1))
///

TEST ///
M = matroid({a,b,c,d},{{0,1},{0,2}})
D = dualMatroid M
assert(D == dualMatroid M)
///

TEST ///
M = matroid({a,b,c,d},{{0,1},{0,2}})
N = deletion_M {3}
assert((groundSet N, bases N) === ({a, b, c}, {set {0, 1}, set {0, 2}}))
///

TEST ///
M = matroid({a,b,c,d},{{0,1},{0,2}})
N = contraction_M {1}
assert((groundSet N, bases N) === ({a, c, d}, {set {0}}))
///

TEST ///
M5 = matroid completeGraph 5
minorM5 = minor(M5, {9}, {3,5,8})
assert((groundSet minorM5, #bases minorM5) === ({set {0, 1}, set {0, 2}, set {0, 3}, set {1, 2}, set {1, 4}, set {2, 3}}, 16))
///

TEST ///
M5 = matroid completeGraph 5
assert(not hasMinor(M5, uniformMatroid(2,4)))
///

TEST ///
M4 = matroid completeGraph 4
assert(toString tuttePolynomial M4 === "x^3+y^3+3*x^2+4*x*y+3*y^2+2*x+2*y")
///

TEST ///
M4 = matroid completeGraph 4
assert(tutteEvaluate(M4, 2, 1) === 38)
///

TEST ///
M4 = matroid completeGraph 4
assert(representationOf M4 === completeGraph 4)
///

TEST ///
A = random(ZZ^3,ZZ^5)
assert(representationOf matroid A === A)
///

TEST ///
F7 = specificMatroids "fano"
w = {0, log(2), 4/3, 1, -4, 2, pi_RR}
assert(greedyAlgorithm(F7, w) === {6,5,3})
///

TEST ///
M4 = matroid completeGraph 4
I = idealCohomologyRing M4
assert((0..<rk M4)/(i -> numColumns basis(i, comodule I)) === (1,8,1))
///

TEST ///
M34 = uniformMatroid(3,4)
I = idealCohomologyRing M34
F = cogeneratorCohRing M34
phi = map(ring F, ring I, gens ring F)
assert(0 == diff(gens phi I, F))
///

end--
restart
loadPackage("Matroids", Reload => true)
uninstallPackage "Matroids"
installPackage "Matroids"
viewHelp "Matroids"
check "Matroids"

--- Examples

M = matroid({a,b,c,d},{{0,1},{0,2}})

matroid(toList (1..4),{{1,2},{1,3}},EntryMethod=>"nonbases") -- Not a matroid

matroid graph({{0,1},{1,2},{0,2},{0,0},{3,4},{4,5},{3,5},{3,3},{5,5}})

M = matroid matrix{{1,0,1,1},{0,1,1,1}} -- parallel elements (test deletion, tuttePolynomial)