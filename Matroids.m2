newPackage("Matroids",
	AuxiliaryFiles => true,
	Version => "1.4.12",
	Date => "May 1, 2022",
	Authors => {{
		Name => "Justin Chen",
		Email => "jchen@math.berkeley.edu",
		HomePage => "https://math.berkeley.edu/~jchen"}},
	Headline => "a package for computations with matroids",
	Keywords => {"Matroids"},
	HomePage => "https://github.com/jchen419/Matroids-M2",
	PackageExports => {"Graphs", "Posets"},
	DebuggingMode => false,
	Certification => {
	     "journal name" => "The Journal of Software for Algebra and Geometry",
	     "journal URI" => "http://j-sag.org/",
	     "article title" => "Matroids: a Macaulay2 package",
	     "acceptance date" => "27 September 2018",
	     "published article URI" => "https://msp.org/jsag/2019/9-1/p03.xhtml",
	     "published article DOI" => "10.2140/jsag.2019.9.19",
	     "published code URI" => "https://msp.org/jsag/2019/9-1/jsag-v9-n1-x03-Matroids.m2",
	     "repository code URI" => "http://github.com/Macaulay2/M2/blob/master/M2/Macaulay2/packages/Matroids.m2",
	     "release at publication" => "cf37f5a1eefc2fe7e6eef2868718256106805027",	    -- git commit number in hex
	     "version at publication" => "0.9.7",
	     "volume number" => "9",
	     "volume URI" => "https://msp.org/jsag/2019/9-1/"
	}
)
export {
	"Matroid",
	"matroid",
	"ParallelEdges",
	"Loops",
	"groundSet",
	"indicesOf",
	"bases",
	"nonbases",
	"circuits",
	"fundamentalCircuit",
	"loops",
	"coloops",
	"isDependent",
	"closure",
	"hyperplanes",
	"flats",
	"latticeOfFlats",
	"restriction",
	"deletion",
	"contraction",
	"minor",
	"hasMinor",
	"isBinary",
	"is3Connected",
	"getSeparation",
	"seriesConnection",
	"parallelConnection",
	"sum2",
	"simpleMatroid",
	"singleElementExtension",
	"CheckWellDefined",
	"freeExtension",
	"freeCoextension",
	"elementaryQuotient",
	"isQuotient",
	"isElementaryQuotient",
	"modularCut",
	"isModularCut",
	"relaxation",
	"relabel",
	"quickIsomorphismTest",
	"getIsos",
	"tutteEvaluate",
	"chromaticPolynomial",
	"setRepresentation",
	"getRepresentation",
	"storedRepresentation",
	"uniformMatroid",
	"affineGeometry",
	"projectiveGeometry",
	"thetaMatroid",
	"binarySpike",
	"spike",
	"swirl",
	"wheel",
	"whirl",
	"getCycles",
	"basisIndicatorMatrix",
	"maxWeightBasis",
	"idealChowRing",
	"Presentation",
	"ChowRingOptions",
	"FlatOrder",
	"cogeneratorChowRing",
	"idealOrlikSolomonAlgebra",
	"specificMatroid",
	"allMatroids",
	"allMinors",
	"toSageMatroid",
	"fromSageMatroid"
}

Matroid = new Type of HashTable
Matroid.synonym = "matroid"

globalAssignment Matroid
net Matroid := M -> (
	net ofClass class M | " of rank " | toString(M.rank) | " on " | toString(#M.groundSet) | " elements"
)

Matroid == Matroid := (M, N) -> M.groundSet === N.groundSet and set bases M === set bases N

matroid = method(Options => {EntryMode => "bases", ParallelEdges => {}, Loops => {}})
matroid (List, List) := Matroid => opts -> (E, L) -> (
	if #L > 0 and not instance(L#0, Set) then L = indicesOf(E, L);
	G := set(0..<#E);
	B := if opts.EntryMode == "nonbases" then if #L == 0 then {G} else subsets(G, #(L#0)) - set L
	else if opts.EntryMode == "bases" then if #L == 0 then error "matroid: There must be at least one basis" else L
	else if opts.EntryMode == "circuits" then (
		x := getSymbol "x";
		R := QQ(monoid[x_0..x_(#E-1)]);
		I := monomialIdeal({0_R} | L/(c -> product(c/(i -> R_i))));
		allVars := product gens R;
		(dual I)_* / (g -> set indices(allVars//g))
	);
	M := new Matroid from {
		symbol groundSet => G,
		symbol bases => B,
		symbol rank => #(B#0),
		cache => new CacheTable from {symbol groundSet => E}
	};
	if opts.EntryMode == "circuits" then (
		M.cache.ideal = I;
		M.cache.circuits = L;
	) else if opts.EntryMode == "nonbases" then M.cache.nonbases = L;
	M
)
matroid List := Matroid => opts -> B -> matroid(unique flatten B, B, opts)
matroid Matrix := Matroid => opts -> A -> (
	k := rank A;
	setRepresentation(matroid(apply(numcols A, i -> A_{i}), (select(subsets(numcols A, k), S -> rank A_S == k))/set), A)
)
matroid Graph := Matroid => opts -> G -> (
	P := opts.ParallelEdges;
	L := opts.Loops/(v -> set{v});
	e := #edges G;
	E := hashTable apply(e, i -> (edges G)#i => i);
	C := getCycles G/(c -> set apply(#c-1, i -> E#(set{c#i, c#(i+1)})));
	for i from 0 to #P - 1 do (
		C = C | select(C, c -> member(E#(P#i), c))/(c -> c - set{E#(P#i)} + set{e+i}) | {set{E#(P#i), e + i}};
	);
	M := matroid(edges G | P | L, C | apply(#L, i -> set{e + #P + i}), EntryMode => "circuits");
	if #L == 0 and #P == 0 then M.cache.graph = G;
	I := id_(ZZ^(#G.vertexSet));
	A := incidenceMatrix G;
	if #P > 0 then A = A | matrix{apply(P/toList, p -> I_{p#0} + I_{p#1})};
	if #L > 0 then A = A | map(ZZ^(numrows A), ZZ^(#L), 0);
	setRepresentation(M, sub(A, ZZ/2))
)
matroid (List, MonomialIdeal) := Matroid => opts -> (E, I) -> (
	allVars := product gens ring I;
	M := matroid(E, (dual I)_* / (g -> set indices(allVars//g)));
	M.cache.ideal = I;
	M
)
matroid Ideal := Matroid => opts -> I -> (
	J := if instance(I, MonomialIdeal) then I else monomialIdeal I;
	-- The following is ~2x faster than isSquareFree
	if (J == I and isSubset(set flatten flatten(J_*/exponents), set{0,1})) then matroid(gens ring J, J)
	else error "matroid: Expected a squarefree monomial ideal"
)

ideal Matroid := MonomialIdeal => M -> ( -- Stanley-Reisner ideal of independence complex
	if M.cache.?ideal then M.cache.ideal else M.cache.ideal = (
		x := getSymbol "x";
		R := QQ(monoid [x_0..x_(#M.groundSet - 1)]);
		dual monomialIdeal({0_R} | apply(bases M, b -> product(toList(M.groundSet - b) /(i -> R_i))))
	)
)

isWellDefined Matroid := Boolean => M -> (
	K := keys M;
	expectedKeys := set {
		symbol groundSet, 
		symbol bases, 
		symbol rank, 
		symbol cache
	};
	if set K =!= expectedKeys then (
		if debugLevel > 0 then (
			added := toList(K - expectedKeys);
			missing := toList(expectedKeys - K);
			if #added > 0 then printerr("isWellDefined: unexpected key(s): " | toString added);
			if #missing > 0 then printerr("isWellDefined: missing keys(s): " | toString missing);
		);
		return false
	);
	if not M.groundSet === set(0..<#M.groundSet) then (
		if debugLevel > 0 then printerr("isWellDefined: expected groundSet to be " | toString set(0..<#M.groundSet));
		return false
	);
	if not (instance(M.bases, List) and all(bases M, b -> instance(b, Set) and isSubset(b, M.groundSet))) then (
		if debugLevel > 0 then printerr("isWellDefined: expected bases to be a list of subsets of groundSet");
		return false
	);
	if not all(M.bases, b -> #b === M.rank) then (
		if debugLevel > 0 then printerr("isWellDefined: expected rank to be the size of all bases");
		return false
	);
	if M.cache.?storedRepresentation then (
		A := M.cache.storedRepresentation;
		if numcols A =!= #M.groundSet or rank A =!= rank M then (
			if debugLevel > 0 then printerr("isWellDefined: storedRepresentation is invalid");
			return false
		);
	);
	 -- circuit elimination
	I := ideal dual M;
	if numgens ideal M < numgens I then I = ideal M;
	R := ring I;
	J := ideal flatten apply(subsets(I_*, 2), p -> (indices gcd(p#0,p#1))/(i -> p#0*p#1//(R_i^2)));
	numgens J == 0 or isSubset(J, I)
)

Matroid _ ZZ := (M, i) -> M.cache.groundSet#i
Matroid _ List := (M, S) -> (M.cache.groundSet)_S
Matroid _ Set := (M, S) -> S/(i -> M.cache.groundSet#i)
Matroid _* := M -> M.cache.groundSet

groundSet = method()
groundSet Matroid := Set => M -> M.groundSet

indicesOf = method()
indicesOf (List, List) := List => (E, L) -> ( -- L: list of lists
	H := hashTable apply(#E, i -> E_i => i);
	L/(l -> set(l/(i -> H#i)))
)
-- indicesOf (List, Sequence) := List => (E, L) -> ( -- L: sequence of sets
	-- H := hashTable apply(#E, i -> E_i => i);
	-- toList(L/(l -> l/(i -> H#i)))
-- )
indicesOf (Matroid, List) := List => (M, L) -> (
	if #L == 0 then return {};
	if not M.cache.?indices then M.cache.indices = hashTable apply(#M.groundSet, i -> M_i => i);
	if not M.cache.indices#?(L#0) then (
		if debugLevel > 0 then printerr("indicesOf: " | toString(L#0) | " is not a member of " | toString(M_*) | ". Treating " | toString(L#0) | " as an index (cf. 'help groundSet')...");
		L
	) else L/(l -> M.cache.indices#l)
)

bases = method()
bases Matroid := List => M -> M.bases

nonbases = method()
nonbases Matroid := List => M -> (
	if M.cache.?nonbases then M.cache.nonbases else M.cache.nonbases = subsets(M.groundSet, rank M) - set M.bases
)

circuits = method()
circuits Matroid := List => M -> (
	if M.cache.?circuits then M.cache.circuits else M.cache.circuits = (ideal M)_*/indices/set
)

fundamentalCircuit = method()
fundamentalCircuit (Matroid, List, Thing) := Set => (M, I, e) -> fundamentalCircuit(M, set indicesOf(M, I), (indicesOf(M, {e}))#0)
fundamentalCircuit (Matroid, Set, ZZ) := Set => (M, I, e) -> (
	J := I + set{e};
	for c in circuits M do if isSubset(c, J) then return c;
	error("fundamentalCircuit: Expected " | toString J | " to be dependent");
)

loops = method()
loops Matroid := List => M -> toList(M.groundSet - flatten(bases M / toList))

coloops = method()
coloops Matroid := List => M -> loops dual M

independentSets Matroid := List => opts -> M -> unique flatten((bases M)/subsets)
independentSets (Matroid, ZZ) := List => opts -> (M, r) -> unique flatten(bases M/(b -> subsets(b, r)))
independentSets (Matroid, List) := List => opts -> (M, S) -> independentSets(M, set indicesOf(M, S))
independentSets (Matroid, Set) := List => opts -> (M, S) -> bases restriction(M, S)

isDependent = method()
isDependent (Matroid, List) := Boolean => (M, S) -> isDependent(M, set indicesOf(M, S))
isDependent (Matroid, Set) := Boolean => (M, S) -> (
	if #S > rank M then return true;
	I := ideal M;
	product(S/(i -> (ring I)_i)) % I == 0
)

rank Matroid := ZZ => M -> M.rank
rank (Matroid, List) := ZZ => (M, S) -> rank(M, set indicesOf(M, S))
rank (Matroid, Set) := ZZ => (M, S) -> (
	if not M.cache#?"ranks" then M.cache#"ranks" = new MutableHashTable;
	if M.cache#"ranks"#?S then M.cache#"ranks"#S else M.cache#"ranks"#S = (
		S0 := sort keys S;
		if M.cache.?rankFunction then (M.cache.rankFunction)(S0)
		else (
			I := ideal M; R := ring I;
			dim (map((coefficientRing R)(monoid [(gens R)_S0]), R))(I)
		)
	)
)

closure = method()
closure (Matroid, List) := List => (M, S) -> toList closure(M, set indicesOf(M, S))
closure (Matroid, Set) := Set => (M, S) -> (
	r := rank(M, S);
	if r == rank M then return M.groundSet;
	S + set select(toList(M.groundSet - S), s -> r == rank(M, S + set{s}))
)

hyperplanes = method()
hyperplanes Matroid := List => M -> (
	if M.cache.?hyperplanes then M.cache.hyperplanes else M.cache.hyperplanes = (circuits dual M)/(c -> M.groundSet - c)
)

flats = method()
flats (Matroid, ZZ) := List => (M, r) -> ( -- computes all intersections of r hyperplanes (which contains all flats of rank = rank M - r)
	if not M.cache#?"flatsOfCorank" then M.cache#"flatsOfCorank" = new MutableHashTable from {0 => {M.groundSet}, 1 => hyperplanes M};
	if M.cache#"flatsOfCorank"#?r then M.cache#"flatsOfCorank"#r else M.cache#"flatsOfCorank"#r = unique flatten apply(flats(M, r-1), f -> apply(hyperplanes M, h -> h*f))
)
flats Matroid := List => M -> (
	if M.cache.?flats then M.cache.flats else M.cache.flats = (
		if debugLevel > 0 then printerr("flats: Finding hyperplanes...");
		H := hyperplanes M;
		if debugLevel > 0 then printerr("flats: " | toString(#H) | " hyperplanes found. Computing intersections of hyperplanes...");
		E := M.groundSet;
		flatList := H;
		newFlats := H;
		M.cache#"flatsRelationsTable" = new MutableHashTable from apply(H, h -> (h, new MutableHashTable from {(h,1),(E,1)}));
		M.cache#"flatsRelationsTable"#E = new MutableHashTable from {(E,1)};
		while true do (
			newFlats = unique flatten apply(newFlats, f -> 
				apply(select(H, h -> not isSubset(f, h)), h -> (
					g := h*f;
					if M.cache#"flatsRelationsTable"#?g then M.cache#"flatsRelationsTable"#g#f = 1 else M.cache#"flatsRelationsTable"#g = new MutableHashTable from {(g,1),(f,1),(h,1),(E,1)};
					g
				))
			) - set flatList;
			if #newFlats == 0 then break;
			if debugLevel > 0 then printerr("flats: " | toString(#newFlats) | " new flats found...");
			flatList = newFlats | flatList;
		);
		append(sort(flatList - set H, f -> #f) | H, E)
	)
)

latticeOfFlats = method()
-- latticeOfFlats Matroid := Poset => M -> poset(flats M/toList/sort, (a, b) -> isSubset(a, b))
latticeOfFlats Matroid := Poset => M -> (
	if not M.cache#?"flatsRelations" then M.cache#"flatsRelations" = (
		H := hyperplanes M;
		E := M.groundSet;
		F01 := flats M;
		F2 := drop(drop(F01, 1), -1);
		if debugLevel > 0 then printerr("latticeOfFlats: Finding transitive closure of precomputed relations...");
		scan(#F2 - #H, i -> (
			f := F2#(-(#H)-1-i);
			scan(toList(set flatten apply(keys M.cache#"flatsRelationsTable"#f, k -> keys M.cache#"flatsRelationsTable"#k) - keys M.cache#"flatsRelationsTable"#f), k -> M.cache#"flatsRelationsTable"#f#k = 1);
		));
		M.cache#"flatsRelationsTable"#(F01#0) = new MutableHashTable from apply(F01, f -> (f,1));
		if debugLevel > 0 then printerr("latticeOfFlats: Creating relations matrix...");
		M.cache#"flatsRelationsMatrix" = matrix apply(F01, f -> apply(F01, f1 -> if M.cache#"flatsRelationsTable"#f#?f1 then 1 else 0));
		if debugLevel > 1 then printerr("latticeOfFlats: relations matrix has rank " | toString(rank M.cache#"flatsRelationsMatrix"));
		if debugLevel > 0 then printerr("latticeOfFlats: Creating relation pairs...");
		sort flatten apply(keys M.cache#"flatsRelationsTable", k -> (
			k0 := sort keys k;
			apply((keys M.cache#"flatsRelationsTable"#k - set{k})/keys/sort, f -> {k0,f})
		))
	);
	poset(flats M/toList/sort, M.cache#"flatsRelations", M.cache#"flatsRelationsMatrix", AntisymmetryStrategy => "none")
)

fVector Matroid := HashTable => opts -> M -> hashTable pairs tally(flats M/rank_M)

dual Matroid := Matroid => {} >> opts -> M -> (
	if M.cache.?dual then M.cache.dual else M.cache.dual = (
		D := matroid(M_*, (bases M)/(b -> M.groundSet - b));
		D.cache.dual = M;
		if M.cache.?storedRepresentation then ( try (
			(r, A) := (rank M, reducedRowEchelonForm M.cache.storedRepresentation);
			pivs := hashTable((a,b) -> a, pivots A);
			nonpivs := sort toList(M.groundSet - values pivs);
			perm := inversePermutation(apply(r, i -> pivs#i) | nonpivs);
			setRepresentation(D, ((-1)*transpose submatrix(A, toList(0..<r), nonpivs) | id_((ring A)^(#M_*-r)))_perm)
		) else (
			if debugLevel > 0 then printerr "dual: could not compute induced dual representation";
			D 
		)) else D
	)
)

restriction = method()
restriction (Matroid, List) := Matroid => (M, S) -> restriction(M, set indicesOf(M, S))
restriction (Matroid, Set) := Matroid => (M, S) -> ( -- assumes S is a subset of M.groundSet (not M_*)
	S0 := sort keys S;
	N := matroid(M_S0, (
		-- H := hashTable(identity, apply(bases M, b -> (I := S*b; (#I, I))));
		-- unique indicesOf(S0, sequence deepSplice H#(max keys H))
		
		-- H := hashTable apply(bases M, b -> (I := S*b; (I, #I)));
		-- r := max values H;
		-- indicesOf(S0, toSequence select(keys H, k -> H#k == r))
		
		-- B := sort(unique(bases M/(b -> S*b)), I -> #I);
		-- indicesOf(S0, drop(B, {0, position(B, I -> #I == #(B#-1)) - 1}) /toList)
		
		B := bases M/(b -> S*b);
		r := max sizes B;
		indicesOf(S0, unique select(B, b -> #b == r) /toList)
	));
	if M.cache.?storedRepresentation then setRepresentation(N, M.cache.storedRepresentation_S0) else N
)
Matroid | Set := (M, S) -> restriction(M, S)
Matroid | List := (M, S) -> restriction(M, S)
-- Note: for tuttePolynomial, do not use ideal M to compute restriction!

deletion = method()
deletion (Matroid, List) := Matroid => (M, S) -> deletion(M, set indicesOf(M, S))
deletion (Matroid, Set) := Matroid => (M, S) -> restriction(M, M.groundSet - S)
Matroid \ Set := (M, S) -> deletion(M, S)
Matroid \ List := (M, S) -> deletion(M, S)

contraction = method()
contraction (Matroid, List) := Matroid => (M, S) -> contraction(M, set indicesOf(M, S))
contraction (Matroid, Set) := Matroid => (M, S) -> ( D := dual M; dual deletion(D, S) ) -- necessary to prevent error with represented matroids over rings that reducedRowEchelonForm cannot handle (e.g. ZZ)
Matroid / Set := (M, S) -> contraction(M, S)
Matroid / List := (M, S) -> contraction(M, S)

minor = method()
minor (Matroid, List, List) := Matroid => (M, X, Y) -> minor(M, set indicesOf(M, X), set indicesOf(M, Y))
minor (Matroid, Set, Set) := Matroid => (M, X, Y) -> (
	if #(X*Y) > 0 then error "minor: Expected disjoint sets";
	N := M / X;
	N \ set((toList Y)/(y -> position(N_*, e -> M_y === e)))
)

hasMinor = method(Options => {Strategy => "flats"})
hasMinor (Matroid, Matroid) := Boolean => opts -> (M, N) -> (
	(n, m) := (#N.groundSet, #M.groundSet);
	if n > m or rank N > rank M or #bases N > #bases M then return false;
	if opts.Strategy === "flats" and isSimple N then (
		v := fVector N;
		truncatedLattice := select(flats(M, rank N), f -> rank_M f >= rank M - rank N);
		possibleFlats := select(truncatedLattice, f -> rank_M f == rank M - rank N);
		truncatedLattice = truncatedLattice - set possibleFlats;
		for f in possibleFlats do (
			if any(1..<rank N, i -> #select(truncatedLattice, F -> rank_M F == rank M - rank N + i and isSubset(f, F)) < v#i) then continue;
			Mf := M/f;
			for Y in independentSets(dual Mf, m - n - #f) do (
				if areIsomorphic(N, Mf \ Y) then (
					if debugLevel > 0 then printerr("hasMinor: Contract "|toString f|", delete "|toString (Y/(y -> (sort toList(M.groundSet - f))#y)));
					return true;
				);
			);
		);
	) else (
		for X in independentSets(M, rank M - rank N) do (
			MX := M / X;
			for Y in independentSets(dual MX, m - n - rank M + rank N) do (
				if areIsomorphic(N, MX \ Y) then (
					if debugLevel > 0 then printerr("hasMinor: Contract "|toString X|", delete "|toString (Y/(y -> (sort toList(M.groundSet - X))#y)));
					return true;
				);
			);
		);
	);
	false
)

isBinary = method()
isBinary Matroid := Boolean => M -> (
	I := ideal dual M;
	if #I_* > #(ideal M)_* then I = ideal M;
	all(subsets(I_*, 2), s -> (lcm s//gcd s) % I == 0)
)

Matroid + Matroid := (M, N) -> (
	(E, B2) := (M_*, bases N);
	if not(E === N_*) then (
		if #set(M_*) < #(M_*) or #set(N_*) < #(N_*) then error "Matroid + Matroid: Cannot have duplicate elements in M or N - cf. ``help (symbol +, Matroid, Matroid)\" for details";
		E = unique(M_* | N_*);
		phi := hashTable apply(#N.groundSet, i -> i => position(E, e -> e === N_i));
		B2 = bases N/(b -> b/(i -> phi#i));
	);
	H := partition(b -> #b, unique flatten table(bases M, B2, plus));
	matroid(E, H#(max keys H))
)

Matroid ++ Matroid := (M, N) -> (
	n := #M.groundSet;
	B := bases N/(b -> b/(i -> i + n));
	matroid(M_*/(e -> (e,0)) | N_*/(e -> (e,1)), unique flatten table(bases M, B, plus))
)

getComponentsRecursive := (S, C) -> (
	if #S == 0 then return {}
	else if #(set S*set flatten(C/toList)) == 0 then return subsets(S, 1);
	comp0 := select(S, s -> any(C, c -> isSubset(set{s, S#0}, c)));
	C = select(C, c -> #(c*set comp0) == 0);
	join({comp0}, getComponentsRecursive(toList(set S - comp0), C))
)
components Matroid := List => M -> (
	singles := join(loops M, coloops M);
	join(subsets(singles, 1), getComponentsRecursive(toList(M.groundSet - singles), circuits M))/set/restriction_M
)

isConnected Matroid := Boolean => M -> (
	I := ideal dual M;
	if #I_* > #(ideal M)_* then I = ideal M;
	all(subsets(gens ring I, 2)/product, p -> any(I_*, g -> g % p == 0) )
)

is3Connected = method()
is3Connected Matroid := Boolean => M -> isConnected M and getSeparation(M, 2) === null

getSeparation = method()
getSeparation (Matroid, ZZ) := Set => (M, k) -> (
	if k > #M_*/2 then ( if debugLevel > 0 then printerr "getSeparation: No k-separation exists for size reasons"; return null );
	if debugLevel > 0 then printerr "getSeparation: Checking existence of minimal k-separator...";
	indepCocircs := select(circuits dual M, c -> #c == k and not isDependent(M, c));
	coindepCircs := select(circuits M, c -> #c == k and not isDependent(dual M, c));
	for X in indepCocircs | coindepCircs do if rank(M, X) + rank(dual M, X) - k <= k-1 then return X;
	if debugLevel > 0 then printerr "getSeparation: Checking existence of nonminimal k-separator...";
	flatsCoflats := toList(set flats M * set flats dual M);
	sepCands := reverse sort(select(flatsCoflats, X -> #X > k and #X < #M_* - k), f -> #f);
	for X in sepCands do if rank(M, X) + rank(dual M, X) - #X <= k-1 then return X;
	null
)

seriesConnection = method()
seriesConnection (Matroid, Matroid) := Matroid => (M, N) -> ( -- assumes basepoint of 0
	if member(0, loops M) then return (M / set{0}) ++ N;
	if member(0, coloops M) then M ++ (N \ set{0});
	n := #M_*;
	D := apply(circuits N, c -> c/(i -> if i > 0 then i = i + n - 1 else 0));
	C1 := select(circuits M, c -> not member(0, c));
	D1 := select(D, c -> not member(0, c));
	(C2, D2) := (circuits M - set C1, D - set D1);
	matroid(toList(0..n+#N_*-2), C1 | D1 | flatten table(C2, D2, plus), EntryMode => "circuits")
)

parallelConnection = method()
parallelConnection (Matroid, Matroid) := Matroid => (M, N) -> dual seriesConnection(dual M, dual N)

sum2 = method()
sum2 (Matroid, Matroid) := Matroid => (M, N) -> (
	if member(0, loops M | loops N | coloops M | coloops N) then error "sum2: Expected basepoint 0 to not be a loop/coloop in either M or N";
	seriesConnection(M, N) / set{0}
)

isSimple Matroid := Boolean => M -> min sizes circuits M > 2

simpleMatroid = method()
simpleMatroid Matroid := Matroid => M -> M \ set(select((ideal M)_*, m -> first degree m <= 2)/indices/last)

-- (CO)EXTENSIONS
-----------------------------------------------------------------

singleElementExtension = method(Options => {CheckWellDefined => false})
singleElementExtension (Matroid, List) := Matroid => o -> (M, K) -> (
    if o.CheckWellDefined and not isModularCut(M, K) then (
	error "singleElementExtension: Expected a modular cut."
    );
    K' := set(K/toList);
    E := toList M.groundSet;
    e := #E;
    B := bases M;
    r := rank M;
    H := select(hyperplanes M, h -> not K'#?h);
    B' := unique flatten for h in H list for b in B list (
	I := b*h;
	if #I == r - 1 then I else continue
    );
    B' = apply(B', I -> I + set{e});
    matroid(E|{e}, B|B')
)
singleElementExtension (Matroid, Set) := Matroid => o -> (M, F) ->
singleElementExtension(M, select(hyperplanes M, h -> isSubset(F, h)),
CheckWellDefined => false)

-- INPUT:  A matroid M and a list K of flats of M forming a modular cut.
-- OUTPUT: The matroid M +_K e that is the single element extension of
--         M by the modular cut K.  See [Ox, Sect 7.2].

-- INPUT:  A matroid M and a set F that is a flat of M.
-- OUTPUT: The matroid M +_F e that is the (principal) single element extension of
--         M by the modular cut of the interval [F, E].  See [Ox, Sect 7.2].
-----------------------------------------------------------------

freeExtension = method()

freeExtension Matroid := Matroid => M -> singleElementExtension(M, M.groundSet)

-- INPUT:  A matroid M.
-- OUTPUT: The matroid M +_E(M) e that is the principal extension of
--         M by the principal modular cut associated to the ground set
--         E(M).  See [Ox, Sect 7.2].
-----------------------------------------------------------------

freeCoextension = method()

freeCoextension Matroid := Matroid => M -> dual singleElementExtension(dual M, M.groundSet)

-- INPUT:  A matroid M.
-- OUTPUT: The matroid M +_E(M) e that is the principal extension of
--         M by the principal modular cut associated to the ground set
--         E(M).  See [Ox, Sect 7.2].
-----------------------------------------------------------------

-- MATROID QUOTIENTS
-----------------------------------------------------------------

elementaryQuotient = method(Options => {CheckWellDefined => false})

elementaryQuotient (List, Matroid) := Matroid => o -> (K, M) -> (
	M' := singleElementExtension(M, K, o);
	e := max toList M'.groundSet;
	M'/{e}
)

-- INPUT:  A matroid M and a list K of flats of M forming a modular cut.
-- OUTPUT: The elementary quotient of M with respect to the modular cut K.
--         See [Ox, Sect 7.3] 
-- CAVEAT: K must be a proper, nonempty set of flats.   
-----------------------------------------------------------------

truncate (Set, Matroid) := Matroid => (F, M) -> (
	M' := singleElementExtension(M, F);
	e := max toList M'.groundSet;
	M'/{e}
)

-- INPUT:  A matroid M and a set F that is a flat of M.
-- OUTPUT: The matroid T_F(M) that is the principal truncation of
--         M by with respect to F.  See [Ox, Sect 7.3]

truncate Matroid := Matroid => M -> truncate(M.groundSet, M)

-- INPUT:  A matroid M.
-- OUTPUT: The matroid T(M) that is the truncation of M.  See [Ox, Sect 7.3].
-----------------------------------------------------------------

isQuotient = method()

isQuotient (Matroid, Matroid) := Boolean => (M', M) -> (
	M.groundSet === M'.groundSet and isSubset(set flats M', set flats M)
)

-----------------------------------------------------------------

isElementaryQuotient = method()

isElementaryQuotient (Matroid, Matroid) := Boolean => (M', M) -> (
	isQuotient(M', M) and rank M' == rank M - 1
)

-----------------------------------------------------------------

modularCut = method()

modularCut (Matroid, Matroid) := List => (M', M) -> (
	if not isElementaryQuotient(M', M) then (
		error "modularCut: Expected the first argument to be an
		elementary quotient matroid of the second argument."
	);
	select(flats M', f -> rank(M, f) - rank(M', f) == 1)/toList/sort
)

-----------------------------------------------------------------

isModularCut = method()

isModularCut (Matroid, List) := Boolean => (M, K) -> (
	K' := set K;
	L := latticeOfFlats M;
	set (filter(L, K/toList/sort)/set) === K' and all(subsets(K, 2), p -> (
		u := p#0 + p#1;
		m := (p#0)*(p#1);
		if rank(M, p#0) + rank(M, p#1) == rank(M, u) + rank(M, m) 
			then K'#?m
			else true
	)) 
)

-- INPUT:  A matroid M and a list K of flats of M.
-- OUTPUT: Whether K is a modular cut of M.
-----------------------------------------------------------------

relaxation = method(Options => {CheckWellDefined => false})
relaxation (Matroid, List) := Matroid => opts -> (M, S) -> relaxation(M, set indicesOf(M, S), CheckWellDefined => true)
relaxation (Matroid, Set) := Matroid => opts -> (M, S) -> (
	if not opts.CheckWellDefined or (member(S, circuits M) and member(S, hyperplanes M)) then matroid(M_*, append(bases M, S))
	else error "relaxation: Expected circuit-hyperplane"
)
relaxation Matroid := Matroid => opts -> M -> (
	CH := set circuits M * set hyperplanes M;
	if #CH == 0 then error "relaxation: No circuit hyperplanes!";
	relaxation(M, first toList CH)
)

relabel = method()
relabel (Matroid, HashTable) := Matroid => (M, perm) -> (
	if set keys perm =!= set values perm then error "relabel: Not a permutation!";
	H := hashTable apply(#M_*, i -> i => if perm#?i then perm#i else i);
	matroid(M_*, (bases M)/(b -> b/(i -> H#i)))
)
relabel (Matroid, List) := Matroid => (M, perm) -> (
	if not all(perm, e -> instance(e, Option)) then perm = apply(#M_*, i -> i => perm#i);
	relabel(M, hashTable perm)
)
relabel Matroid := Matroid => M -> (
	E := toList(0..<#M_*);
	relabel(M, (transpose{E, random E})/toSequence//hashTable)
)

-- Recursively finds all permutations inducing a bijection on circuits (note: permutations(10) is already slow on a typical machine)
getIsos = method()
getIsos (Matroid, Matroid) := List => (M, N) -> (
	(C, D, e) := (sort(circuits M, c -> #c), circuits N, #M.groundSet);
	if not tally sizes C === tally sizes D then return {};
	if #C == 0 then return permutations e;
	local possibles, local c0, local shiftedIndices, local d1, local B, local candidate;
	possibles = {};
	if e > 5 then (
		c0 = toList C#0;
		shiftedIndices = apply(e, i -> i - #select(c0, j -> j < i));
		for d0 in select(D, d -> #d == #c0)/toList do (
			d1 = sort keys(N.groundSet - d0);
			B = apply(permutations d0, q -> hashTable apply(#q, i -> c0#i => q#i));
			possibles = possibles | flatten apply(getIsos(M \ set c0, N \ set d0), p -> (
				flatten apply(B, q -> (
					candidate = apply(e, i -> if member(i, c0) then q#i else (d1)#(p#(shiftedIndices#i)));
					if all(C, c -> member(c/(i -> candidate#i), D)) then {candidate} else {}
				))
			));
		);
		return possibles;
	) else return select(permutations(e), p -> all(C, c -> member(c/(i -> p#i), D)));
)

isomorphism (Matroid, Matroid) := HashTable => (M, N) -> ( -- assumes (M, N) satisfy "Could be isomorphic" by quickIsomorphismTest
	local coloopStore, local C, local D, local e, local C1, local c0slice;
	local coverCircuits, local H, local candidates, local extraElts, local F, local E;
	coloopStore = (M, N)/coloops/sort; -- sort is crucial!
	if #(coloopStore#0) > 0 then (M, N) = (M \ (coloopStore#0), N \ (coloopStore#1)); -- reduces both (M, N) to unions of circuits
	(C, D, e) = (sort(circuits M, c -> #c), circuits N, #M.groundSet);
	if #C == 0 then return hashTable pack(2, mingle coloopStore);
	C1 = C;
	c0slice = sliceBySize(C1#0, C1);
	coverCircuits = {C1#0} | while c0slice#?0 list (
		C1 = sort(c0slice#0, c -> #c);
		c0slice = sliceBySize(C1#0, C1);
		C1#0
	); -- creates maximal list of disjoint circuits in M, covering as much of M.groundSet as possible
	H = apply(coverCircuits, c -> (c, select(D, d -> #d == #c and (pairs sliceBySize(c, C))/last/sizes/tally === (pairs sliceBySize(d, D))/last/sizes/tally))); -- creates list of ordered pairs: first element is member of coverCircuits, second element is list of circuits in N which have the same "intersection size pattern" as the first element
	if min sizes(H/last) == 0 then return;
	candidates = {H};
	for i to #coverCircuits-1 do (
		candidates = flatten apply(candidates, cand -> apply(#last(cand#i), j -> (
			append(cand_{0..<i}, (coverCircuits#i, (last(cand#i))#j)) | apply(cand_{i+1..#coverCircuits-1}, S -> (S#0, select(S#1, s -> #(s*((last(cand#i))#j)) == 0)))
		)))
	); -- "de-nests" second-element lists of H (i.e. each list member becomes its own item, but keeping only those which are disjoint from previously matched circuits of N
	extraElts = M.groundSet - flatten(coverCircuits/toList);
	E = flatten(append(coverCircuits, extraElts)/keys/sort);
	if #extraElts > 0 then candidates = apply(candidates, cand -> cand | {(extraElts, N.groundSet - flatten(cand/last/toList))});
	for cand in candidates do (
		for f in fold((a,b) -> flatten table(a,b,identity), cand/last/keys/permutations) /deepSplice/join do (
			F = hashTable apply(e, i -> E#i => f#i);
			if all(C, c -> member(c/(i -> F#i), D)) then return (
				if #(coloopStore#0) == 0 then F else (
					F = pairs F;
					for i to #(coloopStore#0)-1 do F = apply(F, p -> (p#0 + (if p#0 >= coloopStore#0#i then 1 else 0), p#1 + (if p#1 >= coloopStore#1#i then 1 else 0)));
					hashTable(pack(2, mingle coloopStore) | F)
				)
			);
		);
	);
)

quickIsomorphismTest = method()
quickIsomorphismTest (Matroid, Matroid) := String => (M, N) -> (
	(r, b, e) := (rank M, #bases M, #M.groundSet);
	if not (r == rank N and b == #bases N and e == #N.groundSet) then return "false";
	if M == N then ( if debugLevel > 0 then printerr "quickIsomorphismTest: Matroids are equal"; return "true" );
	if not(betti ideal M === betti ideal N) then return "false";
	if min(b, binomial(e, r) - b) <= 1 then ( if debugLevel > 0 then printerr "quickIsomorphismTest: At most 1 basis/nonbasis"; return "true" );
	try (
		alarm 2; 
		ret := if not betti res dual ideal M === betti res dual ideal N then "false";
		alarm 0;
		ret
	) else (
		alarm 0;
		"Could be isomorphic"
	)
)

areIsomorphic (Matroid, Matroid) := Boolean => (M, N) -> (
	testResult := quickIsomorphismTest(M, N);
	if member(testResult, {null, "Could be isomorphic"}) then not(isomorphism(M, N) === null) else value testResult
)

tuttePolynomialRing := ZZ(monoid(["x","y"]/getSymbol))
tuttePolynomial (Matroid, Ring) := RingElement => memoize((M, R) -> (
	a := coloops M;
	b := loops M;
	if #a + #b == #M.groundSet then R_0^#a*R_1^#b
	else (
		c := set{(keys((bases M)#0 - a))#0};
		tuttePolynomial(deletion(M, c), R) + tuttePolynomial(contraction(M, c), R)
	)
))
tuttePolynomial Matroid := RingElement => M -> tuttePolynomial(matroid(M_*, bases M), tuttePolynomialRing) -- avoids computing induced representations for deletions/contractions, when M has a storedRepresentation

tutteEvaluate = method()
tutteEvaluate (Matroid, Thing, Thing) := Thing => (M, a, b) -> (
	T := tuttePolynomial M;
	sub(T, {(ring T)_0 => a, (ring T)_1 => b})
)

characteristicPolynomial Matroid := RingElement => opts -> M -> (
	T := tuttePolynomial M;
	R := ZZ(monoid([getSymbol "x"]));
	(map(R, ring T, {1 - R_0, 0}))((-1)^(rank M)*T)
)

chromaticPolynomial = method()
chromaticPolynomial Graph := RingElement => G -> (
	P := characteristicPolynomial matroid G;
	(ring P)_0^(#connectedComponents G)*P
)

getCycles = method()
getCycles Graph := List => G -> (
	if not isConnected G then return flatten((connectedComponents G)/(c -> getCycles inducedSubgraph(G, c)));
	G = graph edges G; -- removes loops
	if #edges G < #G.vertexSet then return {}; -- G is a tree
	while true do (
		nonLeaves := select(G.vertexSet, v -> #neighbors(G, v) > 1);
		if #nonLeaves == #G.vertexSet then break;
		if #nonLeaves == 0 then return {};
		G = inducedSubgraph(G, nonLeaves);
	);
	cycles := {};
	while #G.vertexSet > 2 do (
		cycles = join(cycles, select(getClosedWalks(G, G.vertexSet#0, #G.vertexSet), p -> p#1 < p#(#p - 2)));
		G = deleteVertices(G, {G.vertexSet#0});
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

basisIndicatorMatrix = method()
basisIndicatorMatrix Matroid := Matrix => M -> (
	initVector := toList M.groundSet;
	transpose matrix(bases M/(b -> initVector/(i -> if member(i, b) then 1 else 0)))
)

independenceComplex Matroid := SimplicialComplex => M -> simplicialComplex ideal M

maxWeightBasis = method()
maxWeightBasis (Matroid, List) := Set => (M, w) -> (
	maxWeightSol := set{};
	W := (rsort apply(#w, i -> (w#i, i)))/last;
	while not member(maxWeightSol, bases M) do (
		for i from 0 to #W-1 do (
			augmentedSol := maxWeightSol + set{W#i};
			if not isDependent(M, augmentedSol) then (
				maxWeightSol = augmentedSol;
				W = W_(delete(i, toList(0..<#W)));
				break;
			);
		);
	);
	maxWeightSol
)

idealChowRing = method(Options => {CoefficientRing => QQ, ChowRingOptions => new OptionTable from {MonomialOrder => GLex}, Presentation => "standard", Variable => "x", FlatOrder => null})
idealChowRing Matroid := Ideal => opts -> M -> (
	x := getSymbol opts.Variable;
	N := monoid[apply((flats M)/toList/sort, f -> x_f), opts.ChowRingOptions];
	k := opts.CoefficientRing;
	S := k(N);
	x = hashTable apply(S_*, v -> last baseName v => v);
	if opts.Presentation =!= "standard" then (
		L := latticeOfFlats M;
		L' := subposet(L, select(vertexSet L, 
			F -> rank(M, F) >= if opts.Presentation === "FY" then 1 else 2
		));
		RM := L'.RelationMatrix;
		incomp := apply(flatten apply(numColumns RM, j -> apply(select(j, i -> RM_j_i == 0), i -> {j, i}) ), 
			p -> {L'_(p#0), L'_(p#1)}
		);
	);
	I := if opts.Presentation === "simplicial" then (
		mu := moebiusFunction L;
		ideal apply(incomp, F -> (
			l := sum apply(select(vertexSet L', G -> compare(L, F#0, G)), G -> mu#(F#0, G)*x#G);
			l' := sum apply(select(vertexSet L', G -> compare(L, F#1, G)), G -> mu#(F#1, G)*x#G);
			l*l'
		))
	) else if opts.Presentation === "atom-free" then (
		I1 := ideal apply(incomp, F -> x#(F#0)*x#(F#1));
		I2 := ideal flatten apply(atoms L, a -> apply(select(vertexSet L', F -> not compare(L, a, F) ),
			F -> (x#F)*(sum apply(select(vertexSet L', 
				G -> compare(L, a, G) and compare(L, F, G) ), G -> x#G ) )
		));
		I3 := ideal apply(subsets(atoms L, 2), F -> (
			l := sum apply(select(vertexSet L', G -> compare(L, F#0, G)), G -> x#G);
			l' := sum apply(select(vertexSet L', G -> compare(L, F#1, G)), G -> x#G);
			l*l'
		));
		I1 + I2 + I3
        ) else if opts.Presentation === "FY" then (
		I1 = ideal apply(incomp, F -> x#(F#0)*x#(F#1));
		I2 = ideal apply(atoms L, a -> sum apply(select(vertexSet L', 
				G -> compare(L, a, G)), G -> x#G 
		));
		I1 + I2
        ) else (
		F := delete({}, delete(M.groundSet, flats M)/toList/sort);
		I2 = ideal(select(subsets(F, 2), s -> #unique(s#0 | s#1) > max(#(s#0), #(s#1)))/(p -> x#(p#0)*x#(p#1)));
		L0 := sum(select(F, f -> member(0, f))/(f -> x#f));
		I2 + ideal((1..#M.groundSet - 1)/(i -> sum(select(F, f -> member(i, f))/(f -> x#f)) - L0))
	);
    	if opts.FlatOrder =!= null then (
		orderedVars := apply(opts.FlatOrder, f -> x#f);
		if set support I =!= set orderedVars then (
			error "idealChowRing: Expected FlatOrder to match the support of the Chow ring ideal."
		);
	) else orderedVars = support I;
        sub(I, k(monoid[orderedVars, opts.ChowRingOptions]) )
)

cogeneratorChowRing = method()
cogeneratorChowRing Matroid := RingElement => M -> ( -- sorted flats makes this 3x faster
	t := getSymbol "t";
	I := trim idealChowRing M;
	R := ring I;
	W := R[apply(gens R, v -> t_(last baseName v))];
	sub(value (factor((sum(#gens R, i -> W_i*R_i))^(rank M - 1) % sub(I, W)))#1, QQ[gens W])
)

idealOrlikSolomonAlgebra = method(Options => {CoefficientRing => QQ, Variable => "e"})
idealOrlikSolomonAlgebra Matroid := Ideal => opts -> M -> (
	V := sort toList M.groundSet;
	e := getSymbol opts.Variable;
	E := (opts.CoefficientRing)[apply(V, v -> e_v), SkewCommutative => true];
	e = hashTable apply(E_*, v -> last baseName v => v);
	trim ideal apply(circuits M/toList, c -> sum(#c, i -> product(#c, j -> if i == j then 1 else (-1)^j*e#(c#j))))
	-- Cir := apply(circuits M,C->toList C);
	-- return trim ideal apply(Cir,c->sum for i from 0 to length c - 1 list 
		-- product for j from 0 to length c - 1 list if i == j then 1 
		-- else (-1)^j*e#j);
)

setRepresentation = method()
setRepresentation (Matroid, Matrix) := Matroid => (M, A) -> (
	M.cache.storedRepresentation = A;
	M.cache.rankFunction = S -> rank A_S;
	M
)

getRepresentation = method()
getRepresentation Matroid := Thing => M -> (
	if M.cache.?graph then M.cache.graph -- graph(join(M_*, (flatten(select(M_*, c -> #c == 1)/toList))/(v -> {v,v})))
	else if M.cache.?storedRepresentation then M.cache.storedRepresentation
	else ( printerr("getRepresentation: No representation stored"); null )
)

uniformMatroid = method()
uniformMatroid (ZZ, ZZ) := Matroid => (k, n) -> (
	if k > n then (k,n) = (n,k);
	matroid(toList(0..<n), subsets(n, k)/set)
)

affineGeometry = method()
affineGeometry (ZZ, ZZ) := Matroid => (n, p) -> matroid affineMatrix(n, p)

affineMatrix = (n, p) -> sub(transpose matrix toList((prepend(1,n:0)..prepend(1,n:p-1))/toList), ZZ/p)

projectiveGeometry = method()
projectiveGeometry (ZZ, ZZ) := Matroid => (n, p) -> matroid projectiveMatrix(n, p)

projectiveMatrix = (n, p) -> (
	if n == 0 then return matrix{{1_(ZZ/p)}};
	affineMatrix(n, p) | (matrix{toList((p^n-1)//(p-1):0_(ZZ/p))} || projectiveMatrix(n-1, p))
)

thetaMatroid = method()
thetaMatroid ZZ := Matroid => n -> (
	(X, Y) := (toList(0..<n), toList(n..<2*n));
	matroid(X | Y, ({X} | delete(null, flatten table(n, n, (i,j) -> if i =!= j then (X | {Y#i}) - set{j})) | flatten table(subsets(X, n-2), subsets(Y, 2), (s,t) -> s | t))/set)
)

binarySpike = method() -- unique binary tipped r-spike
binarySpike ZZ := Matroid => r -> matroid(id_((ZZ/2)^r) | matrix table(r, r+1, (i,j) -> if i == j then 0 else 1))

spike = method()
spike (ZZ, List) := Matroid => (r, C3) -> ( -- tipped r-spike
	E := toList(0..2*r);
	C1 := toList apply(r, i -> {0, 2*i+1, 2*(i+1)});
	C2 := apply(subsets(r, 2), p -> {2*p#0+1, 2*(p#0+1), 2*p#1+1, 2*(p#1+1)});
	C := C1 | C2 | C3;
	C4 := select(subsets(E, r+1), s -> not any(C, c -> isSubset(c, s)));
	matroid(E, C | C4, EntryMode => "circuits")
)
spike ZZ := Matroid => r -> spike(r, {}) -- free tipped r-spike

swirl = method()
swirl ZZ := Matroid => r -> ( -- free rank-r swirl
	E := toList(0..<2*r);
	nonSpanningCircuits := (flatten flatten table(r, r-3, (i,j) -> (
		v := toList apply(j, k -> 2*(i+k+1));
		zChoices := toList((set{0,1})^**j/deepSplice/toList);
		apply(zChoices, z -> {2*i, 2*i+1} | (z + v) | {2*(i+j+1), 2*(i+j+1)+1})
	)))/(c -> c/(i -> i % (2*r)));
	spanningCircuits := select(subsets(E, r+1), s -> not any(nonSpanningCircuits, c -> isSubset(c, s)));
	matroid(E, nonSpanningCircuits | spanningCircuits, EntryMode => "circuits")
)

wheel = method()
wheel ZZ := Matroid => r -> if r == 2 then matroid(wheelGraph 3, ParallelEdges => {set{1,2}}) else matroid wheelGraph(r+1)

whirl = method()
whirl ZZ := Matroid => r -> relaxation wheel r

specificMatroid = method()
specificMatroid String := Matroid => name -> (
	if name == "U24" then (
		uniformMatroid(2, 4)
	) else if name == "C5" then (
		matroid(toList(0..4), {{0,1,2}}/set, EntryMode => "nonbases")
	) else if name == "fano" or name == "F7" then (
		projectiveGeometry(2, 2)
	) else if name == "nonfano" or name == "F7-" then (
		relaxation(specificMatroid "fano", set{4,5,6})
	) else if name == "V8+" then (
		spike 4 \ set{0}
	) else if name == "vamos" then (
		relaxation(specificMatroid "V8+", set{4,5,6,7})
	) else if name == "pappus" then (
		matroid(toList(0..8), {{0,1,2},{0,4,6},{0,5,7},{1,3,6},{1,5,8},{2,3,7},{2,4,8},{3,4,5},{6,7,8}}/set, EntryMode => "nonbases")
	) else if name == "nonpappus" then (
		relaxation(specificMatroid "pappus", set{6,7,8})
	) else if name == "nondesargues" then (
		matroid(toList(0..9), {{0,2,5},{0,1,4},{0,7,8},{1,3,5},{2,3,4},{2,6,8},{3,6,9},{4,8,9},{5,6,7}}/set, EntryMode => "nonbases")
	) else if name == "betsyRoss" then (
		-- matroid(id_((GF 4)^3) | matrix{{1,1,1,1,1,1,1,1},{a,1,a+1,1,0,a+1,a+1,1},{a,a+1,1,0,a+1,a+1,a,a}})
		matroid(id_((ZZ/5)^3) | matrix{{1,2,-2,1,2,2,1,1},{1,-2,-1,-1,0,1,-2,-1},{1,1,1,0,1,1,1,1}})
	) else if name == "AG32" then (
		affineGeometry(3, 2)
	) else if name == "AG32'" then (
		relaxation(affineGeometry(3,2), set{1,3,4,6})
	) else if name == "F8" then (
		relaxation(specificMatroid "AG32'", set{0,1,6,7})
	) else if name == "J" then (
		matroid matrix{{0_(ZZ/3),0,1,1,1,0,0,0},{1,1,0,1,0,1,0,0},{0,1,1,0,0,0,1,0},{1,0,0,0,-1,0,-1,1}}
	) else if name == "L8" then (
		matroid(toList(0..7), {{0,1,2,3},{0,1,4,5},{1,3,4,6},{1,2,5,6},{0,3,4,7},{0,2,5,7},{2,3,6,7},{4,5,6,7}}/set, EntryMode => "nonbases")
	) else if name == "O7" then (
		matroid matrix {{1_(ZZ/3),1,1,1,1,1,0},{0,0,1,1,-1,-1,1},{1,-1,0,-1,1,-1,1}}
	) else if name == "P6" then (
		relaxation(specificMatroid "Q6", set{0,1,2})
	) else if name == "P7" then (
		matroid(toList(0..6), {{0,1,2},{0,3,4},{0,5,6},{1,3,5},{2,4,6}}/set, EntryMode => "nonbases")
	) else if name == "P8" then (
		matroid(id_((ZZ/3)^4) | matrix{{0,1,1,-1},{1,0,1,1},{1,1,0,1},{-1,1,1,0}})
	) else if name == "P8=" then (
		matroid(id_((ZZ/5)^4) | matrix{{1,1,1,1},{1,1,3,4},{1,4,0,4},{1,2,1,0}})
	) else if name == "Q3(GF(3)*)" then (
		matroid matrix{{1_(ZZ/3),1,1,1,1,1,1,0,0},{0,0,1,1,1,-1,-1,1,1},{1,-1,0,1,-1,0,-1,1,-1}}
	) else if name == "Q6" then (
		matroid(toList(0..5), {{0,1,2},{0,3,4}}/set, EntryMode => "nonbases")
	) else if name == "Q8" then (
		relaxation(specificMatroid "R8", set{0,2,4,6})
	) else if name == "R6" then (
		sum2(uniformMatroid(2,4), uniformMatroid(2,4))
	) else if name == "R8" then (
		relaxation(specificMatroid "AG32'", set{0,2,5,7})
	) else if name == "R9" then (
		matroid(toList(0..8), {{1,2,3},{3,4,5},{3,4,6},{3,5,6},{4,5,6},{6,7,1},{1,4,0},{1,5,8},{2,4,7},{2,5,0},{2,6,8},{3,7,8},{3,7,0},{3,8,0},{7,8,0}}/set, EntryMode => "nonbases")
	) else if name == "R9A" then (
		matroid(toList(0..8),{{0,1,2,7},{0,1,3,4},{0,1,5,8},{0,2,3,8},{0,2,4,6},{0,3,6,7},{0,4,5,7},{1,2,3,5},{1,3,7,8},{1,4,6,8},{2,4,7,8},{3,4,5,8},{5,6,7,8}}/set, EntryMode => "nonbases")
	) else if name == "R9B" then (
		matroid(toList(0..8),{{0,1,2,7},{0,1,3,4},{0,1,6,8},{0,2,4,6},{0,3,5,8},{0,4,7,8},{1,2,3,5},{1,2,4,8},{1,3,7,8},{1,4,5,7},{2,3,6,7},{3,4,6,8},{5,6,7,8}}/set, EntryMode => "nonbases")
	) else if name == "R10" then (
		matroid(id_((ZZ/2)^5) | matrix{{1,1,0,0,1},{1,1,1,0,0},{0,1,1,1,0},{0,0,1,1,1},{1,0,0,1,1}})
	) else if name == "R12" then (
		matroid(id_((ZZ/2)^6) | matrix{{1,1,1,0,0,0},{1,1,0,1,0,0},{1,0,0,0,1,0},{0,1,0,0,0,1},{0,0,1,0,1,1},{0,0,0,1,1,1}})
	) else if name == "S8" then (
		matroid(id_((ZZ/2)^4) | matrix{{0,1,1,1},{1,0,1,1},{1,1,0,1},{1,1,1,1}})
	) else if name == "S5612" then (
		matroid(id_((ZZ/3)^6) | matrix{{0,1,1,1,1,1},{1,0,1,-1,-1,1},{1,1,0,1,-1,-1},{1,-1,1,0,1,-1},{1,-1,-1,1,0,1},{1,1,-1,-1,1,0}})
	) else if name == "T8" then (
		matroid(id_((ZZ/3)^4) | matrix{{0,1,1,1},{1,0,1,1},{1,1,0,1},{1,1,1,0}})
	) else if name == "T12" then (
		matroid(id_((ZZ/2)^6) | matrix{{1,1,0,0,0,1},{1,0,0,0,1,1},{0,0,0,1,1,1},{0,0,1,1,1,0},{0,1,1,1,0,0},{1,1,1,0,0,0}})
	) else error "specificMatroid: Name string must be one of: fano/F7, nonfano/F7-, vamos, pappus, nonpappus, nondesargues, betsyRoss, AG32, AG32', C5, F8, J, L8, O7, P6, P7, P8, P8=, Q3(GF(3)*), Q6, Q8, R6, R8, R9, R9A, R9B, R10, R12, S8, S5612, T8, T12, U24, V8+"
)
specificMatroid Symbol := Matroid => s -> specificMatroid toString s

allMatroids = method()
allMatroids (ZZ, ZZ) := List => (n, r) -> (
	if r > n then (n, r) = (r, n);
	if r > n//2 then return allMatroids(n, n-r)/dual;
	E := toList(0..<n);
	if r == 0 then return {uniformMatroid(0, n)};
	if r == 1 then return {uniformMatroid(1, n)} | apply(n-1, i -> matroid(E, take(subsets(n, 1), i+1), EntryMode => "nonbases"));
	if n > 9 then error "allMatroids: Can only return all matroids on <= 9 elements";
	PE := reverse sort subsets(set E, r);
	numMatroids := {7, 13, 23, 38, 37, 108, 58, 325, 940, 87, 1275, 190214}; -- cf. Table 1 in https://arxiv.org/pdf/math/0702316.pdf
	K := {(4,2),(5,2),(6,2),(6,3),(7,2),(7,3),(8,2),(8,3),(8,4),(9,2),(9,3),(9,4)};
	H := hashTable apply(#K, i -> K#i => {2*i+1+sum take(numMatroids,i), 2*i+sum take(numMatroids,i+1)});
	db := "SmallMatroids.txt";
	if not fileExists db then db = "Matroids/" | db;
	apply(take(lines get db, H#(n,r)), l -> matroid(E, PE_(positions(characters l, c -> c === "*"))))
)
allMatroids ZZ := List => n -> flatten apply(n+1, i -> allMatroids(n, i))

allMinors = method()
allMinors (Matroid, Matroid) := List => (M, N) -> (
	flatten apply(independentSets(M, rank M - rank N), X -> (
		C := M/X; 
		apply(select(independentSets(dual C, #C.groundSet - #N.groundSet), Y -> areIsomorphic(N, C\Y)), Y -> {X, Y/(y -> (sort toList(M.groundSet - X))#y)})
)))

-- Sage matroid conversions
toSageMatroid = method()
toSageMatroid Matroid := String => M -> ( -- for matroids on <= 26 elements
	alphabet := separate("","abcdefghijklmnopqrstuvwxyz");
	G := concatenate alphabet_(toList(0..<#M.groundSet));
	B := concatenate apply(bases M, b -> "'" | concatenate alphabet_(sort toList b) | "',");
	"Matroid(groundset = '" | G | "', bases = [" | substring(B, 0, #B - 1) | "])"
)

fromSageMatroid = method()
fromSageMatroid String := Matroid => s -> (
	L := separate("',",replace(" |\\[|\\]|groundset|bases|=","",s));
	s0 := L#0;
	s0 = substring(s0,0,8) | "{" | demark(",", separate("", substring(s0,9)));
	L = drop(L, -1) | {replace("'\\)","",L#-1)};
	bases := demark("},", apply(drop(L, 1), t -> "{" | demark(",", drop(separate("", t), 1))));
	value(replace("M", "m", s0) | "}, {" | bases | "}})")
)

-- Miscellaneous general purpose helper functions

-- sorts L by values of f (note: L should not involve sequences at all, due to deepSplice)
sort (List, Function) := opts -> (L, f) -> (
	H := hashTable(identity, apply(L, l -> f(l) => l));
	deepSplice join apply(sort keys H, k -> H#k)
)

sizes = L -> L/(l -> #l)

sliceBySize = (s, L) -> partition(l -> #(l*s), L) -- intersects a set against a list of sets, and records sizes

load "./doc-Matroids.m2"

load "./tests-Matroids.m2"

end--
restart
loadPackage("Matroids", Reload => true)
uninstallPackage "Matroids"
installPackage "Matroids"
installPackage("Matroids", RemakeAllDocumentation => true)
viewHelp "Matroids"
check "Matroids"

-- TODO:
-- Update documentation
-- Potential improvements to flats, latticeOfFlats: record (all?) containment info
