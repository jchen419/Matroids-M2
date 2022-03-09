needsPackage "Matroids"

-- Pasture definitions

Pasture = new Type of HashTable
Pasture.synonym = "pasture"
globalAssignment Pasture
net Pasture := P -> (
    (n, h) := (numgens P.multiplicativeGroup, #P.hexagons);
    (s1, s2) := (if n == 1 then "" else "s", if h == 1 then "" else "s");
    net ofClass class P | " on " | net n | " generator" | s1 | " with " | net h | " hexagon" | s2
)

Foundation = new Type of Pasture
Foundation.synonym = "foundation"
globalAssignment Foundation

Pasture == Pasture := (P1, P2) -> P1.multiplicativeGroup == P2.multiplicativeGroup and P1.epsilon == P2.epsilon and set(P1.hexagons/(h -> set(h/set))) === set(P2.hexagons/(h -> set(h/set)))

PastureMorphism = new Type of Matrix
PastureMorphism.synonym = "pasture morphism"
globalAssignment PastureMorphism
net PastureMorphism := phi -> net phi.map
det PastureMorphism := ZZ => opts -> phi -> det matrix phi.map
matrix PastureMorphism := Matrix => opts -> phi -> phi.map

pastureMorphism = method()
pastureMorphism (Pasture, Pasture, Matrix) := PastureMorphism => (P1, P2, m) -> (
    new PastureMorphism from {
        symbol source => P1,
        symbol target => P2,
        symbol map => map(P2.multiplicativeGroup, P1.multiplicativeGroup, m)
    }
)
pastureMorphism (Pasture, Pasture, List) := List => (P1, P2, L) -> apply(L, m -> pastureMorphism(P1, P2, m))

PastureMorphism * PastureMorphism := (phi1, phi2) -> pastureMorphism(phi2.source, phi1.target, phi1.map * phi2.map)

isWellDefined PastureMorphism := Boolean => phi -> (
    -- TODO
    return true;
)

-- Pasture constructions

pasture = method()
pasture (Matrix, Matrix, List) := Pasture => (A0, eps0, L) -> (
    (A, ch) := myMinPres A0;
    eps := (ch * eps0) % A;
    hexes := if all(L, l -> #l == 3) then L/(h -> h/(p -> p/(e -> ch*e)))
    else if all(L, l -> #l == 2) then hexesFromPairs(A, eps, L/(p -> p/(e -> ch*e)))
    else error "expected a list of hexagons or fundamental pairs";
    new Pasture from {
        symbol multiplicativeGroup => coker A,
        symbol epsilon => eps,
        symbol hexagons => hexes,
        cache => new CacheTable
    }
)
pasture (Module, Matrix, List) := Pasture => (M, eps, L) -> pasture(presentation M, eps, L)
pasture GaloisField := Pasture => k -> (
    q := k.order;
    if q == 2 then return specificPasture "F2";
    n := q-1;
    g := matrix{{n}};
    x := k.PrimitiveElement;
    eps := if even q then 0 else n//2;
    exps := toList(1..<n);
    hexes := while #exps > 0 list (
	a := exps#0;
	b := for j in exps do if x^a + x^j - 1 == 0 then break j;
        h := {{a, b}, {(-a) % n, (eps - a + b) % n}, {(-b) % n, (eps - b + a) % n}};
	exps = exps - set flatten h;
	h/(p -> p/(e -> matrix{{e}} % g))
    );
    pasture(g, matrix{{eps}}, hexes)
)
pasture (Array, String) := Pasture => (varArray, s) -> ( -- s should be a comma-separated list of (Laurent) monomials or binomials in varArray, which all equal 1 in the pasture
    varList := delete(null, unique toList varArray);
    qPos := positions(varList, v -> match(toString v, "qq"));
    if #qPos > 1 then error "`qq` cannot be a variable name. Please rewrite variables and relations.";
    if #qPos > 0 then varList = varList_(qPos | delete(qPos#0, toList(0..<#varList)));
    n := #varList;
    eps := ZZ^(n+1)_{0};
    qq := "(ZZ^" | toString(n+1) | ")";
    for i to n-1 do s = replace(toString varList#i, "(qq_{" | toString(i+1) | "})", s);
    G := 2*eps;
    rels := if s == "" then {} else for r in separate(",", replace("[ ]+", "", s)) list (
	sepPos := position(toList(1..<#r), i -> (not r#(i-1) == "(") and (r#i == "-" or r#i == "+"));
	t := if sepPos === null then {r} else {substring(0, sepPos+1, r), (if r#(sepPos+1) == "-" then "-" else "") | substring(sepPos+2, r)};
	t = apply(t, m -> replace("(?<!\\^\\()-", "qq_{0}*", m));
	t = apply(t, m -> if m == "1" then "(qq_{0})^0" else if m == "qq_{0}*1" then "qq_{0}*0" else m);
        v := apply(t, m -> value replace("qq", qq, replace("[\\^]", "*", replace("[\\*]", "+", m))));
        if #v == 2 then v else ( if #v == 1 then G = G | v#0; continue; )
    );
    pasture(G, eps, rels)
)

TEST ///
assert areIsomorphic(pasture([], ""), specificPasture "F1pm")
assert areIsomorphic(pasture([], "-1,-1-1"), specificPasture "krasner")
assert areIsomorphic(pasture([], "-1"), pasture GF 2)
assert areIsomorphic(pasture([], "0+0"), specificPasture "sign")
V5 = pasture(matrix{{4},{0}}, matrix{{2},{0}}, {{matrix{{1},{0}}, matrix{{0},{1}}}, {matrix{{3},{0}}, matrix{{1},{1}}},{matrix{{2},{0}}, matrix{{1},{2}}}})
assert areIsomorphic(V5, pasture([x,i], "-i^2,x-i,-1-i*x^2"))
///

myMinPres = method()
myMinPres Matrix := Sequence => A -> (
    recursionLimitStore := recursionLimit;
    recursionLimit = max(2*numcols A, recursionLimit);
    -- customized code from minimalPresentation(Module, Strategy => 2)
    (g,ch) := smithNormalForm(A, ChangeMatrix => {true, false});
    recursionLimit = recursionLimitStore;
    piv := select(pivots g,ij -> abs g_ij === 1);
    (rows, cols) := (piv/first, piv/last);
    (submatrix'(g,rows,cols),submatrix'(ch,rows,))
)
myMinPres Module := Sequence => M -> myMinPres presentation M

specificPasture = method()
specificPasture String := Pasture => name -> (
    id0 := id_(ZZ^0);
    id1 := id_(ZZ^1);
    z01 := map(ZZ^0, ZZ^1, 0);
    if name == "F1pm" then pasture(2*id1, id1, {})
    else if name == "F2" then pasture(id0, z01, {})
    else if name == "krasner" then pasture(id0, z01, {{z01, z01}})
    else if name == "sign" then pasture(2*id1, id1, {{0*id1, 0*id1}})
    else error "expected `name' to be one of: `F1pm', `F2', `krasner', `sign'"
)

fiberProduct = method()
fiberProduct (Matrix, Matrix) := Module => (f1, f2) -> (
    if f1.target =!= f2.target then error "expected same target module";
    I := mingens intersect(image f1, image f2);
    G := map(target f1, source I, I);
    (K1, K2) := (f1, f2)/ker/mingens;
    subquotient(matrix(((G // f1) || (G // f2)) | (K1 ++ K2)), relations(source f1 ++ source f2))
)
fiberProduct (PastureMorphism, PastureMorphism) := Pasture => (f1, f2) -> (
    if f1.target =!= f2.target then error "expected same target pasture";
    (P1, P2) := (f1.source, f2.source);
    (A1, A2) := (f1.map, f2.map)/matrix;
    (G1, G2) := (P1.multiplicativeGroup, P2.multiplicativeGroup);
    (hex1, hex2) := (P1.hexagons, P2.hexagons);
    (i1, i2) := (id_G1 || map(ZZ^(numgens G2), ZZ^(numgens G1), 0), map(ZZ^(numgens G1), ZZ^(numgens G2), 0) || id_G2)/matrix;
    G := fiberProduct(f1.map, f2.map);
    T := hashTable(splice, for p in P1.hexagons/first list (set{A1*p#0, A1*p#1}, p));
    validPairs := apply(flatten for p in flatten P2.hexagons list (
    	im := set{A2*p#0, A2*p#1};
	if not T#?im then continue;
	P1preimages := if instance(T#im, Sequence) then toList T#im else {T#im};
	flatten apply(P1preimages, p1 -> delete(null, {
	    if A1*p1#0 == A2*p#0 then {i1 * p1#0 + i2 * p#0, i1 * p1#1 + i2 * p#1},
	    if A1*p1#1 == A2*p#0 then {i1 * p1#1 + i2 * p#0, i1 * p1#0 + i2 * p#1}
	}))
    ), pair -> {pair#0 // gens G, pair#1 // gens G});
    eps := (i1 * P1.epsilon + i2 * P2.epsilon) // gens G;
    pasture(G, eps, validPairs)
)

product (Pasture, Pasture) := Pasture => (P1, P2) -> (
    K := specificPasture "krasner";
    fiberProduct(first morphisms(P1, K), first morphisms(P2, K))
)
Pasture * Pasture := (P1, P2) -> product(P1, P2)

TEST /// -- Fiber product of abelian groups
Z6 = coker matrix{{6}}
f1 = map(Z6, ZZ^1, matrix{{2}})
assert Equation(fiberProduct(f1, f1), image matrix {{1,3,0},{1,0,3}})
f2 = 3*id_(Z6)
assert Equation(fiberProduct(f1, f2), subquotient(matrix {{3,0},{0,2}},matrix {{0},{6}}))
///

TEST /// -- Fiber product of pastures
assert areIsomorphic((pasture GF 2) * (pasture GF 3), specificPasture "F1pm")
G = pasture([x], "x + x^2")
f1 = first morphisms(G, G)
FP = fiberProduct(f1, f1)
assert areIsomorphic(G, FP)
f2 = first morphisms(G, specificPasture "krasner")
FP2 = fiberProduct(f2, f2)
assert(#freePartPasture FP2 == 2 and #FP2.hexagons == 6)
///

fiberCoproduct = method()
fiberCoproduct (Matrix, Matrix) := Module => (f1, f2) -> (
    if f1.source =!= f2.source then error "expected same source module";
    (A1, A2) := (f1, f2)/matrix;
    sourceGens := mingens f1.source;
    if numcols sourceGens == 0 then return G1 ++ G2;
    rels := matrix{apply(numcols sourceGens, i -> A1 * sourceGens_{i} || -A2 * sourceGens_{i})};
    coker(rels | (relations f1.target ++ relations f2.target))
)
fiberCoproduct (PastureMorphism, PastureMorphism) := Pasture => (f1, f2) -> (
    if f1.source =!= f2.source then error "expected same source pasture";
    (A1, A2) := (f1.map, f2.map)/matrix;
    (P1, P2) := (f1.target, f2.target);
    (G1, G2) := (P1.multiplicativeGroup, P2.multiplicativeGroup);
    (eps1, eps2) := (P1.epsilon, P2.epsilon);
    (hex1, hex2) := (P1.hexagons, P2.hexagons);
    (i1, i2) := (id_G1 || map(ZZ^(numgens G2), ZZ^(numgens G1), 0), map(ZZ^(numgens G1), ZZ^(numgens G2), 0) || id_G2)/matrix;
    G := fiberCoproduct(f1.map, f2.map);
    validPairs := apply(hex1/first, p -> {i1*p#0, i1*p#1}) | apply(hex2/first, p -> {i2*p#0, i2*p#1});
    eps := (i1 * P1.epsilon);
    pasture(G, eps, validPairs)
)

coproduct = method()
coproduct (Pasture, Pasture) := Pasture => (P1, P2) -> (
    F1pm := specificPasture "F1pm";
    fiberCoproduct(first morphisms(F1pm, P1), first morphisms(F1pm, P2))
)
Pasture ** Pasture := (P1, P2) -> coproduct(P1, P2)

TEST ///
U24 = uniformMatroid(2, 4)
U = foundation U24
areIsomorphic(U ** U, foundation(U24 ++ U24))
///

-- Foundations

minTopLeft := A -> A_({{0,1,2,3},{1,0,3,2},{2,3,0,1},{3,2,1,0}}#(minPosition A))
-- the output of getPerm is {a, b} means sigma^a * rho^b where sigma = (13) and rho = (123)
getPerm := (A, f) -> (
    B := minTopLeft apply(A, f);
    p1 := if B_1 < B_2 then (-1, 1) else (1, -1);
    p2 := if B_2 < B_3 then (-1, 1) else (1, -1);
    p3 := if B_3 < B_1 then (-1, 1) else (1, -1);
    b := {{p1#0, p3#1}, {p2#0, p1#1}, {p3#0, p2#1}};
    i := position(b/product, x -> x == -1);
    if b#i#0 == -1 then {0, ((i+2) % 3)} else {1, (2*(i+2) % 3)}
)
H4acoeffs := (p1, p2)-> ( -- the order is (eps,xh4,yh4,xh5,yp are permutation of xh4,xh5 
    (u,v) := ((p1#0+p2#0) % 2, (2*(p1#0+1)*p1#1*(p2#0+1)+p2#1) % 3);
    transpose matrix if u == 0 then(
        if v == 0 then {{0,1,0,-1,0},{0,0,1,0,-1}}
        else if v == 1 then {{0,1,0,0,1},{1,0,-1,1,-1}}
        else {{1,-1,0,-1,1},{0,0,1,1,0}}
    ) else (
        if v == 0 then {{0,1,0,0,-1},{0,0,1,-1,0}}
        else if v == 1 then {{1,-1,0,1,-1},{0,0,1,0,1}}
        else {{0,1,0,1,0},{1,0,-1,-1,1}}
    )                  
)
H4bcoeffs := (p1,p2,p3)->( -- permutation of y_i,x_{i-1},x_{i+1}
    w3 := if p1#0 == 0 then (
        if p1#1 == 0 then (0,1,0,0,0,0,0)
        else if p1#1 == 1 then (0,0,-1,0,0,0,0)
        else (1,-1,1,0,0,0,0)
    ) else (
        if p1#1 == 0 then (0,0,1,0,0,0,0)
        else if p1#1 == 1 then (1,1,-1,0,0,0,0)
        else (0,-1,0,0,0,0,0)
    );
    w1 := if p2#0 == 0 then (
        if p2#1 == 0 then (0,0,0,-1,0,0,0)
        else if p2#1 == 1 then (0,0,0,0,1,0,0)
        else (1,0,0,1,-1,0,0)
    ) else (
        if p2#1 == 0 then (0,0,0,0,-1,0,0)
        else if p2#1 == 1 then (1,0,0,-1,1,0,0)
        else (0,0,0,1,0,0,0)
    );
    w2 := if p3#0 == 0 then (
        if p3#1 == 0 then (0,0,0,0,0,-1,0)
        else if p3#1 == 1 then (0,0,0,0,0,0,1) 
        else (1,0,0,0,0,1,-1)
    ) else (
        if p3#1 == 0 then (0,0,0,0,0,0,-1)
        else if p3#1 == 1 then (1,0,0,0,0,-1,1)
        else (0,0,0,0,0,1,0)
    );
    {(w3#0+w1#0+w2#0) % 2} | drop(toList w1 + toList w2 + toList w3,1)
)
h3 := (i, m) -> m_(delete(i-1,#m))
chooseHyp := (L,f,g) -> L#(position(L,h -> isSubset (f+g,h)))
containmentTable := (LF,LH) -> hashTable apply(LH, h -> set select(LF, f -> isSubset (f,h)) => h)

-- genHex = method()
-- genHex (Matrix, Matrix, List) := List => (A, eps, p) -> {{p#0 % A, p#1 % A}, {(-p#1) % A, (eps + p#0 - p#1) % A}, {(-p#0) % A, (eps - p#0 + p#1) % A}}

hexesFromPairs = method()
hexesFromPairs (Matrix, Matrix, List) := List => (A, eps, L) -> (
    hexList := {};
    for p in L do (
        fp := {p#0 % A, p#1 % A};
        if any(hexList, h -> compareHex(fp, h)) then continue;
        hexList = append(hexList, {fp, {(-fp#1) % A, (eps + fp#0 - fp#1) % A}, {(-fp#0) % A, (eps - fp#0 + fp#1) % A}});
    );
    hexList
)

compareHex = method()
compareHex (List, List) := Boolean => (fp, hex) -> any(hex, p -> fp == p or fp == reverse p) -- fp and hex should be in normal form

kruskalSpanningForest = method()
kruskalSpanningForest Graph := Graph => G -> (
    comps := new MutableList from (vertices G/(v -> set{v}));
    k := #connectedComponents G;
    graph(vertices G, for e in sort edges G list (
        if #comps == k then break;
        ic := select(2, comps, c -> #(c*e) > 0);
        if #ic == 1 then continue;
        comps = append(delete(ic#0, delete(ic#1, comps)), ic#0 + ic#1);
        e
    ))
)

TEST ///
G = graph(toList(0..8), {{0,2},{0,4},{0,5},{0,7},{0,8},{1,2},{1,4},{1,5},{1,6},{1,7},{1,8},{3,4},{3,5},{3,6},{3,7},{3,8}})
G = graph(toList(0..9), {{0,4},{1,4},{2,4},{3,4},{0,6},{5,6},{1,7},{5,7},{1,8},{2,8},{5,8},{1,9},{2,9},{3,9},{5,9}})
assert isConnected G
assert(#kruskalSpanningForest G == #vertices G - 1)
assert(#edges spanningForest G == #vertices G - 2)
///

foundation = method(Options => {Strategy => "Bases", HasF7Minor => null, HasF7dualMinor => null})
foundation Matroid := Foundation => opts -> M -> (
    if M.cache#?"foundation" then M.cache#"foundation" else M.cache#"foundation" = (
    r := rank M;
    if opts.Strategy === "Hyperplanes" then (
        hypMap := hashTable apply(#hyperplanes M, i -> (hyperplanes M)#i => i);
        if debugLevel > 5 then print("hypMap: " | net hypMap);
        indexOfHyp := h -> hypMap#h;
        corank2flats := select(flats M, F -> rank_M F == r - 2);
        corank3flats := select(flats M, F -> rank_M F == r - 3);
        if debugLevel > 0 then print "Finding U(2,4) minors ...";
        U24minors := flatten apply(corank2flats, F -> subsets(select(hyperplanes M, H -> isSubset(F, H)), 4));
        if debugLevel > 0 then print "Finding U(2,5) minors ...";
        U25minors := flatten apply(corank2flats, F -> subsets(select(hyperplanes M, H -> isSubset(F, H)), 5));
        if debugLevel > 0 then print "Finding rank 3 minors (C5, U(3,5), Fano) ...";
        F7 := specificMatroid "fano";
        (F7Known, F7dualKnown) := (opts.HasF7Minor =!= null, opts.HasF7dualMinor =!= null);
        (hasF7, hasF7dual) := (if F7Known then opts.HasF7Minor else false, if F7dualKnown then opts.HasF7dualMinor else false);
        H4hyps := flatten for F in corank3flats list (
            cork2F := select(corank2flats, F2 -> isSubset(F, F2));
            if #cork2F < 5 then continue;
            hypsF := select(hyperplanes M, H -> isSubset(F, H));
            if not F7Known and not hasF7 and min(#hypsF, #cork2F) >= 7 then hasF7 = hasMinor(M/F, F7);
            if #hypsF < 8 then continue;
            for S in subsets(cork2F, 5) list (
                T := unique apply(subsets(S, 2)/toSequence, chooseHyp_hypsF);
                if member(#T, {8,10}) then (S, T) else continue
            )
        );
        if debugLevel > 0 then print "Detecting dual Fano minor ...";
        if not F7dualKnown then for F in select(flats M, f -> rank_M f == r - 4) do (
            if #select(corank3flats, F3 -> isSubset(F, F3)) < 7 then continue;
            if #select(corank2flats, F2 -> isSubset(F, F2)) < 21 then continue;
            if #select(hyperplanes M, H -> isSubset(F, H)) < 14 then continue;
            if hasMinor(M/F, dual F7) then (
                hasF7dual = true;
                break;
            );
        );
        if debugLevel > 1 then print ("F7: " | net hasF7 | ", F7*: " | net hasF7dual);
        if debugLevel > 0 then print "All minors found. Finding relations ...";
        H4aminors := select(H4hyps, p -> #last p == 8);
        H4bminors := select(H4hyps, p -> #last p == 10);
        u := #U24minors;
        G := ZZ^(2*u+1);
        eps := matrix G_{0};
        Hminus := (if hasF7 or hasF7dual then 1 else 2)*eps;
        twistedRatios := apply(U24minors, S -> {S#0, S#3, S#2, S#1});
        genRatios := U24minors | twistedRatios;
        genTable := hashTable apply(#U24minors, i -> set genRatios#i => i);
        if debugLevel > 5 then print("genTable: " | net genTable);
        hashMap := (D,i) -> matrix G_{1 + genTable#(set D) + (if i == 0 then 0 else u)};
        H3rels := flatten apply(U25minors/(m -> sort(m, indexOfHyp)), m ->
            {hashMap(h3_5 m,0) + hashMap(h3_3 m,0) - hashMap(h3_4 m,0),
            hashMap(h3_5 m,0) + hashMap(h3_2 m,1) - hashMap(h3_1 m,1),
            hashMap(h3_1 m,0) + hashMap(h3_3 m,0) - hashMap(h3_2 m,0),
            hashMap(h3_2 m,1) + hashMap(h3_4 m,1) - hashMap(h3_3 m,1),
            hashMap(h3_4 m,1) + hashMap(h3_1 m,0) - hashMap(h3_5 m,1)});
        if debugLevel > 0 then print "Finding H4a relations ...";
        H4arels := if #H4aminors == 0 then map(ZZ^(2*u+1),ZZ^0,0) else fold(apply(H4aminors, m -> (
            h := (last m)#(position(last m, x -> #select(first m, f -> isSubset(f,x)) == 3));
            (f4,f5) := toSequence select(first m, f -> not isSubset (f,h));
            (f1,f2,f3) := toSequence (first m - set (f4,f5));
            d1 := {chooseHyp(last m,f4, f1),chooseHyp(last m,f4, f2),chooseHyp(last m, f4, f3), chooseHyp(last m, f4, f5)};
            d2 := {chooseHyp(last m,f5, f1),chooseHyp(last m,f5, f2),chooseHyp(last m, f5, f3), chooseHyp(last m, f4, f5)};
            fold({eps,hashMap(d1,0),hashMap(d1,1),hashMap(d2,0),hashMap(d2,1)},(a,b) -> a|b)*H4acoeffs(getPerm(d1, indexOfHyp), getPerm(d2, indexOfHyp))
            )), (a,b) -> a|b);
        if debugLevel > 5 then print("H4arels: " | toString H4arels);
        if debugLevel > 0 then print "Finding H4b relations ...";
        H4brels := if #H4bminors == 0 then map(ZZ^(2*u+1),ZZ^0,0) else fold(flatten apply(H4bminors, p -> (
            T := containmentTable p;
            Hats := apply(5, i -> (apply(4, j -> T#(set{p#0#i,p#0#((i+1+j) %5)})), apply({0,3,2,1}, j-> T#(set{p#0#i,p#0#((i+1+j) %5)}))));
            coeffs := apply(5, i -> H4bcoeffs(getPerm(Hats#i#1, indexOfHyp), getPerm(Hats#((i-1)%5)#0, indexOfHyp), getPerm(Hats#((i+1)%5)#0, indexOfHyp)));
            if debugLevel > 5 then print("coeffs: " | net coeffs | ", hats:" | net Hats);
            apply(5, i -> (
                cols := {eps,hashMap(Hats#i#1,0), hashMap(Hats#i#1,1), hashMap(Hats#(i-1)#0,0), hashMap(Hats#(i-1)#1,1), hashMap(Hats#((i+1)%5)#0,0), hashMap(Hats#((i+1)%5)#1,1)};
                sum(#cols, j -> coeffs#i#j*cols#j)
            )))), (a,b) -> a|b); 
        H := matrix {{Hminus} | H3rels} | H4arels | H4brels;
        if debugLevel > 2 then print("Presentation matrix H: " | toString H);
        if debugLevel > 0 then print("All relations found. Computing Smith normal form for " | toString numrows H | " x " | toString numcols H | " matrix ...");
        (g, ch) := myMinPres H;
        eps = ch_{0} % g;
        hexes := hexesFromPairs(g, eps, apply(u, i -> {ch_{i+1}, ch_{i+u+1}}));
    ) else (
        G = ZZ^(#bases M + 1);
        eps = matrix G_{0};
        signPerm := s -> if det ((id_(ZZ^(#M_*)))_s)^(sort s) == 1 then 0 else 1;
        basesMap := hashTable apply(#bases M, i -> (bases M)#i => i+1);
        maxRankNonbases := select(nonbases M, N -> rank_M N == rank M - 1)/toList;
        trivialCrossRatios := matrix{flatten for N in maxRankNonbases list (
            C := toList fundamentalCircuit(M, set N, N#0);
            D := toList fundamentalCircuit(dual M, M.groundSet - N, last toList(M.groundSet - N));
            flatten table(#C-1, #D-1, (i,j) -> (
                I := N - set{C#-1, C#i};
                crossRatioIndices := {I|{C#-1,D#-1}, I|{C#i,D#j}, I|{C#-1,D#j}, I|{C#i,D#-1}};
                sum(crossRatioIndices/signPerm)*eps + matrix sum apply(crossRatioIndices_{0,1}, b -> G_(basesMap#(set b))) - matrix sum apply(crossRatioIndices_{2,3}, b -> G_(basesMap#(set b)))
            ))
        )};
        if trivialCrossRatios == 0 then trivialCrossRatios = map(ZZ^(#bases M+1),ZZ^0,0);
        if debugLevel > 0 then << "#trivialCrossRatios: " << numcols trivialCrossRatios << endl;
        B := sort toList first bases M;
        D = sort toList (M.groundSet - B);
        zeroPos := apply(D, d -> (C = fundamentalCircuit(M, set B, d); select(toList(0..<r), i -> not member(B#i, C))));
        BG := graph(B | D, flatten apply(#D, i -> apply(B - set(B_(zeroPos#i)), j -> {j, D#i})));
        onePos := (edges kruskalSpanningForest BG)/toList/sort;
        if debugLevel > 0 then << "Spanning forest: " << onePos << endl;
        imDegMap := matrix({G_1} | apply(onePos, p -> G_(basesMap#(set B + set p - (set B*set p)))));
        (g, ch) = myMinPres (2*eps | trivialCrossRatios | imDegMap);
        eps = ch_{0} % g;
        if debugLevel > 0 then << "Finding all U24 minors..." << endl;
        E := toList M.groundSet;
        U := uniformMatroid(2,4);
        dbgLevelStore = debugLevel;
        debugLevel = 0;
        U24minors = apply(allMinors(M, U), p -> {p#0, E - p#0 - p#1});
        debugLevel = dbgLevelStore;
        u = #U24minors;
        if debugLevel > 0 then << u << " U24 minors found. Generating hexagons..." << endl;
        hexes = hexesFromPairs(g, eps, apply(U24minors, p -> (
            l := {set{p#1#0, p#1#1}, set{p#1#2, p#1#3}, set{p#1#0, p#1#2}, set{p#1#1, p#1#3}, set{p#1#0, p#1#3}, set{p#1#1, p#1#2}};
            l = apply(l, q -> ch_(basesMap#(p#0 + q)));
            {l#0 + l#1 - l#2 - l#3, l#4 + l#5 - l#2 - l#3}/matrix
        )));
        genTable = basesMap;
    );
    new Foundation from {
        symbol multiplicativeGroup => coker g,
        symbol epsilon => eps,
        symbol hexagons => hexes,
        cache => new CacheTable from {"pruningMap" => ch, "genTable" => genTable, "numU24minors" => u, "strategy" => opts.Strategy}
    }
    )
)

-- Morphisms

hexTypes = method()
hexTypes (Pasture, Boolean) := List => (P, doTally) -> (
    A := presentation P.multiplicativeGroup;
    F3 := select(P.hexagons, h -> #unique flatten h == 1);
    D := select(P.hexagons - set F3, h -> any(h, p -> #unique p == 1));
    H := select(P.hexagons - set F3 - set D, h -> (p := unique flatten h; #p == 2 and all(p, e -> 3*e % A == P.epsilon)));
    U := P.hexagons - set F3 - set D - set H;
    if doTally then hashTable {("U", #U), ("D", #D), ("H", #H), ("F3", #F3)} else {U, D, H, F3}
)
hexTypes Pasture := HashTable => P -> hexTypes(P, true)

freePartPasture = method()
freePartPasture Pasture := List => P -> (
    A := presentation P.multiplicativeGroup;
    positions(toList(0..<numrows A), i -> A^{i} == 0)
)

-- changeBase = (b, n) -> (
    -- if n < b then return {(0, n)};
    -- k := floor(log_b n);
    -- a := floor(n/b^k);
    -- {(k, a)} | changeBase(b, n - a*b^k)
-- )

-- fullRankSublattice1 = method(Options => {Order => 2, Shuffle => false})
-- fullRankSublattice1 Pasture := List => opts -> P -> (
    -- if P.cache#?"sublattice1" then P.cache#"sublattice1" else P.cache#"sublattice1" = (
        -- rowIndices := freePartPasture P;
        -- perm := if opts.Shuffle then random else reverse;
        -- projections := perm apply(P.hexagons/first, pair -> {pair#0^rowIndices, pair#1^rowIndices}); -- first two pairs seem not in general position..
        -- r := #rowIndices;
        -- s := rank (matrix{flatten flatten P.hexagons})^rowIndices;
        -- L := ZZ^r;
        -- goodPairs := {};
        -- for pair in projections do (
            -- Q := L/image matrix{pair};
            -- if rank Q == rank L - 2 then ( L = Q; goodPairs = append(goodPairs, pair); );
            -- if rank L <= r - s + 1 then break;
        -- );
        -- if debugLevel > 5 then print(rank L, goodPairs); 
        -- if rank L == r - s then return {goodPairs, {}};
        -- if rank L > r - s + 2 then error "Could not find enough good fundamental pairs. Try again with `Shuffle => true'"; -- need rank L <= 2.
        -- goodMatrix := matrix {flatten goodPairs};
        -- allExtraCols := flatten for S in subsets(projections - set goodPairs, rank L) list (
            -- E := matrix {flatten S};
            -- Q := L/image E;
            -- extraCols := {};
            -- if rank Q == r - s then (
                -- extraCols = for t in subsets(numcols E, rank L) list (
                    -- D := det(goodMatrix | E_t);
                    -- if abs D == 1 then break {(apply(t, i -> E_{i}), D)};
                    -- (apply(t, i -> E_{i}), D)
                -- );
            -- );
            -- extraCols
        -- );
        -- minPair := (-1, infinity);
        -- for p in allExtraCols do (
            -- if gcd(p#1, opts.Order) == 1 then (minPair = p; break);
            -- if p#1 < minPair#1 then minPair = p;
        -- );
        -- {goodPairs, minPair#0}
    -- )
-- )

-- morphisms1 = method(Options => {FindOne => false})
-- morphisms1 (Pasture, Pasture) := List => opts -> (P, P') -> (
    -- Pstar := presentation P.multiplicativeGroup;
    -- P'star := presentation P'.multiplicativeGroup;
    -- freePart := freePartPasture P;
    -- freePart' := freePartPasture P';
    -- torsPart := toList(0..<numrows Pstar) - set freePart;
    -- torsPart' := toList(0..<numrows P'star) - set freePart';
    -- fundPairsP := flatten P.hexagons;
    -- fundEltsP := unique flatten fundPairsP;
    -- fundPairsP' := flatten P'.hexagons;
    -- fundEltsP' := unique flatten fundPairsP';
    -- T := coker(Pstar^torsPart);
    -- T' := coker(P'star^torsPart');
    -- eta := map(ZZ^(numgens T'), ZZ^(#freePart), 0);
    -- eta' := map(ZZ^(#freePart'), ZZ^1, 0);
    -- H := select(abelianGroupHom(T, T'), f -> ((((f | eta) * P.epsilon) || eta') - P'.epsilon) % P'star == 0);
    -- if debugLevel > 0 then print ("number of possible phi is: " | net(#H));
    -- G := fullRankSublattice1(P);
    -- latticeGens1 := apply(G#0, p -> fundPairsP_(position(fundPairsP, q -> {q#0^freePart, q#1^freePart} == p)));
    -- latticeGens2 := apply(G#1, g -> fundEltsP_(position(fundEltsP, q -> q^freePart == g)));
    -- otherHexes := select(P.hexagons, hex -> (all(latticeGens1, p -> not compareHex(p/(e -> e % Pstar), hex))));
    -- otherPairs := otherHexes/first;
    -- if debugLevel > 0 then print ("number of other pairs is: " | net (#otherPairs));
    -- A := matrix {(flatten latticeGens1) | latticeGens2};
    -- B := inverse sub(A^freePart, QQ); -- inverse sub(matrix {(flatten G#0) | G#1}, QQ);
    -- FmodG := minPres coker(A^freePart);
    -- if debugLevel > 0 then print ("Quotient lattice is: "| net FmodG);
    -- K := apply(abelianGroupHom(FmodG, T'), f -> f * transpose matrix(FmodG.cache.pruningMap));
    -- g := #G#0 + #G#1;
    -- if debugLevel > 0 then print ("Trying " | net(#H * (#fundEltsP')^g) | " candidate morphisms ...");
    -- unique flatten for phi in H list (
        -- phi' := phi || map(ZZ^(#freePart'), ZZ^(#torsPart), 0);
        -- D := phi' * A^torsPart;
        -- N := (#fundEltsP')^g - 1;
        -- flatten while N >= 0 list (		        
            -- s := hashTable changeBase(#fundEltsP', N);
            -- s = apply(g, i -> if s#?(g - 1 - i) then s#(g - 1 - i) else 0);
            -- N = N - 1;
            -- candidates := apply(#G#0, i -> (
                -- e := fundEltsP'#(s#i);
                -- apply(select(fundPairsP', p -> member(e,p)), p -> matrix{if e == p#1 then reverse p else p})
            -- )) | apply(#G#1, i -> {fundEltsP'#(s#(#G#0+i))});
            -- candidates = unique if #candidates == 0 then {map(ZZ^(numrows P'star), ZZ^0, 0)} else fold(candidates, (a, b) -> flatten table(a, b, (i, j) -> i|j));
            -- if debugLevel > 1 and #candidates > 1 then print ("Testing " | net(#K*#candidates) | " sub-candidates ...");
            -- flatten for C in candidates list (
                -- E := (C - D) * B;
                -- torsE := subTorsion(E^torsPart', T');
                -- if torsE === false then continue;
                -- freeE := try sub(E^freePart', ZZ);
                -- if freeE === null then continue;
                -- for psi in K list ( 
                    -- M := phi' | ((torsE + psi) || freeE);
                    -- if not all(otherPairs, p -> any(P'.hexagons, h -> compareHex({M*p#0 % P'star, M*p#1 % P'star}, h))) then continue;
                    -- if opts.FindOne then return M else M 
                -- )
            -- )
        -- )
    -- )
-- )

subTorsion = method()
subTorsion (Matrix, Module) := Matrix => (X, G) -> ( 
    -- attempts to substitute a matrix over QQ into a finite abelian group G (column by column)
    -- assumes G is given by a minimal presentation
    -- number of rows of X should equal numgens G
    matrix for i to (numcols mingens G) - 1 list (
        n := (presentation G)_(i,i);
        for j to (numcols X) - 1 list (
            x := X_(i,j);
            (a, b) := (numerator x, denominator x);
            if gcd(b, n) != 1 then return false;
            for k to b-1 do if (a+n*k)%b == 0 then break ((a+n*k)//b) % n
        )
    )
)

TEST ///
X1 = matrix {{1/3},{1/5}}
X2 = matrix {{1/3},{3/2}}
X3 = X1 | X1
G = coker diagonalMatrix{2,6}
assert(subTorsion(X1,G) == matrix{{1},{5}})
assert(subTorsion(X2,G) == false)
assert(subTorsion(X3,G) == matrix{{1,1},{5,5}})
assert(subTorsion(matrix{{-1/5}}, coker matrix{{2}}) == matrix{{1}})
///

abelianGroupHom = method()
abelianGroupHom (Module, Module) := List => (G1, G2) -> (
    H := minPres Hom(G1, G2);
    if H == 0 then return {map(ZZ^(numgens G2), ZZ^(numgens G1), 0)};
    ords := apply(numgens H, i -> (presentation H)_(i,i));
    homElts := apply(toList(fold(apply(ords, a -> set(0..<a)), (a,b) -> a**b)), s -> transpose matrix {{deepSplice s}});
    homElts/(f -> matrix homomorphism(H.cache.pruningMap * map(H, ZZ^1, f)))
)

TEST ///
G1 = coker diagonalMatrix{2,6}
G2 = coker diagonalMatrix{2}
G3 = coker diagonalMatrix{5}
assert(#abelianGroupHom(G1,G1) == 48)
assert(#abelianGroupHom(G1,G2 ++ G3) == 4)
assert(#abelianGroupHom(G1,G3) == 1)
///

fundEltPartners = method()
fundEltPartners (List, Thing) := List => (L, A) -> (
    unique for p in L list if p#0 === A then p#1 else if p#1 === A then p#0 else continue
)
fundEltPartners (Pasture, Thing) := List => (P, e) -> (
    H := if P.cache#?"partnerTable" then P.cache#"partnerTable" else P.cache#"partnerTable" = (
        FP := unique flatten P.hexagons;
        FE := unique flatten FP;
        hashTable apply(FE, e -> e => fundEltPartners(FP, e))
    );
    if H#?e then H#e else {}
)

fullRankSublattice = method()
fullRankSublattice Pasture := List => P -> (
    if P.cache#?"sublattice" then P.cache#"sublattice" else P.cache#"sublattice" = (
        n := numrows presentation P.multiplicativeGroup;
        freePart := freePartPasture P;
        torsPart := toList(0..<n) - set freePart;
        S := {}; -- list of lists of type 4 hexagons
        s := rank (matrix{flatten(P.hexagons/first)})^freePart;
        currentPairs := {};
        while true do (
            A := if #currentPairs == 0 then map(ZZ^n,ZZ^0,0) else matrix{flatten(currentPairs/first/last)};
            r := rank A^freePart;
            if r == s then break;
            (type1Pair, type2Pairs, type3Pairs, type4Hexes) := (null, {}, {}, {});
	    for h in P.hexagons - set(currentPairs/last) - set flatten S do (
		t := {rank((A | h#0#0)^freePart), rank((A | h#0#1)^freePart), rank((A | h#0#0 | h#0#1)^freePart)};
		if set t === set{r} then type4Hexes = append(type4Hexes, h);
		if type1Pair =!= null then continue;
		if set t === set{r, r+1} then type1Pair = {{sort t, if t === {r,r+1,r+1} then h#0 else reverse h#0}, h}
		else if set t === set{r+1} then ( -- hexagon with type 2 pair may also have type 1 pair
		    d := {rank((A | h#1#0)^freePart), rank((A | h#1#1)^freePart)};
		    if set d === set{r,r+1} then type1Pair = {{{r, r+1, r+1}, if d === {r,r+1} then h#1 else reverse h#1}, h}
		    else type2Pairs = append(type2Pairs, {{t, h#0}, h});
		) else if set t === set{r+1, r+2} then type3Pairs = append(type3Pairs, {{t, h#0}, h});
	    );
	    S = append(S, type4Hexes);
	    newPair := if type1Pair =!= null then type1Pair
	    else if #type2Pairs > 0 then type2Pairs#0
            else if #type3Pairs > 0 then ( S = append(S, {}); type3Pairs#0 )
            else break;
            currentPairs = append(currentPairs, newPair);
        );
        S = append(S, P.hexagons - set(currentPairs/last) - set flatten S);
        G := currentPairs/first;
        g := #freePart;
        L := if g == 0 then map(ZZ^n, ZZ^0, 0) else matrix{flatten for i to #G-1 list if G#i#0#2 == 1 + G#i#0#1 then G#i#1 else G#i#1#1};
        k := 0;
        z := map(ZZ^(#torsPart), ZZ^1, 0);
        checkPairs := {};
        generatingRules := flatten for i to #G-1 list (
            if G#i#0#2 == 1 + G#i#0#1 then ( -- type 3 pair
                k = k+1;
                {{z,0},{z,1}}
            ) else ( -- type 1/2 pair
                B := G#i#1#0;
                isType2Pair := G#i#0#0 == G#i#0#1;
                if isType2Pair then B = B | G#i#1#1;
                coeff = (gens ker((L_(toList(0..<i+k)) | B)^freePart))_{0};
                if isType2Pair and abs((flatten entries coeff)#-2) != 1 then (
                    L = submatrix(L, , toList(0..<i+k)) | G#i#1#0 | submatrix(L, , toList(i+k+1..<g));
                    coeff = coeff^{0..<i+k-1,i+k+1,i+k};
                );
                if abs((flatten entries coeff)#(if isType2Pair then -2 else -1)) != 1 then checkPairs = append(checkPairs, G#i#1);
                {{(L_(toList(0..<i+k)) | B)^torsPart*coeff, coeff}}
            )
        );
        type4Data := apply(#S, i -> apply(S#i, h -> apply(h#0, e -> (
            B = submatrix(L, , toList(0..<i));
            (BQQ, eQQ) := (sub(B^freePart, QQ), sub(e^freePart, QQ));
            C := flatten entries(eQQ // BQQ);
            c := if #C == 0 then -1 else lcm(C/denominator);
            coeffs := lift(c*(transpose matrix{C}), ZZ);
            (B*coeffs - c*e, coeffs, c)
        ))));
        checkPairs = checkPairs | delete(null, flatten apply(#S, i -> apply(#(S#i), j -> if any(type4Data#i#j, t -> abs last t != 1) then S#i#j#0)));
        P.cache#"latticeGensMatrix" = L;
        P.cache#"generatingRules" = generatingRules;
        P.cache#"checkPairs" = checkPairs;
        P.cache#"type4Data" = type4Data;
        P.cache#"quotientLattice" = minPres coker(L^freePart);
        G
    )
)

morphisms = method(Options => {FindOne => false, FindIso => false}) -- Assumes fundamental elements of P1 generate P1.multiplicativeGroup
morphisms (Pasture, Pasture) := List => opts -> (P1, P2) -> (
    P1star := presentation P1.multiplicativeGroup;
    P2star := presentation P2.multiplicativeGroup;
    fundPairsP1 := unique flatten P1.hexagons;
    fundEltsP1 := unique flatten fundPairsP1;
    fundPairsP2 := unique flatten P2.hexagons;
    fundEltsP2 := unique flatten fundPairsP2;
    fundPairsP2unordered := unique(fundPairsP2 | fundPairsP2/reverse);
    fundPairsP2set := set(fundPairsP2/set);
    if opts.FindIso then (
        if not(#P1.hexagons == #P2.hexagons and #fundEltsP1 == #fundEltsP2 and P1star == P2star) then (
            if debugLevel > 0 then print "Pastures have different numerical data!";
            return {};
        ) else if P1 == P2 then return {pastureMorphism(P1, P2, id_(P1.multiplicativeGroup))};
    );
    freePart1 := freePartPasture P1;
    freePart2 := freePartPasture P2;
    (r1, r2) := (#freePart1, #freePart2);
    (n1, n2) := (numrows P1star, numrows P2star);
    torsPart1 := toList(0..<n1) - set freePart1;
    torsPart2 := toList(0..<n2) - set freePart2;
    
    -- Fetch sublattice data
    G := fullRankSublattice P1;
    A := P1.cache#"latticeGensMatrix";
    generatingRules := P1.cache#"generatingRules";
    torsLatticeGens := generatingRules/first;
    checkPairs := P1.cache#"checkPairs";
    type4Data := P1.cache#"type4Data";
    B := inverse sub(A^freePart1, QQ);
    
    -- Prepare torsion maps
    T1 := coker(P1star^torsPart1);
    T2 := coker(P2star^torsPart2);
    eta1 := map(ZZ^(numgens T2), ZZ^r1, 0);
    eta2 := map(ZZ^r2, ZZ^1, 0);
    H := select(abelianGroupHom(T1, T2), f -> ((((f | eta1) * P1.epsilon) || eta2) - P2.epsilon) % P2star == 0);
    H = apply(H, phi -> phi || map(ZZ^r2, ZZ^(#torsPart1), 0));
    Q := P1.cache#"quotientLattice";
    K := apply(abelianGroupHom(Q, T2), f -> f * transpose matrix(Q.cache.pruningMap));
    T0P2 := if T2 == 0 then map(ZZ^(numrows K#0), ZZ^(numcols K#0), 0) else null;
    if debugLevel > 0 then print("(#phi, #psi): " | net(#H, #K));
    z0 := map(ZZ^n2, ZZ^0, 0);
    
    -- Main loop
    pastureMorphism(P1, P2, unique flatten for phi in H list (
        D := phi * A^torsPart1;
        checkType4 = apply(#type4Data, i -> apply(type4Data#i, t -> {phi*t#0#0^torsPart1, phi*t#1#0^torsPart1}));
        if not all(checkType4#0, p -> any(fundPairsP2, pair -> set pair === set{p#0 % P2star, p#1 % P2star})) then continue;
        delta := apply(r1, i -> phi * torsLatticeGens#i);
        C0 := z0;
        level := 0; -- level should always be the level of current node (previously: == numcols C0)
        candidates := new MutableList from {{z0}};
        flatten while #(candidates#0) > 0 list (
            if #(candidates#level) == 0 then (
                C0 = C0_{0..<numcols C0-1};
                level = level - 1;
                candidates = drop(candidates, -1);
                candidates#level = drop(candidates#level, 1);
                continue;
            ) else if level < r1 then (
                C0 = C0 | candidates#level#0;
                rule := last generatingRules#level;
                newCandidates := if rule === 0 then fundEltsP2 -- first member of type 3
                else if rule === 1 then fundEltPartners(fundPairsP2, candidates#level#0) -- second member of type 3
                else ( -- type 1/2 pairs
                    coeff := flatten entries rule;
                    isType2Pair := #coeff == level+2;
                    (alpha, beta) := if isType2Pair then (coeff#-2, coeff#-1) else (coeff#-1, 0);
                    w := (delta#level - C0*transpose matrix{drop(coeff, if isType2Pair then -2 else -1)}) % P2star;
                    if (abs(alpha), beta) == (1,0) then fundEltPartners(P2, alpha*w % P2star)
                    else unique flatten apply(fundPairsP2unordered, pair -> if (alpha*pair#0 + beta*pair#1) % P2star === w then {pair#1} else {})
                );
                if opts.FindIso then (
                    newCandidates = select(newCandidates, c -> rank(C0 | c) == 1 + numcols C0);
                );
                newCandidates = select(newCandidates, c -> (
                    all(#type4Data#(level+1), i -> (
                        data := type4Data#(level+1)#i;
                        checkPair := checkType4#(level+1)#i;
                        v := set apply(2, j -> (checkPair#j + (C0 | c)*data#j#1) % P2star);
                        any(fundPairsP2, p -> set{p#0*data#0#2 % P2star, p#1*data#0#2 % P2star} === v)
                    ))
                ));
                level = level + 1;
                candidates#level = newCandidates;
                if debugLevel > 0 then << "\rSearch tree: " << toString apply(#candidates, i -> #candidates#i) << flush;
                continue;
            ) else flatten while #(candidates#r1) > 0 list ( -- level == r1
                C := C0 | candidates#r1#0;
                candidates#r1 = drop(candidates#r1, 1);
                E := (C - D) * B;
                torsE := if T0P2 =!= null then T0P2 else subTorsion(E^torsPart2, T2);
                if torsE === false then continue;
                freeE := try sub(E^freePart2, ZZ);
                if freeE === null then continue;
                for psi in K list (
                    M := phi | ((torsE + psi) || freeE);
                    if opts.FindIso and abs det M != 1 then continue;
                    -- if not all(checkPairs, p -> any(P2.hexagons, h -> compareHex({M*p#0 % P2star, M*p#1 % P2star}, h))) then continue;
                    if not all(checkPairs, p -> member(set {M*p#0 % P2star, M*p#1 % P2star}, fundPairsP2set)) then continue;
                    if opts.FindOne or opts.FindIso then return {pastureMorphism(P1, P2, M)} else M
                )
            )
        )
    ))
)

areIsomorphic (Pasture, Pasture) := Boolean => (P, P') -> #morphisms(P, P', FindIso => true) > 0

isoTypes = method()
isoTypes List := List => L -> (
    isoClasses := {};
    for P in L do (
        isNewIsoClass := for c in isoClasses do if areIsomorphic(c, P) then break false;
        if isNewIsoClass =!= false then isoClasses = append(isoClasses, P);
    );
    isoClasses
)

TEST /// -- rank 2 uniform matroids (k-regular partial fields)
U = foundation uniformMatroid(2,4)
assert Equation((#freePartPasture U, #U.hexagons), (2, 1))
V = foundation uniformMatroid(2,5)
assert Equation((#freePartPasture V, #V.hexagons), (5, 5))
U26 = foundation uniformMatroid(2,6)
assert Equation((#freePartPasture U26, #U26.hexagons), (9, 15))
///

TEST /// -- Q6
Q6 = matroid(toList(0..5), {{0,1,2},{0,3,4}}, EntryMode => "nonbases")
U35 = uniformMatroid_3 5
V = foundation U35
assert(hasMinor(Q6, U35))
assert(areIsomorphic(foundation Q6, V))
///

TEST /// -- Non-Fano
NF = specificMatroid "nonfano"
D = foundation NF
assert(hexTypes D === hashTable {"H"=>0,"D"=>1,"F3"=>0,"U"=>0})
D2 = foundation(NF ++ NF, Strategy => "Hyperplanes")
assert(hexTypes D2 === hashTable {"H"=>0,"D"=>2,"F3"=>0,"U"=>0})
S = specificPasture "sign"
assert Equation(1, #morphisms(D, S))
assert Equation(1, #morphisms(D2, S))
///

TEST /// -- MacLane matroid
AG23 = affineGeometry (2,3)
M = AG23 \ set{0}
F = foundation M
H = pasture([x], "-x^3, x+x^5")
assert(F == foundation AG23)
assert areIsomorphic(F, H)
assert Equation(0, #morphisms(F, specificPasture "sign"))
///

TEST /// -- orientations of Pappus, non-Pappus
P = foundation specificMatroid "pappus"
Q = foundation specificMatroid "nonpappus"
S = specificPasture "sign"
assert Equation(18, #morphisms(P, S))
assert Equation(36, #morphisms(Q, S))
///

TEST /// -- Betsy-Ross
(E, H) = (toList(0..10), {{0,1},{0,2,5,6},{0,3,8,9},{0,4},{0,7,10},{1,2},{1,3,6,7},{1,4,5,9},{1,8,10},{2,3},{2,4,7,8},{2,9,10},{3,4},{3,5,10},{4,6,10},{5,7},{5,8},{6,8},{6,9},{7,9}})
BR = dual matroid(E, H/(h -> E - set h), EntryMode => "circuits")
G = pasture([t], "t + t^2")
assert areIsomorphic(G, foundation BR)
homSet = morphisms(G, G)
assert Equation(2, #homSet)
assert (tally(homSet/det) === new Tally from {(1,1),(-1,1)})
assert Equation(2, #morphisms(G, specificPasture "sign"))
assert Equation(2, #morphisms(G, pasture GF 4))
assert Equation(1, #morphisms(G, pasture GF 5))
///

TEST /// -- Isomorphism check
M = specificMatroid "nonpappus"
nP = foundation M
phi = random M_*
N = matroid(M_*, (nonbases M)/(n -> n/(e -> phi#e)), EntryMode => "nonbases")
assert areIsomorphic(M, N)
F = foundation N
assert areIsomorphic(nP, F)
///

TEST /// -- R9B matroid, cf. https://doc.sagemath.org/html/en/reference/matroids/sage/matroids/catalog.html#sage.matroids.catalog.R9B
R9B = matroid(toList(0..8),{{0,1,2,7},{0,1,3,4},{0,1,6,8},{0,2,4,6},{0,3,5,8},{0,4,7,8},{1,2,3,5},{1,2,4,8},{1,3,7,8},{1,4,5,7},{2,3,6,7},{3,4,6,8},{5,6,7,8}}, EntryMode => "nonbases")
F = foundation R9B
assert (hexTypes F === hashTable {"H"=>1,"D"=>1,"F3"=>1,"U"=>12})
assert all(flatten flatten F.hexagons, e -> e != 0)
assert all({5,7,8,9,11}, q -> #morphisms(F, pasture GF q) == 0)
///

TEST ///-- Brettel partial field I
I = pasture([z,t], "z + z^2, -z^2 + t, z^4 + z*t")
P = foundation specificMatroid "pappus"
assert Equation(18, #morphisms(P, I))
///

--Natural map from the foundation of minor
hyperplaneCorrespondenceTable = method()
hyperplaneCorrespondenceTable (Matroid, ZZ, String) := HashTable => (M, e, mode) -> (
    N := if mode === "delete" then M \ set{e} else M / set{e};
    (HM, HN) := (hyperplanes M, hyperplanes N);
    hashTable apply(HN, h -> ( H := set apply(toList h, i -> if i<e then i else i+1); (h, if member(H, HM) then H else H + set{e})))
)

inducedMapFromMinor = method()
inducedMapFromMinor (Matroid, ZZ, String) := PastureMorphism => (M, e, mode) -> (
    N := if mode === "delete" then M \ set{e} else M / set{e};
    F := foundation M;
    G := foundation N;
    H := hyperplaneCorrespondenceTable(M, e, mode);	
    if numgens F.multiplicativeGroup == 0 then pastureMorphism(G, F, map(F.multiplicativeGroup, G.multiplicativeGroup, 0)) else (
    	inducedMinors := apply(sort(pairs G.cache#"genTable" /toList, last)/first/toList, U -> 1 + (F.cache#"genTable")#(set apply(U, h -> H#h)));
    	B := id_(ZZ^(numgens F.multiplicativeGroup))_{0};
    	B = B | (F.cache#"pruningMap")_(inducedMinors | apply(inducedMinors, i -> i + F.cache#"numU24minors"));
    	C := id_(ZZ^(numgens G.multiplicativeGroup)) // (G.cache#"pruningMap");
    	pastureMorphism(G, F, B*C)
    )
)

--Positive Orientability (cf. Thm 5.2 in https://arxiv.org/pdf/1310.4159.pdf)
isNonCrossing = method()
isNonCrossing (List, List) := Boolean => (C, D) -> (  -- assumes C and D are disjoint
    (minC, maxC, minD, maxD) := (min C, max C, min D, max D);
    (minC < minD and maxC > maxD) or (minD < minC and maxD > maxC)
)
isNonCrossing (Set, Set) := Boolean => (C, D) -> isNonCrossing(toList C, toList D)

isPositivelyOriented = method()
isPositivelyOriented Matroid := Boolean => M -> (
    all(circuits M, C -> all(select(circuits dual M, D -> #(D * C) == 0), D -> isNonCrossing(C, D)))
)

isPositivelyOrientable = method()
isPositivelyOrientable Matroid := Boolean => M -> (
    any(permutations (#M_*), phi -> isPositivelyOriented matroid(M_*, (circuits M)/(C -> C/(e -> phi#e)), EntryMode => "circuits"))
)

-- Finding representation from pasture morphisms

representation = method()
representation (Matroid, PastureMorphism) := Matrix => (M, phi) -> (
    F := foundation M;
    if source phi =!= F then error "Expected source of phi to equal the foundation of M";
    B := sort toList first bases M;
    (ch, basesMap) := (F.cache#"pruningMap", F.cache#"genTable");
    table(rank M, #M_*, (i,j) -> (
        p := position(B, b -> b === j);
        if p === null then (
            B1 := set B - set{B#i} + set{j};
            if not isDependent(M, B1) then (
                s := (i+position(sort toList B1, b -> b === j))*phi.target.epsilon;
                s + (matrix(phi.map))*ch_{basesMap#B1}
            ) else 0
        ) else ( if i === p then 1 else 0 )
    ))
)

-- isKnownNonzero := f -> f =!= "zero" and sum degree f == 0

-- chooseFundElt := (phix, phiy, eps, perm) -> (
    -- if perm == {0, 0} then phix
    -- else if perm == {1, 0} then phiy
    -- else if perm == {0, 1} then -phiy
    -- else if perm == {1, 1} then eps+phix-phiy
    -- else if perm == {0, 2} then eps+phiy-phix
    -- else if perm == {1, 2} then -phix
-- )

-- representation (Matroid, PastureMorphism) := Matrix => (M, phi) -> (
    -- r := rank M;
    -- n := #M.groundSet;
    -- B := sort toList first bases M;
    -- D := sort toList (M.groundSet - B);
    -- -* sigma := hashTable apply(n, i -> if i < r then (B#i, i) else (D#(r+i), i)); *-
    -- F := M.cache#"foundation";
    -- if phi.source =!= F then error"expected source of phi to be the foundation of M";
    -- z := 0 * phi.target.epsilon;
    -- zeroPos := apply(D, d -> (C := fundamentalCircuit(M, B, d); select(toList(0..<r), i -> not member(B#i, C))));
    -- -* K := completeMultipartiteGraph {r, n-r};
    -- if r > n-r then K = graph apply(edges K, e -> set (reverse toList(0..<n))_(toList e));
    -- G := deleteEdges(K, flatten apply(#D, i -> apply(zeroPos#i, j -> {j, r+i}))); *-
    -- G := graph(B | D, flatten apply(#D, i -> apply(B - set(B_(zeroPos#i)), j -> {j, D#i})));
    -- onePos := (edges spanningForest G)/toList/sort;
    -- m := r*(n-r) - #(flatten zeroPos) - #onePos;
    -- -* k := -1; *-
    -- y := getSymbol "y";
    -- S := ZZ[y_1..y_(numgens phi.target.multiplicativeGroup), Inverses => true, MonomialOrder => Lex];
    -- varTable := hashTable flatten table(r, n-r, (i, j) -> (i, D#j) => i*#D + j);
    -- x := getSymbol "x";
    -- -* R := ZZ[x_1..x_m, Inverses => true, MonomialOrder => Lex];
    -- R := S[apply(sort keys varTable, k -> x_k), Inverses => true, MonomialOrder => Lex]; *-
    -- R := S[apply(sort keys varTable, k -> x_k)];
    -- J := ideal flatten apply(#D, i -> apply(zeroPos#i, j -> R_(varTable#(j, D#i))));
    -- H := new MutableHashTable from for p in flatten table(r, n-r, identity) list (((p#0, D#(p#1)),
	-- if member(p#0, zeroPos#(p#1)) then "zero"
	-- else if member({B#(p#0),D#(p#1)}, onePos) then (J = J + ideal(R_(varTable#(p#0, D#(p#1))) - 1); z)
	-- else R_(varTable#(p#0, D#(p#1)))
	-- -* else (
	    -- k = k+1;
	    -- R_k
	-- )) *-
    -- ));
    -- unknownPos := select(keys H, k -> if H#k === "zero" then false else sum degree H#k > 0); print(unknownPos);
    -- while true do (
	-- for p in unknownPos do (
	    -- rowIndices := select(toList(0..<r), i -> isKnownNonzero H#(i,p#1));
	    -- p1 := for s in flatten table(rowIndices, toList (0..<n-r), (i,j) ->(i, D#j)) do if all({H#(p#0,s#1), H#s}, isKnownNonzero) then break s;
	    -- if p1 === null then continue;
	    -- I := set B - set{B#(p#0), B#(p1#0)};
	    -- hyps := apply({p#0, p1#0, p#1, p1#1}, j -> position(hyperplanes M, h -> isSubset(I + set{j}, h)));
	    -- Hyps := (hyperplanes M)_hyps;
	    -- perm := getPerm(hyps, identity);
	    -- H#p = if #unique Hyps == 4 then (
	    	-- i := F.cache#"genTable"#(set Hyps);
		-- im := (matrix phi.map) * ((F.cache#"pruningMap")_{i,i+F.cache#"numU24minors"});
		-- crossRatio := chooseFundElt(im_{0}, im_{1}, phi.target.epsilon, perm);
		-- J = J + ideal (R_(varTable#p) * R_(varTable#p1) -  S_(flatten entries crossRatio) * R_(varTable#(p1#0,p#1)) * R_(varTable#(p#0, p1#1)));
		-- crossRatio + sum({H#(p1#0, p#1), H#(p#0, p1#1), -H#p1})
	    -- ) else (
	    	-- J = J + ideal (R_(varTable#p) * R_(varTable#p1) -  R_(varTable#(p1#0,p#1)) * R_(varTable#(p#0, p1#1)));
	    	-- sum({H#(p1#0, p#1), H#(p#0, p1#1), -H#p1})
    	    -- );
	    -- if debugLevel > 5 then (
		-- print(matrix table(r, n-r, (i, j) -> if H#(i,D#j) === "zero" then 0_S else if instance(H#(i,D#j), Matrix) then S_(flatten entries H#(i,D#j)) else H#(i,D#j)));
		-- <<Hyps<<", "<<hyps<<", "<<(#unique Hyps == 4)<<im<<perm<<endl;
            -- );
	-- );    
	-- newUnknowns := select(keys H, k -> if H#k === "zero" then false else sum degree H#k > 0);
	-- if #newUnknowns == #unknownPos then break;
        -- unknownPos = newUnknowns;
	
    -- );
    -- A := matrix table(r, n-r, (i, j) -> if H#(i,D#j) === "zero" then 0_R else if instance(H#(i,D#j), Matrix) then R_(flatten entries H#(i,D#j)) else H#(i,D#j));
    -- shift := 0;
    -- (matrix {apply(n, i -> if member(i, B) then (shift = shift+1; matrix (R^r)_{position(toList(0..<r),j -> B#j == i)}) else A_{i-shift})}, J)
-- )

representations = method(Options => options morphisms)
representations (Matroid, GaloisField) := List => opts -> (M, k) -> (
    -- reps := apply(morphisms(foundation M, pasture k, opts), representation_M);
    -- apply(reps, A -> matrix table(rank M, #M_*, (i,j) -> (
    maps := morphisms(foundation M, pasture k, opts);
    apply(maps/representation_M, A -> matrix table(rank M, #M_*, (i,j) -> (
        if A#i#j === 0 then 0_k
        else if A#i#j === 1 then 1_k
        else (k.PrimitiveElement)^(if A#i#j == 0 then 0 else (A#i#j)_(0,0))
    )))
)

-- (Quasi-)Fixed/cofixed elements

isQuasiFixed = (M, e) -> coker (inducedMapFromMinor(M, e, "delete")).map == 0

isQuasiCofixed = (M, e) -> isQuasiFixed(dual M, e)

cosimpleMatroid = M -> dual simpleMatroid dual M

isQuasiFree = M -> (
    if not is3Connected M then return false;
    all(select(toList(0..<#M_*), e -> isQuasiFixed_M e), e -> not is3Connected cosimpleMatroid (M\{e})) and  all(select(toList(0..<#M_*), e -> isQuasiCofixed_M e), e -> not is3Connected simpleMatroid (M/{e}))
)

-- Special classes of matroids

spike = method()
spike (ZZ, List) := Matroid => (r, C3) -> (
    E := toList(0..2*r);
    C1 := toList apply(r, i -> {0, 2*i+1, 2*(i+1)});
    C2 := apply(subsets(r, 2), p -> {2*p#0+1, 2*(p#0+1), 2*p#1+1, 2*(p#1+1)});
    C := C1 | C2 | C3;
    C4 := select(subsets(E, r+1), s -> not any(C, c -> isSubset(c, s)));
    matroid(E, C | C4, EntryMode => "circuits")
)
spike ZZ := Matroid => r -> spike(r, {})

swirl = method()
swirl ZZ := Matroid => r -> (
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
wheel ZZ := Matroid => r -> matroid wheelGraph (r+1)

whirl = method()
whirl ZZ := Matroid => r -> relaxation wheel(r+1)

-- Note: for wheels/whirls, computing foundations via Strategy => "Hyperplanes" is faster, but the opposite is true for spikes/swirls

end--

-- specific matroids
F7 = specificMatroid "fano"
T8 = matroid (id_((ZZ/3)^4) | matrix table (4, 4, (i,j) -> if i == j then 0_(ZZ/3) else 1)) -- T8
C4 = matroid(toList(0..3), {{0,1}}, EntryMode => "nonbases")
C5 = matroid(toList(0..4), {{0,1,2}}, EntryMode => "nonbases")
P6 = matroid(toList(0..5), {{0,1,2}}, EntryMode => "nonbases")
Q6 = matroid(toList(0..5), {{0,1,2},{0,3,4}}, EntryMode => "nonbases")
R1 = matroid(toList(0..6), {{0,1,2,3}}, EntryMode =>"nonbases")
R2 = matroid(toList(0..6), {{0,1,2},{4,5,6}}, EntryMode => "nonbases")
R3 = matroid(toList(0..6), {{0,1,2}}, EntryMode => "nonbases")
Q8 = matroid(toList(0..<8), {set {0,1,2,3},set {0,1,4,5},set {1,2,5,6},set {2,3,6,7},set {0,3,4,7},set {4,5,6,7},set {0,1,6,7},set {1,2,4,7},set {2,3,4,5},set {0,3,5,6},set {0,2,4,6}}, EntryMode => "nonbases")
L8 = matroid({0,1,2,3,4,5,6,7}, {set{0,1,2,3},set{0,1,4,5},set{1,2,5,6},set{2,3,6,7},set{0,3,4,7},set{4,5,6,7},set{0,7,2,5},set{1,6,3,4}}, EntryMode => "nonbases")
Q8 = matroid({0,1,2,3,4,5,6,7}, {set{0,1,2,3},set{0,1,4,5},set{1,2,5,6},set{2,3,6,7},set{0,3,4,7},set{4,5,6,7}, EntryMode => "nonbases")
nonP = matroid(toList(0..8), {{0,1,2},{0,4,8},{0,3,7},{1,3,6},{1,5,8},{2,4,6},{2,5,7},{6,7,8}}, EntryMode => "nonbases")
R9A = matroid(toList(0..8),{{0,1,2,7},{0,1,3,4},{0,1,5,8},{0,2,3,8},{0,2,4,6},{0,3,6,7},{0,4,5,7},{1,2,3,5},{1,3,7,8},{1,4,6,8},{2,4,7,8},{3,4,5,8},{5,6,7,8}}, EntryMode => "nonbases")
M = matroid(toList(0..<7),{set {0, 1, 2}, set {0, 3, 4}, set {1, 3, 5}, set {2, 4, 5}, set {2, 3, 6}}, EntryMode => "nonbases")
N = matroid(toList(0..<8),{set {0, 1, 2, 3}, set {0, 1, 4, 5}, set {2, 3, 4, 5}, set {0, 1, 6, 7}, set {2, 3, 6, 7}, set {4, 5, 6, 7}}, EntryMode => "nonbases")
GF 4; BR = matrix {{1,0,0,1,1,1,1,1,1,1,1},{0,1,0,a,1,a+1,1,0,a+1,a+1,1},{0,0,1,a,a+1,1,0,a+1,a+1,a,a}} -- representation of Betsy-Ross
BRplus = BR | transpose matrix{{1,0,1}} -- foundation is F4
GF 4; D = matrix{{1,0,0,1,a,1,0,a+1,1},{0,1,0,a,a,1,a,1,a+1},{0,0,1,0,1,1,1,1,1}}
GF 4; D = matrix{{1,0,0,1,a+1,1,0,a,1},{0,1,0,a+1,a+1,1,a+1,1,a},{0,0,1,0,1,1,1,1,1}}
M = matroid (matrix{{7:1}} || transpose matrix {{-3,0}, {-3/4,-1}, {3/2,-2}, {-3/4,1}, {3/2,2}, {0,0}, {3,0}}) -- Example 2.2 in paper

-- a class of non-orientable matroids (Bland--Las-Vergnas, Orientability of Matroids, Ex. 3.11)
r = 6
C = apply(subsets(r, 2), p -> p | {p#0 + r, p#1 + r}) | apply(r, i -> delete(i, toList(0..<r)) | {i+r}) | {apply(r, i -> i+r)}
M = matroid(toList(0..<2*r), C | select(subsets(2*r, r+1), S -> not any(C, c -> isSubset(c, S))), EntryMode => "circuits")
elapsedTime morphisms(foundation M, specificPasture "sign")

U = foundation uniformMatroid_2 4
V = foundation uniformMatroid_2 5
F = foundation uniformMatroid_3 6

-- 0 = a, 1 = b, 2 = -b, 3 = eps+a-b, 4 = -a, 5 = eps-a+b
fundEltsU = flatten flatten U.hexagons
toList((set(0..<#fundEltsU))^** 4/deepSplice/toList);
H1 = hashTable{(0,1),(1,0),(2,3),(3,2),(4,5),(5,4)}
elapsedTime quotients = for idx in toList((set(0..<#fundEltsU))^** 4/deepSplice/toList) list (
    l = {0} | idx;
    A = (presentation U.multiplicativeGroup) | matrix{apply(5, i -> fundEltsU_(H1#(l#i)) - fundEltsU_(l#((i+1) % 5)) - fundEltsU_(l#((i-1) % 5)))};
    (g,ch) = smithNormalForm(A, ChangeMatrix => {true, false});
    piv = select(pivots g,ij -> abs g_ij === 1);
    (rows, cols) = (first \ piv, last \ piv);
    (g,ch) = (submatrix'(g,rows,cols),submatrix'(ch,rows,));
    {idx, pasture(g, ch * U.epsilon, U.hexagons/(h -> h/(p -> p/(e -> (ch * e) % g))))}
);
uniQuotients = unique (quotients/last);
netList (uniQuotients/peek)
representative = first select(quotients, l -> (last l) === uniQuotients#0)

U = foundation (uniformMatroid_2 4 ++ uniformMatroid_2 4)
fundEltsU = flatten flatten U.hexagons
H2 = hashTable{(0,1),(1,0),(2,3),(3,2),(4,5),(5,4),(6,7),(7,6),(8,9),(9,8),(10,11),(11,10)}
elapsedTime quotients2 = unique for idx in toList((set(0..<#fundEltsU))^** 4/deepSplice/toList) list (
    if all(idx, i -> i<6) then continue;
    l = {0} | idx;
    A = (presentation U.multiplicativeGroup) | matrix{apply(5, i -> fundEltsU_(H2#(l#i)) - fundEltsU_(l#((i+1) % 5)) - fundEltsU_(l#((i-1) % 5)))};
    (g,ch) = smithNormalForm(A, ChangeMatrix => {true, false});
    piv = select(pivots g,ij -> abs g_ij === 1);
    (rows, cols) = (first \ piv, last \ piv);
    (g,ch) = (submatrix'(g,rows,cols),submatrix'(ch,rows,));
    pasture(g, ch * U.epsilon, unique (U.hexagons/(h -> h/(p -> p/(e -> (ch * e) % g)))))
);
quotients2 = lines get "quotients2.txt" /value;
elapsedTime isoTypes quotients2;
netList(isoClasses/peek)

-- Nathan's spike
n = 4
X = entries id_((ZZ/2)^n) /(r -> transpose matrix{r})
Y = apply(n, i -> sum X - X#i)
E = toList apply(n, i -> X#i) | toList apply(n, i -> Y#i)
fringeBases = flatten flatten apply(subsets(n,2), p -> apply(toList(fold(apply(toList(0..<n) - set p, i -> set{X#i, Y#i}), (a,b) -> a ** b))/deepSplice/toList, s -> {s | {X#(p#0), Y#(p#0)}, s | {X#(p#1), Y#(p#1)}}));
fringeBases = apply(fringeBases, B -> sort apply(B, b -> position(E, e -> e == b)))
hypercube = toList((fold(apply(n, i -> set{i,i+n}), (a,b) -> a**b))/deepSplice/toList/sort)
areIsomorphic(matroid(toList(0..<2*n), fringeBases | hypercube), spike n \ set{0})
indepSet = {{0,1,2,3},{0,1,6,7},{2,3,4,5},{4,5,6,7}}
NS = matroid(toList(0..<2*n), fringeBases | (hypercube - set indepSet))
nonbases NS /toList == {{0,1,2,3},{0,1,4,5},{2,3,4,5},{0,2,4,6},{1,2,5,6},{0,3,4,7},{1,3,5,7},{0,1,6,7},{2,3,6,7},{4,5,6,7}}
NS = matroid(toList(0..<8), {{0,1,2,3},{0,1,4,5},{2,3,4,5},{0,2,4,6},{1,2,5,6},{0,3,4,7},{1,3,5,7},{0,1,6,7},{2,3,6,7},{4,5,6,7}}, EntryMode => "nonbases")
F = foundation NS
G = pasture([z], "z+z^2")
morphisms(G, G)
G = foundation specificMatroid "betsyRoss"
morphisms(F, G)

-- Non-trivial isomorphism check
F = foundation uniformMatroid_3 7
G = foundation uniformMatroid_4 7
F == G
elapsedTime areIsomorphic(F, G)

-- Isomorphism classes of foundations of matroids on 7 elements
r3 = select(allMatroids 7, M -> rank M <= 3);
elapsedTime foundr3 = r3/foundation;
numericalData = tally apply(foundr3, F -> (#freePartPasture F, #F.hexagons))
numericalClasses = apply(keys numericalData, k -> foundr3_(positions(foundr3, F -> k == (#freePartPasture F, #F.hexagons))));
elapsedTime isoTypes foundr3;

-- Isomorphism classes of foundations of matroids on 8 elements
r4 = select(allMatroids 8, M -> rank M <= 4);
elapsedTime foundr4 = r4/foundation;
numericalData = tally apply(foundr4, F -> (#freePartPasture F, #F.hexagons))
numericalClasses = apply(keys numericalData, k -> foundr4_(positions(foundr4, F -> k == (#freePartPasture F, #F.hexagons))));
elapsedTime isoTypes foundr4;

-- single element extensions
linearSubclasses = method()
linearSubclasses Matroid := List => M -> (
    r := rank M;
    hyp := hyperplanes M;
    corank2 := select(flats M, f -> rank_M f == r - 2);
    upSets := apply(corank2, f -> {f,select(hyp, h -> isSubset(f, h))});
    k := 0;
    validClasses := new MutableHashTable;
    H := hyp;
    for h in H do (
	c := set {};
	while (#H > 0) do (
	    c = c + set {h};
	    validClasses#c = 1;
	    H = H - set unique flatten select(upSets, u -> member(h, u));
	)
    )
)

isolatedHypSets = method()
isolatedHypSets (List, List) := Set => (hyp, upSets) -> (
    if #hyp == 0 then return set{};
    h0 := hyp#0;
    result := set{{h0}};
    while true do (
	numResults := #result;
	for l in keys result do (
	    result = result + set apply(hyp - set unique flatten select(upSets, u -> any(l, h -> member(h, u))) - set hyp_(toList(0..<max positions(hyp, H -> member(H,l)))), e -> append(l, e));
	);
    	if #result == numResults then break else print (#result - numResults);
    );
    result + isolatedHypSets(hyp - set {h0}, upSets)
)

elapsedTime tally apply(subsets(28, 2), s -> (
includedIndices = s; 
s0 = unique flatten upSets_includedIndices; 
finishGen = false; 
while finishGen == false do (
    currentSize = #includedIndices; 
    for i in toList(0..<28) - set includedIndices do(
	if #(set(upSets#i) * set(s0)) > 1 then ( 
	    s0 = unique(s0 | upSets#i);
	    includedIndices = append(includedIndices, i);
	    break;
	); 
    ); 
    if #includedIndices == currentSize then finishGen = true;
);
set includedIndices
))

-- TODO:
-- Q: when checking checkPairs, enough to consider torsion?
-- compute limits/colimits of pastures
-- determining if a pasture is a tensor product of specified pastures
-- compute symmetry quotients?
-- Handle quotient by full rank sublattice correctly

restart
load "foundations.m2"
debugLevel = 1
