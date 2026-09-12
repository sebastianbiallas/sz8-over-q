# The primitive permutation groups of degree 65 (GAP library) and the Sz(8) facts the
# certificate cites.  Driven by tools/primitive65.py, which writes results/primitive65.json.
#   gap -q -b --quitonbreak gap/primitive65.g < /dev/null
SetPrintFormattingStatus("*stdout*", false);
n := NrPrimitiveGroups(65);
Print("NPRIM ", n, "\n");
for i in [1..n] do
  G := PrimitiveGroup(65, i);
  Print("PRIM ", i, " | ", Name(G), " | ", Size(G), " | ", Size(DerivedSubgroup(G)), " | ", IsSimpleGroup(G), "\n");
od;
G := PrimitiveGroup(65, 7);
D := DerivedSubgroup(G);
Print("NORMALISER_S65 ", Size(Normalizer(SymmetricGroup(65), G)), "\n");
Print("SZ8_ORDER ", Size(D), " SIMPLE ", IsSimpleGroup(D), "\n");
Print("SZ8_MAXIMAL_ORDERS ", List(MaximalSubgroupClassReps(D), Size), "\n");
Print("SZ8_ELEMENT_ORDERS ", Set(List(ConjugacyClasses(D), c -> Order(Representative(c)))), "\n");
Print("G_ELEMENT_ORDERS ", Set(List(ConjugacyClasses(G), c -> Order(Representative(c)))), "\n");
P13 := SylowSubgroup(D, 13);
Print("N_G_C13_ORDER ", Size(Normalizer(G, P13)), " ORBITS ", List(Orbits(Normalizer(G, P13), [1..65]), Length), "\n");
Print("N_SZ8_C13_ORDER ", Size(Normalizer(D, P13)), "\n");
# cycle types on 65 points of a class of elements of each order in G
for c in ConjugacyClasses(G) do
  g := Representative(c);
  Print("CLASS ", Order(g), " | ", Collected(CycleLengths(g, [1..65])), " | ", g in D, "\n");
od;
