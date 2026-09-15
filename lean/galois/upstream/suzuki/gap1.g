S := SuzukiGroup(IsMatrixGroup, 8);;
Print("order ", Size(S), "\n");
for g in GeneratorsOfGroup(S) do Display(g); Print("\n"); od;
Print("field ", DefaultFieldOfMatrixGroup(S), "\n");
QUIT;
