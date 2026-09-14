read("resolvent.gp");
P1 = -polcoef(Rs, 2, Y); P2 = polcoef(Rs, 1, Y); P3 = -polcoef(Rs, 0, Y);
if (Rs != Y^3 - P1*Y^2 + P2*Y - P3, error("shape"));
for (m = 1, 3, my(P = [P1,P2,P3][m]); print("E", m, " ", vector(poldegree(P, t)+1, k, polcoef(P, k-1, t))));
print("ev ", [subst(P1,t,-7/5), subst(P2,t,-7/5), subst(P3,t,-7/5)]);
D = P1^2*P2^2 - 4*P2^3 - 4*P1^3*P3 + 18*P1*P2*P3 - 27*P3^2; print("D(0) ", subst(D,t,0));
print("disc check ", D == poldisc(Rs, Y));
