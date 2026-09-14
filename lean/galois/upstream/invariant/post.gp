{
  my(P = vector(3, m, sum(n = 1, #E[m], E[m][n] * t^(n-1))));
  Rs = Y^3 - P[1]*Y^2 + P[2]*Y - P[3];   \\ resolvent of 13^12 theta
  write(DIR "/resolvent.gp", "Rs = ", Rs, ";");
  print("irreducible over Q(t): ", polisirreducible(Rs));
  D = poldisc(Rs, Y); print("disc(Rs) factor (t-part): ", factor(D / content(D))[,1]~, " exps ", factor(D/content(D))[,2]~);
  r75 = subst(Rs, t, -7/5); print("R(Y,-7/5) factors: ", factor(r75)[,1]~);
  print("R(Y,-7/5) squarefree: ", poldegree(gcd(r75, deriv(r75))) == 0);
  r0 = subst(Rs, t, 0); print("R(Y,0) field polredabs: ", polredabs(r0), "  disc ", factor(nfdisc(r0)));
  n2 = s^3+6*s^2-27*s+21; d2 = 3*(s^3-7*s^2+12*s-5); n1 = -4*s^3+6*s^2+36*s-6; d1 = 3*(s^3+5*s^2-9*s-5);
  for (k = 1, 4, my(t0 = [0, 1, 2, -1][k]);
    my(q = subst(Rs, t, t0), c2 = n2 - t0*d2, c1 = n1 - t0*d1);
    print("t0=", t0, ": R ", if(polisirreducible(q), polredabs(q), factor(q)[,1]~), " | T2 ", if(polisirreducible(c2), polredabs(c2), factor(c2)[,1]~), " | T1 ", if(polisirreducible(c1), polredabs(c1), factor(c1)[,1]~)));
}
