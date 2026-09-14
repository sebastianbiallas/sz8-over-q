\\ usage: set PREC and M before reading
default(realprecision, PREC);
read(DIR "/data.gp"); read(DIR "/orb.gp");
F0 = subst(F, t, 0);
rr = polroots(F0);
\\ order roots by the certified disc centres (paper order)
r0 = vector(65, i, my(best = 1); for(j = 2, 65, if(abs(rr[j] - centers[i]) < abs(rr[best] - centers[i]), best = j)); rr[best]);
dmin = vecmin(vector(65, i, abs(r0[i] - centers[i])));
dmax = vecmax(vector(65, i, abs(r0[i] - centers[i])));
printf("max centre distance %.3g\n", dmax);
print("roots distinct after matching: ", #Set(apply(z -> round(z * 10^6), r0)) == 65);
Fx = deriv(F, x);
ser(i) = {
  my(r = r0[i] + O(t^M));
  for (k = 1, ceil(log(M) / log(2)) + 3, r = r - subst(F, x, r) / subst(Fx, x, r));
  r;
}
R = vector(65, i, ser(i));
print("residual check: ", exponent(abs(polcoef(subst(F, x, R[1]), M-1, t))) );
thetaO(O) = {
  my(S = vector(65, i, 0), P = Map());
  for (n = 1, #O[,1],
    my(i = O[n,1] + 1, j = O[n,2] + 1, k = O[n,3] + 1);
    S[i] += R[j] * R[k]);
  sum(i = 1, 65, R[i]^2 * S[i]);
}
th = [thetaO(O0), thetaO(O1), thetaO(O2)];
printf("theta_j(0): %.12g\n", vector(3, j, polcoef(th[j], 0, t)));
printf("pairwise diffs: %.6g %.6g %.6g\n", abs(polcoef(th[1]-th[2],0,t)), abs(polcoef(th[1]-th[3],0,t)), abs(polcoef(th[2]-th[3],0,t)));
e = [th[1]+th[2]+th[3], th[1]*th[2]+th[1]*th[3]+th[2]*th[3], th[1]*th[2]*th[3]];
sc = 13^(4*kscale);
{
for (m = 1, 3,
  my(v = vector(M, n, polcoef(e[m], n-1, t) * sc^m), rv = vector(M, n, round(real(v[n]))), err = vecmax(vector(M, n, abs(v[n] - rv[n]))));
  E[m] = rv;
  printf("e%d: max dist to integer %.3g; nonzero degrees %s; digits %s\n", m, err, select(n -> rv[n+1] != 0, vector(M, n, n-1)), vector(M, n, if(rv[n], #digits(abs(rv[n])), 0)));
);
}
