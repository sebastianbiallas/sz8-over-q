#!/usr/bin/env python3
"""Exact cubic discriminants and field identifications used in the section identifying the cyclic cubic quotient."""
import shutil
import subprocess


def main():
    if shutil.which('gp') is None:
        raise SystemExit('Install PARI/GP (gp must be on PATH).')
    code = r'''
n1=-4*x^3+6*x^2+36*x-6; d1=3*(x^3+5*x^2-9*x-5);
n2=x^3+6*x^2-27*x+21; d2=3*(x^3-7*x^2+12*x-5);
p=x^3+x^2-4*x+1;
if(gcd(n1,d1)!=1 || gcd(n2,d2)!=1,error("common factor"));
if(poldisc(n1-t*d1,x)!=936^2*(t^2+t+1)^2,error("T1 discriminant"));
if(poldisc(n2-t*d2,x)!=117^2*(t^2+t+1)^2,error("T2 discriminant"));
if(!polisirreducible(p) || nfdisc(p)!=169,error("conductor-13 field"));
if(nfisisom(p,d1/3)==0 || nfisisom(p,d2/3)==0,error("infinity fields"));
if(nfisisom(x^3-39*x-26,monic(n1))==0,error("T1 zero fiber"));
if(nfisisom(x^3-39*x-91,n2)==0,error("T2 zero fiber"));
if(nfisisom(monic(n1),n2)!=0,error("twists must differ"));
if(nfdisc(x^3-39*x-26)!=117^2 || nfdisc(x^3-39*x-91)!=117^2,error("conductor-117 fibers"));
Tref=(x^3-3*x-1)/(3*x*(x+1));
if(subst(Tref,x,-1/(x+1))!=Tref,error("reference deck transformation"));
print("PASS: exact cubic discriminants and field identifications.");
'''.replace('monic(n1)', '(n1/pollead(n1))')
    result = subprocess.run(['gp', '-q', '-f'], input=code, text=True, capture_output=True)
    expected = 'PASS: exact cubic discriminants and field identifications.'
    if result.returncode or result.stderr.strip() or result.stdout.strip() != expected:
        raise SystemExit(result.stderr + result.stdout)
    print(expected)


if __name__ == '__main__':
    main()
