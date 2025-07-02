load "IntegralFrobeniusMatrix.m";

function AllEllipticCurvesOverFl(l, traces, W)
        print "Computing residual curves...";

        FF := GF(l);
        U, m := UnitGroup(FF);
        Q, toQ := U/(2*U);
        ns := m(Inverse(toQ)(Q.1));
        assert LegendreSymbol(Integers()!ns, l) eq -1;

        cvsj:=[];
        for a in FF do 
            if a notin [FF!0, FF!1728] then
                E:=EllipticCurveFromjInvariant(a);
                EE:=QuadraticTwist(E, ns);
                    if TraceOfFrobenius(E) in traces and not IsIsomorphic(W, E) then
                        Append(~cvsj, E);
                    end if;
                    if TraceOfFrobenius(EE) in traces and not IsIsomorphic(W, EE) then
                        Append(~cvsj, EE);
                    end if;
            end if;
        end for;

        Q1, m1 := quo<U | 4*U>;
        Q2, m2 := quo<U | 6*U>;

        mm1 := map<Q1 -> FF | q :-> m(Inverse(m1)(q))>;
        mm2 := map<Q2 -> FF | q :-> m(Inverse(m2)(q))>;


        crvs_0_in_1st := [EllipticCurve([0, mm2(b)]) : b in Q2 | TraceOfFrobenius(EllipticCurve([0, mm2(b)])) in traces and not IsIsomorphic(W, EllipticCurve([0, mm2(b)]))]; // j = 0
        crvs_0_in_2nd := [EllipticCurve([mm1(a), 0]) : a in Q1| TraceOfFrobenius(EllipticCurve([mm1(a), 0])) in traces and not IsIsomorphic(W, EllipticCurve([mm1(a), 0]))]; // j = 1728

        cvs := cvsj cat crvs_0_in_1st cat crvs_0_in_2nd;
   

    return cvs;
end function;

function MonicDivisors(f,p) //outputs list with all divisors of f ordered by degree, divisor of order (p-1)/2 (i.e. isog poly) together with its factors, factor of order 1 (i.e. torsion poly)
    facs := Factorization(f);
    n := #facs;
    print "factorisation done";
    // Prepare exponent ranges for each factor
    exp_lists := [[0..facs[i][2]] : i in [1..n]];

    divisors := [];
    isogeny_poly:=0;
    torsion_poly:=0;
    for exp_tuple in CartesianProduct(exp_lists) do
        d := 1;
        factors:=[];
        for i in [1..n] do
            d *:= facs[i][1]^exp_tuple[i];
            Append(~factors, facs[i][1]^exp_tuple[i]);
        end for;
        if Degree(d) eq Integers()!((p-1)/2) then //this is the polynomial fixed by a p-isogeny
            isogeny_poly:=d;
            isg_fact:=factors;
            //fact_isog_poly:=fact_g;
        end if;
        if Degree(d) eq 1 then // this is a linear polynomial corresponding to a torsion point
            torsion_poly:=d;
        
        end if;
        Append(~divisors, d);
    end for;
    return divisors, isogeny_poly, isg_fact, torsion_poly;
end function;

function pTorsionPoints(E, p)

print "computing P";
    FF := BaseRing(E);
    assert Characteristic(FF) ne p;
    div_poly:=DivisionPolynomial(E, p);
    fact, isg_pol, fact_isg_pol, trs_pol :=MonicDivisors(div_poly,p);
print "monic divisors done";

    if trs_pol ne 0 then // if P is a torsion point i.e. Frob = (1,b),(0,1)
            xP:=Roots(trs_pol)[1][1];
            fP:=trs_pol;
            K:=FF;
    else
    for f in fact_isg_pol do
    if Degree(f) gt 1 then
    d:=Degree(f);
    K := GF(#FF^d);
    xP:=Roots(f,K)[1][1];
    fP:=f;
    break f;
    end if;
    end for;
    end if;
    
    print "xP=",xP;
    
    PK<y>:=PolynomialRing(K);
    EoK:=ChangeRing(E,K);
    pE:=PK!Evaluate(DefiningPolynomial(EoK),[xP,y,1]);

    // computing the fiels where the y-coordinates live, i.e. where P, Q live.
    if #Factorisation(pE) eq 1 then
    Kp:=ext<K | pE>;
    else
    Kp:=K;
    end if;

    EoKp:=ChangeRing(EoK,Kp);
    P:=EoKp!Points(EoKp,xP)[1];

    
//compute Q
print "computing Q";
R<X>:=PolynomialRing(Kp);
//fact:=Factorisation(div_poly,Kp);

fP:=R!isg_pol;
fQ:=R!div_poly;

for g in fact do
ok:=0;
gg:=R!g; 
    if IsIrreducible(g) and Degree(g) gt 0 and fP mod gg ne 0 then
        if #Roots(gg) ne 0 then
            xQ:=Roots(gg)[1][1];
            ok:=1;
            Kp2:=Kp;
            break g;
        end if;
        for ff in Factorisation(gg) do
            if Degree(ff[1]) lt Degree(fQ) then
                fQ:=ff[1];
                break ff;
            end if;
        end for;
    end if;
end for;
print "ok=",ok;
print "fQ=", fQ;
if ok eq 0 then
    Kp2:= ext<Kp | fQ>;
    xQ:=Roots(fQ,Kp2)[1][1];
end if;
print "xQ=",xQ;

//compute yQ

EoKp2:=ChangeRing(EoKp,Kp2);
PK<y>:=PolynomialRing(Kp2);
pE:=PK!Evaluate(DefiningPolynomial(EoKp2),[xQ,y,1]);


if #Factorisation(pE) eq 1 then
    Kp3:=ext<Kp2 | pE>;
else
    Kp3:=Kp2;
end if;

EoKp3:=ChangeRing(EoKp2,Kp3);
Q:=EoKp3!Points(EoKp3,xQ)[1];

P:=EoKp3!P;

return P, Q, Kp3, EoKp3;
   
end function;

function ComputeB(E1,p)
FF:=BaseRing(E1);
l:=Characteristic(FF);
tr := TraceOfFrobenius(E1);
G := GL(2, p);

M1:=G!IntegralFrobenius(E1); M1;
print "sanity check: traces agree:";
Trace(M1) eq tr;

P1, Q1, Kp,EoKp:=pTorsionPoints(E1, p);
print "point P1 is", P1;
print "point Q1 is", Q1;

print "sanity check: linearly independent:";
IsLinearlyIndependent([P1,Q1],p);

Gal,_,toAut:=AutomorphismGroup(Kp,FF);
Frobq:=toAut(Gal.1);
assert Frobq(Kp.1) eq Kp.1^l;


//anti-symplectic basis
P<x>:=PolynomialRing(Kp);
zeta:=Roots(x^p - 1)[2,1];
print "zeta done";
assert zeta ne 1;

pairing:=WeilPairing(P1,Q1,p);
print "Weil pairing done";
k:=Index([zeta^k eq pairing : k in [1..p]],true);
if IsSquare(k) then
    Q1:=Q1;
    print "symplectic basis";
else
    print "anti-symplectic basis";
    Q1:=-Q1;
end if;


FrP1:=EoKp![Frobq(P1[1]),Frobq(P1[2])];
FrQ1:=EoKp![Frobq(Q1[1]),Frobq(Q1[2])];

a:=Integers()!(M1[1][1]);

print "sanity check, Frob P1 = trace/2 * P1";
FrP1 eq a*P1;


// find b

for i in [1..p] do
    if FrQ1 eq i*P1+a*Q1 then
        b:=i;
    end if;
end for;

return b;

end function;


//tup:=<"864a1",5,19>;
//tup:=<"864b1",7,19>;
//tup:=<"864a1", 7, 19>;
tup:=<"864a1", 73, 211>;

//triples := [<"864a1", 5, 19>, <"864b1", 7, 19>, <"864a1",73,211>];

label, l, p := Explode(tup);
print "Current triple:", label,l, p;      
FF := GF(l);
E := EllipticCurve(label);
E1 := ChangeRing(E, FF);


b_W:=ComputeB(E1,p);
print "b corresponding to W is:",b_W;

/*----------------------------------*/
a := TraceOfFrobenius(E1);

traces := [tr : tr in [-Floor(2*Sqrt(l))..Floor(2*Sqrt(l))] | (a - tr) mod p eq 0];

curves := AllEllipticCurvesOverFl(l, traces, E1);
print "There are", #curves, "isomorphism classes of elliptic curves not isomorphic with W over F_l with trace = a mod p:";
    
    if #curves eq 0 then
        print "no curves";
        print "X_W^-(Q_l) is empty for triple:", tup;
    else
        //print curves;

        G := GL(2, p); 
        M1:=G!IntegralFrobenius(E1);
        assert Order(M1) mod p eq 0;

        Galmods:=[];
    
        for C in curves do
            M2:=G!IntegralFrobenius(C);
            if Order(M2) mod p eq 0 then
                bol,g:=IsConjugate(G,M1,M2);
                    if bol then
                        Append(~Galmods,<C,g, M1, M2>);
                    end if;
            end if;
        end for;

        print "There are", #Galmods, "elliptic curves with the same p-torsion Galois module as W";
        if #Galmods eq 0 then
            print "X_W^-(Q_l) is empty for triple:", tup;
        end if;
    end if;

    for gm in Galmods do
        E:=gm[1];
        b:=ComputeB(E,p);
        print "b corresponding to E",E;
        print "is", b;
    end for;