function symFrobMatrix2(E,p)
Gp:=GL(2,p);
Fp:=GF(p);
Zp:=Integers(p);
Fq:=BaseField(E);
q:=Characteristic(Fq);
P<x>:=PolynomialRing(Rationals());

// fixes a non-square mod p
_:=exists(ns){ x : x in [1..p] | not IsSquare(Zp!x) };
assert LegendreSymbol(ns,p) eq -1;

EoFq:=E;
polE:=DivisionPolynomial(EoFq,p);
K:=SplittingField(polE);
PK<y>:=PolynomialRing(K);
roots:=Roots(polE,K);
r1:=roots[1,1];

EoK:=ChangeRing(EoFq,K);
pE:=PK!Evaluate(DefiningPolynomial(EoK),[r1,y,1]);

if #Factorisation(pE) eq 1 then
Kp:=ext<K | pE>;
else
Kp:=K;
end if;
 

EoKp:=ChangeRing(EoK,Kp);

// fixing a primitive root of unity to use in with the Weil pairing
zeta:=Roots(x^p - 1,K)[2,1];
assert zeta ne 1;

P1:=EoKp!Points(EoKp,r1)[1];

for i in [1..#roots] do
    pt:=Points(EoKp,roots[i,1])[1];
    if IsLinearlyIndependent([P1,pt],p) then
        pairing:=WeilPairing(P1,pt,p);
        k:=Index([zeta^k eq pairing : k in [1..p]],true);
        if IsSquare(Zp!k) then
            P2:=pt;
        else
            P2:=ns*pt;
        end if;
        break i;
    end if;
end for;
assert IsSquare(Zp!Index([zeta^k eq WeilPairing(P1,P2,p) : k in [1..p]],true));

 
/* computing the action of Frob_q in the computed basis */

// finding the Frobenius element

Gal,_,toAut:=AutomorphismGroup(Kp,Fq);
Frobq:=toAut(Gal.1);
assert Frobq(Kp.1) eq Kp.1^q;

FrP1:=EoKp![Frobq(P1[1]),Frobq(P1[2])];
FrP2:=EoKp![Frobq(P2[1]),Frobq(P2[2])];

for a, b in [1..p] do
    if (a*P1 + b*P2) eq FrP1 then
        vec1:=[a,b]; bol1:=true;
    else
        bol1:=false;
    end if;
    if (a*P1 + b*P2) eq FrP2 then
        vec2:=[a,b]; bol2:=true;
    else
        bol2:=false;
    end if;
    if bol1 and bol2 then break a; end if;
end for;
FrobMat:=Transpose(Gp!Matrix([vec1,vec2]));
return FrobMat, [P1,P2];
end function;

load "IntegralFrobeniusMatrix.m";

//triples ordered by l, and the last one with the next smallest p. Includes the ones from nuno-kraus

/*triples1:=[<"864a1",5,19>, <"864a1", 31,43 >, <"864a1",73,211>, <"864a1", 95597, 67>];
triples2:=[<"864b1", 7,19>,<"864b1", 13, 43>,<"864b1",19,67>,<"864b1", 97,307>];
triples3:=[<"864c1",73,211>,<"864c1", 577, 19 >, <"864c1", 17257, 19>, <"864c1",28813, 19>];

triples := [<"864a1", 5, 19>, <"864b1", 7, 19>, <"864a1",73,211>];
*/

//p=19 triples

triples:=[<"864c1", 577, 19 >, <"864c1", 17257, 19>, <"864c1",28813, 19>];

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

for tup in triples do 
    label, l, p := Explode(tup);
    print "Current triple:", label,l, p;

    FF := GF(l);
    E := EllipticCurve(label);
    E1 := ChangeRing(E, FF);
    a := TraceOfFrobenius(E1);

    traces := [tr : tr in [-Floor(2*Sqrt(l))..Floor(2*Sqrt(l))] | (a - tr) mod p eq 0];

    curves := AllEllipticCurvesOverFl(l, traces, E1);
    print "There are", #curves, "isomorphism classes of elliptic curves not isomorphic with W over F_l with trace = a mod p:";
    
    if #curves eq 0 then
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
        else
            //print Galmods;
        
print "computing Frobenius on fixed residual curve";
M1:=symFrobMatrix2(E1,p);
assert Order(M1) mod p eq 0;
symplectic:=[];
types:=[];
for j in [1..#Galmods] do
	print "+++++";
	E2:=Galmods[j][1];  
	M2:=symFrobMatrix2(E2,p);
	bol,g:=IsConjugate(G,M1,M2);
	if bol then 
	if not IsSquare(Determinant(g)) then
		print "failed with ", Galmods[j];
		break j;		
	else
		Append(~types,IsSquare(Determinant(g)));
	    Append(~symplectic,E2);
    end if;    
	end if;
end for;
if #Galmods eq #symplectic then
print "YAY for triple:",tup;
print "all curves give symplectic points!"; 
end if;
    end if;
    end if;
end for;
