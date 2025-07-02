//This code verifies the claims in Table 2.

load "IntegralFrobeniusMatrix.m";

// This function checks that p divides the order of Frobenius.
function CheckpdivFrob(E,l,p)
    FF:=GF(l);
    E:=ChangeRing(E,FF);
    G:=GL(2,p);
    F:=G!IntegralFrobenius(E);
    return F;
end function;

//This function checks that for all primes q dividing \Delta_l (q/p) is not -1.
function Checkcond4(D, p)
    primeFactors := PrimeDivisors(D);
    for q in primeFactors do
        if LegendreSymbol(q, p) eq -1 then
            return false;
        end if;
    end for;
    return true;
end function;

EC:=["864a1", "864b1", "864c1"]; //Cremona Labels of the elliptic curves W from Table 2.
bound:=10000; //Checking primes l up to this bound.

for label in EC do
    count:=0;
    E:=EllipticCurve(label);
    for l in PrimesInInterval(5,bound) do
        a:=TraceOfFrobenius(E,l);
        D:=a^2-4*l;
        pD:=PrimeDivisors(D); //The condition -p Delta_l= s^2, implies that p| Delta_l, reducing the search space.
        pD:= [p : p in pD | p mod 24 eq 19 and IsSquare(-p*D)]; // We only need to consider primes p which are 19 mod 24 and such that -p Delta_l= s^2, as detailed on page 26. 
        for p in pD do 
            if l ne p and Order(CheckpdivFrob(E,l,p)) mod p eq 0 and  Checkcond4(D, p) then //Checking the remaining two conditions.
                print CheckpdivFrob(E,l,p);
                count:=count+1;
            end if;
        end for;
    end for;
    print "For the elliptic curve W of Cremona Label", label, "we have", count, "valid pairs.";
end for;