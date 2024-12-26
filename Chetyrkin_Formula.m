
(* The function "ChetyrkinFormula" performs integration over the momentum p[i],
   using the one-loop formula, given in Chetyrkin et al., N.P. B.192, 159, for
   integrals with propagators of the form:

    hat2[p[i]]^j hat2[-p[i] + b]^k   or   hat2[p[i]]^j hat2[p[i] + b]^k.     

   Note: Before applying ChetyrkinFormula in an expression, the latter must be
         expanded, or the part of the expression that depends on p[i] must be
         collected.
         We also included the definition of "grule" for replacing g functions
         coming from the Chetryrkin's Formula. *)


ChetyrkinFormula[expr_Plus,p[i_]] := ChetyrkinFormula[#,p[i]]& /@ expr

ChetyrkinFormula[expr_Times,p[i_]] := Select[expr,FreeQ[#,p[i]]&]*
                          ChetyrkinFormula1[Select[expr,!FreeQ[#,p[i]]&],p[i]]

ChetyrkinFormula[expr_,p[i_]] := If[FreeQ[expr,p[i]],expr,
				    ChetyrkinFormula1[expr,p[i]]]

ChetyrkinFormula1[a_. hat2[p[i_]]^j_. hat2[-p[i_]+b_]^k_.,p[i_]] :=
          sisq[b]^(nDim/2-j-k)/(4Pi)^2 *Sum[g[j,k,count[a,s2[2p[i],_]],s]*
	  sisq[b]^s /s!/4^s (Fold[box[#1,p[i],#2]&,a,Table[rho[20+l],{l,s}]] /.
	  p[i] -> b) ,{s,0,count[a,s2[2p[i],_]]/2}] /;
          (FreeQ[a,hat2[_. p[i] + _]] && FreeQ[a,exp[_ p[i]]])

ChetyrkinFormula1[a_. hat2[p[i_]]^j_. hat2[p[i_]+b_]^k_.,p[i_]] :=	  
	  sisq[-b]^(nDim/2-j-k)/(4Pi)^2 * Sum[g[j,k,count[a,s2[2p[i],_]],s]*
	  sisq[-b]^s /s!/4^s (Fold[box[#1,p[i],#2]&,a,Table[rho[20+l],{l,s}]] /.
	  p[i] -> -b),{s,0,count[a,s2[2p[i],_]]/2}] /;
          (FreeQ[a,hat2[_. p[i] + _]] && FreeQ[a,exp[_ p[i]]])

ChetyrkinFormula1[a_,p[i_]] := a

box[a_,b_,c_] := box1[Expand[a],b,c] /; (FreeQ[a,box] && FreeQ[a,box1] &&
					 FreeQ[a,derivp] && FreeQ[a,derivp1])

box1[a_Plus,b_,c_] := box1[#,b,c]& /@ a
box1[a_Times,b_,c_] := (Select[a,FreeQ[#,b]&])*
                       derivp[derivp[Select[a,!FreeQ[#,b]&],b,c],b,c]
box1[a_,b_,c_] := If[FreeQ[a,b],0,derivp[derivp[a,b,c],b,c]]


derivp[a_,b_,c_] := derivp1[Expand[a],b,c] /; (FreeQ[a,derivp] && FreeQ[a,derivp1])

derivp1[a_Plus,b_,c_]:= derivp1[#,b,c]& /@ a
derivp1[a_^j_,b_,c_]:= j a^(j-1) derivp1[a,b,c]
derivp1[a_*b_,c_,d_]:= derivp1[a,c,d]*b + derivp1[b,c,d]*a
derivp1[a_,b_,c_]:= 0 /; FreeQ[a,b]
derivp1[s2[2 a_,b_],c_,d_]:= delm[b,d] /; (a === c)

grule = {g[a_,b_,n_,s_] :> (4Pi)^(2-nDim/2) Gamma[a+b-s-nDim/2]/Gamma[a]/Gamma[b] Beta[nDim/2-a+n-s,nDim/2-b+s]}
