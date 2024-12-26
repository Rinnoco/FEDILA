(* The function "makeprod" introduces the object "prod" for reducing
 rho indices. In particular,   prod[a,b] = s2[2a,rho]*s2[2b,rho].   

   Note: Before applying makeprod in an expression, the latter must be
         expanded, or the part of the expression that depends on rho must
         be collected.                                                     *)

makeprod[expr_Plus]:= makeprod /@ expr

makeprod[expr_Times]:= Select[expr,FreeQ[#,rho]&]*
                       makeprod1[Select[expr,!FreeQ[#,rho]&]]

makeprod[expr_] := If[FreeQ[expr,rho],expr,makeprod1[expr]]

makeprod1[expr_]:=
  Module[{temp},
	 temp = expr;
	 Do[temp = temp /. s2[a_,rho[i]]*s2[b_,rho[i]] c_. :> If[FreeQ[c,rho[i]],prod[Expand[a/2],Expand[b/2]]*c,s2[a,rho[i]]*s2[b,rho[i]]*c],{i,Length[Union[rhos[expr]]]}];
	 temp]

  
unmakeprod[expr_Plus]:= unmakeprod /@ expr

unmakeprod[expr_Times]:= Select[expr,FreeQ[#,prod]&]*
          unmakeprod1[Select[expr,!FreeQ[#,prod]&],Length[Union[rhos[expr]]]]

unmakeprod[expr_] := If[FreeQ[expr,prod],expr,unmakeprod1[expr,Length[Union[rhos[expr]]]]]  

unmakeprod1[prod[p1_,p2_]^i_. a_.,rhomax_]:= unmakeprod1[prod[p1,p2]^(i-1)*a,rhomax+1]*s2[Expand[2 p1],rho[rhomax+1]]*s2[Expand[2 p2],rho[rhomax+1]]

unmakeprod1[expr_,rhomax_] := expr

  
prodtosisq[expr_] := expr /. prod[p1_,p2_] :> If[OrderedQ[{reducep[Expand[-p1+p2]],reducep[Expand[p1+p2]]}],-1/2*(sisq[Expand[-p1+p2]] - sisq[p1] - sisq[p2]),1/2*(sisq[Expand[p1+p2]] - sisq[p1] - sisq[p2])]
