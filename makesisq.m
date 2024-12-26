
(* The function "makesisq" introduces the object "sisq" for reducing
   rho indices. In particular,   sisq[a] = s2[2a,rho]^2.   

   Note: Before applying makesisq in an expression, the latter must be
         expanded, or the part of the expression that depends on rho must
         be collected.                                                     *)

makesisq[expr_Plus]:= makesisq /@ expr

makesisq[expr_Times]:= Select[expr,FreeQ[#,rho]&]*
                       makesisq1[Select[expr,!FreeQ[#,rho]&]]

makesisq[expr_] := If[FreeQ[expr,rho],expr,makesisq1[expr]]

makesisq1[expr_]:=
  Module[{temp},
	 temp = expr;
	 Do[temp = temp /. s2[a_,rho[i]]^2 b_. :> If[FreeQ[b,rho[i]],sisq[Expand[a/2]]*b,s2[a,rho[i]]^2*b],{i,Length[Union[rhos[expr]]]}];
	 temp]


unmakesisq[expr_Plus]:= unmakesisq /@ expr

unmakesisq[expr_Times]:= Select[expr,FreeQ[#,sisq]&]*
          unmakesisq1[Select[expr,!FreeQ[#,sisq]&],Length[Union[rhos[expr]]]]

unmakesisq[expr_] := If[FreeQ[expr,sisq],expr,unmakesisq1[expr,Length[Union[rhos[expr]]]]]  

unmakesisq1[sisq[p_]^i_. a_.,rhomax_]:= unmakesisq1[sisq[p]^(i-1)*a,rhomax+1]*s2[Expand[2 p],rho[rhomax+1]]^2

unmakesisq1[expr_,rhomax_] := expr

