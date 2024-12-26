(* The function "makeslash" introduces the object "slash" for reducing
   rho indices. In particular,   slash[a] = gamma[rho]*s2[2a,rho].   

   Note: Before applying makesisq in an expression, the latter must be
         expanded, or the part of the expression that depends on rho must
         be collected.                                                     *)

makeslash[expr_Plus]:= makeslash /@ expr

makeslash[expr_Times]:= Select[expr,FreeQ[#,rho]&]*
                       makeslash1[Select[expr,!FreeQ[#,rho]&]]

makeslash[expr_] := expr

makeslash1[expr_]:=
  Module[{temp},
	 temp = expr;
	 Do[temp = temp /. dtrace[a___,rho[i],b___] s2[c_,rho[i]] d_. :>
	    If[FreeQ[d,rho[i]],dtrace[a,slash[Expand[c/2]],b]*d,
	                      dtrace[a,rho[i],b]*s2[c,rho[i]]*d] /.
	    gtrace[a___,rho[i],b___] s2[c_,rho[i]] d_. :>
	    If[FreeQ[d,rho[i]],gtrace[a,slash[Expand[c/2]],b]*d,
	                       gtrace[a,rho[i],b]*s2[c,rho[i]]*d];
	    ,{i,Length[Union[rhos[expr]]]}];
	 reducerho[temp]]


	 
unmakeslash[expr_Plus]:= unmakeslash /@ expr

unmakeslash[expr_Times]:= Select[expr,FreeQ[#,slash]&]*
          unmakeslash1[Select[expr,!FreeQ[#,slash]&],Length[Union[rhos[expr]]]]

unmakeslash[expr_] := If[FreeQ[expr,slash],expr,unmakeslash1[expr,Length[Union[rhos[expr]]]]]  

unmakeslash1[dtrace[a___,slash[p_],b___] c_.,rhomax_]:= unmakeslash1[dtrace[a,rho[rhomax+1],b]*c,rhomax+1]*s2[Expand[2 p],rho[rhomax+1]]

unmakeslash1[gtrace[a___,slash[p_],b___] c_.,rhomax_]:= unmakeslash1[gtrace[a,rho[rhomax+1],b]*c,rhomax+1]*s2[Expand[2 p],rho[rhomax+1]]

unmakeslash1[expr_,rhomax_] := expr				  
