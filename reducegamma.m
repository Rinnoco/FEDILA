(* The function reducegamma reduces the gamma matrices appearing in dtraces and gtraces by using the following identity: slash[p]*slash[p] = sisq[p].
 NOTE: The function uses internally the functions makeslash and unmakeslash. Thus, the input and output do not depend on slash. *)

reducegamma[expr_Plus]:= reducegamma /@ expr
  
reducegamma[expr_]:= unmakeslash[reducegamma1[makeslash[expr]]]

reducegamma1[expr_Times]:= reducegamma1 /@ expr
  
reducegamma1[dtrace[a___,slash[p_],slash[p_],b___]]:=reducegamma1[dtrace[a,b]]*
                                                     sisq[p]
  
reducegamma1[gtrace[a___,slash[p_],slash[p_],b___]]:=reducegamma1[gtrace[a,b]]*
                                                     sisq[p]
  
reducegamma1[expr_]:= expr

(* The function applyWI applies WI of the form:
     spash[p]*slash[-p+k]*slash[k] = -sisq[p]*slash[k] + slash[p]*sisq[k]
   and similar relations.
   NOTE: The function uses internally the functions makeslash and unmakeslash. Thus, the input and output do not depend on slash.*)

applyWI[expr_]:= unmakeslash[Expand[makeslash[expr] //.
        dtrace[a___,slash[p1_],slash[p2_],slash[p3_],b___] :>
  Which[SameQ[p2,Expand[-p1+p3]],-dtrace[a,slash[p3],b]*sisq[p1] +
	                          dtrace[a,slash[p1],b]*sisq[p3],
	SameQ[p2,Expand[p1+p3]], dtrace[a,slash[p3],b]*sisq[p1] +
				  dtrace[a,slash[p1],b]*sisq[p3],
	SameQ[p2,Expand[p1-p3]], dtrace[a,slash[p3],b]*sisq[p1] -
	                          dtrace[a,slash[p1],b]*sisq[p3],
	SameQ[p2,Expand[-p1-p3]],-dtrace[a,slash[p3],b]*sisq[p1] -
	                          dtrace[a,slash[p1],b]*sisq[p3],
			True,dtrace[a,slashHIDE[p1],slash[p2],slash[p3],b]] //.
	gtrace[a___,slash[p1_],slash[p2_],slash[p3_],b___] :>
  Which[SameQ[p2,Expand[-p1+p3]],-gtrace[a,slash[p3],b]*sisq[p1] +
	                         gtrace[a,slash[p1],b]*sisq[p3],
	SameQ[p2,Expand[p1+p3]], gtrace[a,slash[p3],b]*sisq[p1] +
	                         gtrace[a,slash[p1],b]*sisq[p3],
	SameQ[p2,Expand[p1-p3]], gtrace[a,slash[p3],b]*sisq[p1] -
	                         gtrace[a,slash[p1],b]*sisq[p3],
	SameQ[p2,Expand[-p1-p3]],-gtrace[a,slash[p3],b]*sisq[p1] -
	                         gtrace[a,slash[p1],b]*sisq[p3],
			True,gtrace[a,slashHIDE[p1],slash[p2],slash[p3],b]] /.
	slashHIDE -> slash]]
					 
  
