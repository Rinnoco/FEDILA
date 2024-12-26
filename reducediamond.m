
(* The function "reducediamond" make use of the recursion relation, given
   in Chetyrkin et al., N.P. B.192, 159, for scalar two-loop integrals of
   the "diamond" type, i.e., with propagators of the form:

        hat2[p[1]]^a*hat2[-p[1]+q[1]]^b*hat2[-p[1]+p[2]]^l*
        hat2[p[2]]^m*hat2[-p[2]+q[1]]^n.
   
   A generalized formula for tensor diamond integrals, given in
   "scanned_notes_diamond_integral.pdf", is also applied in this function.     

   Note: Before applying reducediamond in an expression, the latter must be
         expanded, or the part of the expression that depends on both denoms
         and p[1] must be collected.
         NB: denoms[a,b,l,m,n] = hat2[p[1]]^a*hat2[-p[1]+q[1]]^b*
                                 hat2[-p[1]+p[2]]^l*hat2[p[2]]^m*
                                 hat2[-p[2]+q[1]]^n                          *)

reducediamond[expr_Plus] := reducediamond /@ expr

reducediamond[expr_] :=  
  expr //. c_. denoms[a_?((#!=0)&),b_?((#!=0)&),l_?((IntegerQ[#] && #>0)&),
		     m_?((IntegerQ[#] && #>0)&),n_?((IntegerQ[#] && #>0)&)] :>
	   Module[{ctemp,c1,c2,c3},
                  ctemp = If[Head[c] === Times,List @@ c,{c}];
                  c1 = Times @@ Select[ctemp,FreeQ[#,p[1]]&];
                  c2 = (Select[ctemp,!FreeQ[#,p[1]]&] /. s2[2 p[1],r1_]^r2_ :>
			(Sequence @@ Table[s2[2 p[1],r1],{j,r2}]));
		  c3 = Times @@ c2;		    
                  c1*inv[nDim+count[c3,s2[2p[1],_]]-a-b-2l]*
	          (-a*(c3*denoms[a+1,b,l,m-1,n] - c3*denoms[a+1,b,l-1,m,n])
	           -b*(c3*denoms[a,b+1,l,m,n-1] - c3*denoms[a,b+1,l-1,m,n])
		   + Sum[(Times @@ Drop[c2,{s}])*(c2[[s]] /. p[1] -> p[2])*
		        denoms[a,b,l,m,n],{s,Length[c2]}])]
