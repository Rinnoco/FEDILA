(* This function operates on a sum of terms, each of which is a product.
   For each term, which may contain up to one "dtrace", it checks all pairs of 
   consecutive indices of gamma matrices: If the rest of the term is symmetric
   under the interchange of a pair of two consecutive indices, then the term 
   gets multiplied by a Kronecker delta of these two indices *)

reducegammaproductDirac[a_] := 
  Module[{expr = If[Head[a]===Plus, List@@a, {a}], expr2,imax,productDiraclengths},
         expr = {# /. productDirac[__]->1, (# / (# /. productDirac[__]->1)) // Rationalize}& /@ expr;
         productDiraclengths = Union[Length /@ Select[Variables[expr],Head[#]===productDirac&]];
         imax = If[productDiraclengths === {}, 0, productDiraclengths[[-1]] - 2];
         Do[expr2 = 
              Table[{If[Length[expr[[j,2]]]>i+2 && 
                        !(FreeQ[expr[[j,2,i+1]],rho]) && 
                        !(FreeQ[expr[[j,2,i+2]],rho]) && 
                        (Length[Position[expr[[j,2]],expr[[j,2,i+1]]]] + 
                         Length[Position[expr[[j,2]],expr[[j,2,i+2]]]] == 2) &&
                        SameQ[expr[[j,1]], expr[[j,1]] /. {expr[[j,2,i+1]]->expr[[j,2,i+2]],
                                                           expr[[j,2,i+2]]->expr[[j,2,i+1]]}],
                        expr[[j,1]] delm[expr[[j,2,i+1]],expr[[j,2,i+2]]], 
                        expr[[j,1]]],
                     expr[[j,2]]},
                    {j,Length[expr]}]; 
            expr = expr2, {i,imax-1}]; 
         Plus @@ ((Times @@ #)& /@ expr)]


reducegammatraceDirac[a_] := 
  Module[{expr = If[Head[a]===Plus, List@@a, {a}], expr2,imax,traceDiraclengths},
	 expr = {# /. b_. traceDirac[__] :> b, #}& /@ expr;
         expr = {#[[1]], #[[2]]/#[[1]] // Rationalize } & /@ expr;
         traceDiraclengths = Union[Length /@ Select[Variables[expr],Head[#]===traceDirac&]];
         imax = If[traceDiraclengths === {}, 0, traceDiraclengths[[-1]] ];
         Do[expr2 = 
              Table[{If[Length[expr[[j,2]]]>i && 
                        !(FreeQ[expr[[j,2,i]],rho]) && 
                        !(FreeQ[expr[[j,2,i+1]],rho]) && 
                        (Length[Position[expr[[j,2]],expr[[j,2,i]]]] + 
                         Length[Position[expr[[j,2]],expr[[j,2,i+1]]]] == 2) &&
                        SameQ[expr[[j,1]], expr[[j,1]] /. {expr[[j,2,i]]->expr[[j,2,i+1]],
                                                           expr[[j,2,i+1]]->expr[[j,2,i]]}],
                        expr[[j,1]] delm[expr[[j,2,i]],expr[[j,2,i+1]]], 
                        expr[[j,1]]],
                     expr[[j,2]]},
                    {j,Length[expr]}]; 
            expr = expr2, {i,imax-1}]; 
         Plus @@ ((Times @@ #)& /@ expr)]
