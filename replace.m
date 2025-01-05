replace[expr_,{a_,b_}] := expr  /;  FreeQ[expr,a]
replace[expr_Plus,list_]:= replace[#,list]& /@ expr
replace[expr_,{a_,b_}]:=
    replace[Select[expr,(!FreeQ[#,rho])&],{a,b}] *
                        (Select[expr,FreeQ[#,rho]&] /. a->b) /;
                            SameQ[Head[expr],Times] && 
                            (Or @@ (FreeQ[#,rho]& /@ List @@ expr))
replace[expr_,{a_,b_}]:= replace1[expr,{a,b}] /; !SameQ[Head[expr],Plus] 

replace1[expr_,{a_,b_}] := expr  /;  FreeQ[expr,a]
replace1[expr_Times,{a_,b_}]:= 
  Block[{pref=1, rest=1},
        Do[ If[ MemberQ[{delm,epsilon},Head[expr[[j]]] ] && FreeQ[Head[expr[[j]]],a],
                pref *= expr[[j]],
                rest *= expr[[j]] ],
            {j,Length[expr]} ];
        pref * replace2[Expand[rest],{a,b},pref]]
replace1[expr_,a_]:= replace2[Expand[expr],a,1] /; !(Head[expr]===Times)

replace2[expr_Plus,a__]:= replace2[#,a]& /@ expr
replace2[expr_,{a_,b_},pref_]:=
      Block[{expr1}, 
            expr1 = canonical[ExpandAll[expr /. a->b]];
            expr1 = expr1 * nDim^(Length[Union[rhos[expr],rhos[pref]]] -
                                  Length[Union[rhos[expr1],rhos[pref]]])]

rhos[expr_] := expr[[Sequence @@ #]]& /@ Position[expr,rho[_]]







