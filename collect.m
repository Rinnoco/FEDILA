(* collects g^_, alatt^_, Nc^_, delm[], epsilon[], hat2[], etc.              *)
(* The list of elements to collect may contain also Heads of variables as well as 
   patterns, e.g.       collect[...,{g,s2[k[_],_],c2,...}]                   *)

collect[expr_,testa_]:= collect[expr,{testa}] /; 
                                    !(Head[testa] === List) 

collect[expr_,listtesta_List] := 
  Collect[expr, 
          Select[variablesnew[expr],
                 (   MemberQ[listtesta,#] 
                  || MemberQ[listtesta,Head[#]]
                  || collect1[listtesta,#] )& 
                ]
         ]

collect1[listtesta_List,a_] := Or @@ (MatchQ[a,#]& /@ listtesta)

variablesnew[a_]:=Sort[Union[Flatten[variablesnew1[a]]] /. Null -> Sequence[]]
variablesnew1[a_Plus]:= variablesnew1[List @@ a]
variablesnew1[a_List]:= variablesnew1 /@ a
variablesnew1[a_Times]:= variablesnew1[List @@ a]
variablesnew1[a_Power]:= variablesnew1[a[[1]]]
variablesnew1[a_]:= Null /; NumberQ[a]
variablesnew1[a_]:= a
