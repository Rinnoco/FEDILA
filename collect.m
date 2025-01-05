(* collects g^_, alatt^_, Nc^_, delm[], epsilon[], hat2[], etc.              *)
(* The list of elements to collect may contain also Heads of variables as well as 
   patterns, e.g.       collect[...,{g,s2[k[_],_],c2,...}]                   *)

collect[expr_,testa_]:= collect[expr,{testa}] /; 
                                    !(Head[testa] === List) 

collect[expr_,listtesta_List] := 
  Collect[expr, 
          Select[Variables[expr],
                 (   MemberQ[listtesta,#] 
                  || MemberQ[listtesta,Head[#]]
                  || collect1[listtesta,#] )& 
                ]
         ]

collect1[listtesta_List,a_] := Or @@ (MatchQ[a,#]& /@ listtesta)

