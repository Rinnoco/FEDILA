(* Programmi per fare il riordinamento, sia negli impulsi, date le
 proprieta' di simmetria, sia negli indici rho *)
 
(* Abbiamo fatto la sostituzione: hat -> cap per s2 -> d2 *)
 
(* Versione modificata nella regola che calcola porder1 e rorder di una
   espressione con testa Times *)


porder[expr_] := expr /; FreeQ[expr,p]
porder[expr_] := Block[
 {pfactors=1, rest=1, numerop, plist, perms, goodperms={} },
 If[SameQ[Head[expr],Times],
    Do[ If[ MemberQ[{fhat,hat2,expi,delta},Head[expr[[ii]]] ],
            pfactors *= expr[[ii]],
            rest *= expr[[ii]] ],
        {ii,Length[expr]} ], 
   rest=expr];
   numerop = Length[Union[ ps[expr] ]] ;
    plist = Table[p[ii],{ii,numerop}] ;
     perms = Permutations[plist] ;
      Do[ If[
           pfactors == (pfactors /. Inner[Rule,plist,perms[[ii]],List]),
             goodperms = Append[goodperms,perms[[ii]]]      
                                              ],
                                     {ii,Length[perms]}
                                                       ] ;
      pfactors * porder1[rest,plist,goodperms]
                                                              ]

ps[expr_] := expr[[ Sequence @@ # ]]& /@ Position[expr,p[_]]

porder1[expr_Plus,a_,b_] :=
                  (porder1[#,a,b])& /@ expr

porder1[expr_Times,a_,b_] := 
    porder1[Select[expr,!FreeQ[#,p]&],a,b] *
                        Select[expr,FreeQ[#,p]&] /;
                              Or @@ (FreeQ[#,p]& /@ List @@ expr)

porder1[expr_,plist_,perms_] := Block[{expr1 = expr},
   Do[
      If[!OrderedQ[{ps[expr1],
                     ps[expr /. Inner[Rule,plist,perms[[ii]],List]]}], 
         expr1 = expr /. Inner[Rule,plist,perms[[ii]],List]
        ], {ii,Length[perms]}
     ]; 
   expr1                             ]

rhos[expr_] := expr[[Sequence @@ #]]& /@ Position[expr,rho[_]]

rorder[expr_Times] := 
       rorder[Select[expr,!FreeQ[#,rho]&]] *
                         Select[expr,FreeQ[#,rho]&] /;
                              Or @@ (FreeQ[#,rho]& /@ List @@ expr)     

rorder[a_Plus] :=
           rorder /@ a

rorder[a_Times] := Block[ {d2, listrho},
                         listrho = Union[ rhos[a] ];
                         rorder1[a /. s2 -> d2, listrho] /. d2 -> s2
                        ]

rorder1[a_,listrho_] :=
                a /; Length[listrho] == 1

rorder1[a_,listrho_] := 
   rorder2[a,
           listrho,
           rcompare[Table[rhos[a /.{listrho[[1]] -> listrho[[ii]],
                                    listrho[[ii]] -> listrho[[1]]}],
                          {ii,Length[listrho]}
                         ], 
                    listrho
                   ] 
          ]

rorder2[a_,listrho_,rpref_] :=
  Switch[ Length[rpref],
           0, a,
           1, rorder1[a /. {listrho[[1]] -> rpref[[1]],
                                 rpref[[1]] -> listrho[[1]]},
                       Drop[listrho,1]
                         ],
           _,firstor0[Sort[Array[(rorder1[a /. {listrho[[1]] -> rpref[[#]],
                                        rpref[[#]] -> listrho[[1]]},
                                  Drop[listrho,1]
                                 ])& ,
                          Length[rpref] 
                         ],
                   OrderedQ[{rhos[#1],rhos[#2]}]&
                  ]]
        ]

firstor0[list_] := Block[{flag = 0},
             Do[ Do[ If[list[[jj]] === -list[[ii]], flag = 1],
                    {ii,jj + 1, Length[list]}],
                 {jj,Length[list] - 1}];
             If[flag == 1, 0, list[[1]] ]
                        ]
                                             
rcompare[list_,listrho_] := Catch[ Block[
 {result={},listlocal=list,listrholocal=listrho,translist=Transpose[list],
   poslist,ii},
 For[ii=1,ii<=Length[list[[1]]],ii++,
     If[!(SameQ @@ translist[[ii]]),
        (poslist=Flatten[Position[translist[[ii]],listrho[[1]]]];
         If[poslist=={},
            Throw[listrholocal],
            (listlocal = (listlocal[[#]])& /@ poslist ;
             listrholocal = (listrholocal[[#]])& /@ poslist;
             translist=Transpose[listlocal]; 
             result={listrholocal[[1]]} )
           ])
       ]
    ]; result                    ]]
                                                        
rorder[a_] := a            




