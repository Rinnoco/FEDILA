(* To make this version run faster, instances of:
        canonical // rorder // collectCFirst 
   have been replaced by:
        canonical // collectCFirst                 *)
(* In this version, use of collectCFirst has been eliminated
   altogether, since it lead to an imcompatible input format for 
   contract1                                                      *)

(* Contraction of a list of vertices, which may contain gluons, ghosts
   and/or fermions

   Note: 1) No extra factors of (-1) are assigned to closed loops of
            ghosts
         2) The (ij)th element of the matrix `contractionsG' indicates
            the number of contractions among antighosts from the ith
            and ghosts from the jth vertex. Consequently, this matrix 
            is not symmetric; in this case, 'contract' should be
            called separately for each version of the matrix
         3) The (ij)th element of the matrix `contractionsF' indicates
            the number of contractions among antifermions from the ith
            and fermions from the jth vertex.
         4) Each vertex is intended to be multiplied by:
              A[k[1],mu[1],c[1]] * ... * A[k[n],mu[n],c[n]] *
              phibar[k[n+1],c[n+1]] * ... * phibar[k[n+m],c[n+m]] *
              phi[k[n+m+1],c[n+m+1]] * ... * phi[k[n+2m],c[n+2m]]
              Psibar[k[n+2m+1],fmu[n+2m+1],cf[n+2m+1]]*........*
              Psibar[k[n+2m+l],fmu[n+2m+l],cf[n+2m+l]]*
              Psi[k[n+2m+l+1],fmu[n+2m+l+1],cf[n+2m+l+1]]*.....*
              Psi[k[n+2m+2l],fmu[n+2m+2l],cf[n+2m+2l]]
         5) Vertices are presented in the form: {{n,nG,nF},expr}, where:
              n    is the number of gluon legs
              nG   is the number of ghost-antighost pairs
              nF   is the number of fermion-antifermion pairs
              expr is the expression for the vertex itself                *)


contract[vertices_, contractions_] :=
contract[vertices, contractions, Table[Table[0,{Length[vertices]}],{Length[vertices]}],Table[Table[0,{Length[vertices]}],{Length[vertices]}]]
contract[vertices_,contractions_,contractionsG_]:= 
contract[vertices,contractions,contractionsG,Table[Table[0,{Length[vertices]}],{Length[vertices]}]]
contract[vertices_, contractions_, contractionsG_,contractionsF_] := 
  Block[{pcount=0, pdep, pdeprules, qrules, 
         bcount=0, bdep, bdeprules, arules,
         rhocount=0, rhodep, rhodeprules, nurules,
         bfcount=0, bfdep, bfdeprules, afrules,
         frhocount=0, frhodep, frhodeprules, fnurules,
         localvertices, numbervertices, orders, ordersG, ordersF,
         externals, externalsG, externalsAG, externalsF, externalsAF,
         used, usedG, usedAG, usedF, usedAF,
         extindex=0, propprod=1},

        localvertices = (#[[2]])& /@ vertices;
        numbervertices=Length[vertices];
        orders = (#[[1,1]])& /@ vertices;
        ordersG = (#[[1,2]])& /@ vertices;
        ordersF = (#[[1,3]])& /@ vertices;
        externals=Table[orders[[i]]-Sum[contractions[[i,j]],
                        {j, numbervertices}], {i, numbervertices}];
        externalsG=Table[ordersG[[i]]-Sum[contractionsG[[j,i]],
                         {j, numbervertices}], {i, numbervertices}];
        externalsAG=Table[ordersG[[i]]-Sum[contractionsG[[i,j]],
                          {j, numbervertices}], {i, numbervertices}];
        externalsF=Table[ordersF[[i]]-Sum[contractionsF[[j,i]],
                          {j, numbervertices}], {i, numbervertices}];
        externalsAF=Table[ordersF[[i]]-Sum[contractionsF[[i,j]],
                         {j, numbervertices}], {i, numbervertices}];
        used = externals;
        usedG = externalsG + orders + ordersG;
        usedAG = externalsAG + orders;
        usedF = externalsF + orders + ordersG + ordersG + ordersF;
        usedAF = externalsAF + orders + ordersG + ordersG;
       
(* Rename of internal indices (b,rho), and evaluation of bcount and rhocount *)

        Do[pdep=0; 
           While[!FreeQ[vertices[[i]], p[pdep+1]], pdep+=1];
           pdeprules=Table[Rule[p[idep],p[pcount+idep]], {idep, 1, pdep}];
           If[pdep!=0 && pcount!=0, localvertices[[i]]=localvertices[[i]] /. 
           pdeprules];
           pcount+=pdep;
 
           bdep=0; 
           While[!FreeQ[vertices[[i]], b[bdep+1]], bdep+=1];
           bdeprules=Table[Rule[b[idep],b[bcount+idep]], {idep, 1, bdep}];
           If[ bdep!=0 && bcount!=0, localvertices[[i]]=localvertices[[i]] /. 
           bdeprules];
           bcount+=bdep;

           bfdep=0; 
           While[!FreeQ[vertices[[i]], bf[bfdep+1]], bfdep+=1];
           bfdeprules=Table[Rule[bf[idep],bf[bfcount+idep]], {idep, 1, bfdep}];
           If[ bfdep!=0 && bfcount!=0, localvertices[[i]]=localvertices[[i]] /.
           bfdeprules];
           bfcount+=bfdep;

           rhodep=0; 
           While[!FreeQ[vertices[[i]], rho[rhodep+1]], rhodep+=1];
           rhodeprules=Table[Rule[rho[idep],rho[rhocount+idep]], 
           {idep, 1, rhodep}];
           If[rhodep!=0 && rhocount!=0, localvertices[[i]]=localvertices[[i]] /.
           rhodeprules]; 
           rhocount+=rhodep;

           frhodep=0; 
           While[!FreeQ[vertices[[i]], frho[frhodep+1]], frhodep+=1];
           frhodeprules=Table[Rule[frho[idep],frho[frhocount+idep]], 
           {idep, 1, frhodep}];
           If[frhodep!=0 && frhocount!=0, localvertices[[i]]=localvertices[[i]]
            /. frhodeprules]; 
           frhocount+=frhodep,
          {i, numbervertices}];

(* Partial symmetrization of the vertex list; the part below which
regards ghosts is trivial, unless there are any effective vertices
present, which might contain more than one ghost-antighost pair    *)

        Do[localvertices[[i]] =
             (symmetrizepartially[localvertices[[i]], 
                                  Prepend[contractions[[i]],externals[[i]]],
                                  0 ])
              // Expand // renamem // canonical ;
           localvertices[[i]] =
             (symmetrizepartially[localvertices[[i]], 
                                  Prepend[contractionsG[[i]],externalsAG[[i]]],
                                  orders[[i]] ])
              // Expand // renamem // canonical ;
           localvertices[[i]] =
             (symmetrizepartially[localvertices[[i]], 
                                  Prepend[(#[[i]])& /@ contractionsG,externalsG[[i]]],
                                  orders[[i]]+ordersG[[i]] ])
              // Expand // renamem // canonical ;
            localvertices[[i]] =
             (symmetrizepartially[localvertices[[i]], 
                                  Prepend[contractionsF[[i]],externalsAF[[i]]],
                                  orders[[i]]+ordersG[[i]]+ordersG[[i]] ])
              // Expand // renamem // canonical ;
           localvertices[[i]] =
             (symmetrizepartially[localvertices[[i]], 
                                  Prepend[(#[[i]])& /@ contractionsF,externalsF[[i]]],
                                  orders[[i]]+ordersG[[i]]+ordersG[[i]]+ordersF[[i]] ])
              // Expand // renamem // canonical ,
         {i, numbervertices}];    

(* Rename indices which remain external after contractions *)

        Do[qrules = Table[Rule[k[iexternal], q[extindex+iexternal]], 
                          {iexternal, externals[[i]] }];
           arules = Table[Rule[c[iexternal], a[extindex+iexternal]],
                          {iexternal, externals[[i]] }];
           nurules= Table[Rule[mu[iexternal],nu[extindex+iexternal]],
                          {iexternal, externals[[i]] }];
           If[externals[[i]] !=0,localvertices[[i]] = localvertices[[i]] /. qrules /. arules /. nurules];
           extindex += externals[[i]],
           {i, numbervertices}];
        Do[qrules = Table[Rule[k[orders[[i]]+iexternal], q[extindex+iexternal]], 
                          {iexternal, externalsAG[[i]] }];
           arules = Table[Rule[c[orders[[i]]+iexternal], a[extindex+iexternal]],
                          {iexternal, externalsAG[[i]] }];
           If[externalsAG[[i]] !=0,localvertices[[i]] = localvertices[[i]] /. qrules /. arules];
           extindex += externalsAG[[i]],
           {i, numbervertices}];
        Do[qrules = Table[Rule[k[orders[[i]]+ordersG[[i]]+iexternal],
                               q[extindex+iexternal]], 
                          {iexternal, externalsG[[i]] }];
           arules = Table[Rule[c[orders[[i]]+ordersG[[i]]+iexternal],
                               a[extindex+iexternal]],
                          {iexternal, externalsG[[i]] }];
           If[externalsG[[i]] !=0,localvertices[[i]] = localvertices[[i]] /. qrules /. arules];
           extindex += externalsG[[i]],
           {i, numbervertices}];
          Do[qrules = Table[Rule[k[orders[[i]]+ordersG[[i]]+ordersG[[i]]+
                      iexternal], q[extindex+iexternal]], 
                          {iexternal, externalsAF[[i]] }];
           afrules = Table[Rule[cf[orders[[i]]+ordersG[[i]]+ordersG[[i]] +
                     iexternal], af[extindex+iexternal]],
                          {iexternal, externalsAF[[i]] }];
           fnurules= Table[Rule[fmu[orders[[i]]+ordersG[[i]]+ordersG[[i]]+
                     iexternal],fnu[extindex+iexternal]],
                          {iexternal, externalsAF[[i]] }];
           If[externalsAF[[i]] !=0,localvertices[[i]] = localvertices[[i]] /. qrules /. afrules /. fnurules];
           extindex += externalsAF[[i]],
           {i, numbervertices}];
          Do[qrules = Table[Rule[k[orders[[i]]+ordersG[[i]]+ordersG[[i]]+
                      ordersF[[i]]+iexternal], q[extindex+iexternal]], 
                          {iexternal, externalsF[[i]] }];
           afrules = Table[Rule[cf[orders[[i]]+ordersG[[i]]+ordersG[[i]] +
                     ordersF[[i]]+iexternal], af[extindex+iexternal]],
                          {iexternal, externalsF[[i]] }];
           fnurules= Table[Rule[fmu[orders[[i]]+ordersG[[i]]+ordersG[[i]]+
                     ordersF[[i]]+iexternal],fnu[extindex+iexternal]],
                          {iexternal, externalsF[[i]] }];
           If[externalsF[[i]] !=0,localvertices[[i]] = localvertices[[i]] /. qrules /. afrules /. fnurules];
           extindex += externalsF[[i]],
           {i, numbervertices}]; 
(* Let us complete the necessary symmetrization of the vertices. We
recall that, in order to avoid superfluous symmetrizations:
     1) We do not symmetrize over external legs
     2) If the ith and jth vertex (i<j) are connected through n>1
        gluon lines, we symmetrize only over the n legs of the jth vertex.
     3) If 2n legs from the ith vertex are contracted among themselves, 
        we symmetrize only over (2n-1)!! permutations.
     4) If n>1 antighost legs from the ith vertex are contracted with 
        n ghost legs from the jth vertex (i<j, i=j, i>j), we symmetrize
        only over the antighost legs.                                 *)

        Do[localvertices[[i]] = 
             symmetrizeauto[localvertices[[i]],
                            used[[i]]+(Plus@@(Take[contractions[[i]],i-1]))+1,
                            used[[i]]+(Plus@@(Take[contractions[[i]],i]))],
           {i,numbervertices}];
        Do[Do[localvertices[[j]] = 
                symmetrize[localvertices[[j]],
                           used[[j]]+(Plus@@(Take[contractions[[j]],i-1]))+1, 
                           used[[j]]+(Plus@@(Take[contractions[[j]],i]))],
              {j,i+1,numbervertices}],
           {i,numbervertices}];
        Do[Do[localvertices[[i]] = 
                symmetrize[localvertices[[i]],
                           usedAG[[i]]+(Plus@@(Take[contractionsG[[i]],j-1]))+1, 
                           usedAG[[i]]+(Plus@@(Take[contractionsG[[i]],j]))],
              {j,numbervertices}],
           {i,numbervertices}];
        Do[Do[localvertices[[i]] = 
                symmetrize[localvertices[[i]],
                          usedAF[[i]]+(Plus@@(Take[contractionsF[[i]],j-1]))+1, 
                          usedAF[[i]]+(Plus@@(Take[contractionsF[[i]],j]))],
              {j,numbervertices}],
           {i,numbervertices}];
        Do[localvertices[[i]] = localvertices[[i]] // Expand // renamem 
                                // canonical ,
           {i,numbervertices}];

(* Self contractions of vertices, and contractions of the ith and jth vertex;
   These two operations are performed simultaneously, in order to respect the
   order of indices, as imposed by `symmetrizepartially' above               *)

        Do[Do[++used[[i]];++used[[i]];
              ++pcount;++bcount;++rhocount;++rhocount;
              localvertices[[i]] =
                contract1[localvertices[[i]], used[[i]]-1, used[[i]],
                          pcount, bcount, rhocount-1, rhocount];
              propprod *= prop[p[pcount], rho[rhocount-1], rho[rhocount]],
              {contractions[[i,i]]/2}];
           Do[Do[localvertices[[i]] = 
                   localvertices[[i]] /. k[++used[[i]] ] -> p[++pcount]
                                     /. c[used[[i]] ] -> b[++bcount]
                                     /. mu[used[[i]] ] -> rho[++rhocount];
                 localvertices[[j]] = 
                   localvertices[[j]] /. k[++used[[j]] ] -> -p[pcount]
                                     /. c[used[[j]] ] -> b[bcount]
                                     /. mu[used[[j]] ] -> rho[++rhocount];
                 propprod *= prop[p[pcount], rho[rhocount-1], rho[rhocount]],
                 {contractions[[i,j]]}],
              {j, i+1, numbervertices}],
           {i, numbervertices}];
        Do[Do[If[i==j,
                 Do[++usedG[[i]];++usedAG[[i]];++pcount;++bcount;
                    localvertices[[i]] =
                      contract1[localvertices[[i]],usedAG[[i]],usedG[[i]],
                                pcount, bcount, 0, 0];
                    propprod *= propG[p[pcount]],
                    {contractionsG[[i,i]]}],
                 Do[localvertices[[i]] = 
                      localvertices[[i]] /. k[++usedAG[[i]]] -> p[++pcount]
                                        /. c[usedAG[[i]]] -> b[++bcount];
                    localvertices[[j]] = 
                      localvertices[[j]] /. k[++usedG[[j]]] -> p[pcount]
                                        /. c[usedG[[j]]] -> b[bcount];
                    propprod *= propG[p[pcount]],
                    {contractionsG[[i,j]]}]],
              {j, numbervertices}],
           {i, numbervertices}];
          Do[Do[If[i==j,
                 Do[++usedAF[[i]];++usedF[[i]];++pcount;++bfcount;
                    ++frhocount;++frhocount;++rhocount;
                    localvertices[[i]] =
                      contractF1[localvertices[[i]],usedAF[[i]],usedF[[i]],
                                pcount, bfcount, frhocount-1, frhocount];
                    propprod *= propF[p[pcount],frho[frhocount-1],frho[frhocount],rho[rhocount]],
                    {contractionsF[[i,i]]}],
                 Do[localvertices[[i]] = 
                    localvertices[[i]] /. k[++usedAF[[i]]] -> p[++pcount]
                                      /. cf[usedAF[[i]]] -> bf[++bfcount]
                                      /. fmu[usedAF[[i]]] -> frho[++frhocount];
                    localvertices[[j]] = 
                    localvertices[[j]] /. k[++usedF[[j]]] -> p[pcount]
                                      /. cf[usedF[[j]]] -> bf[bfcount]
                                      /. fmu[usedF[[j]]] -> frho[++frhocount];
                    propprod *= propF[p[pcount],frho[frhocount-1],frho[frhocount]                               ,rho[++rhocount]],
                    {contractionsF[[i,j]]}]],
              {j, numbervertices}],
           {i, numbervertices}];
(* Propagator product *)

        propprod * Product[localvertices[[i]], {i, numbervertices}]
        ]


contract1[vertex_,used1_,used2_,pcount_,bcount_,rhocount1_,rhocount2_]:=
            contract2[vertex /. c[used1]  -> b[bcount] 
                             /. c[used2]  -> b[bcount]
                             /. mu[used1] -> rho[rhocount1]
                             /. mu[used2] -> rho[rhocount2],
                      used1,used2,pcount,rhocount1]

contract2[vertex_,used1_,used2_,pcount_,rhocount1_]:=
      vertex /; FreeQ[vertex,k[used1]]&&FreeQ[vertex,k[used2]]
contract2[vertex_Plus,a__]:= contract2[#,a]& /@ vertex
contract2[expr_,used1_,used2_,pcount_,rhocount1_]:=
    contract2[Select[expr,(!FreeQ[#,rho] || 
                           !FreeQ[#,k[used1]] || 
                           !FreeQ[#,k[used2]])&],used1,used2,pcount,rhocount1] *
    Select[expr,(FreeQ[#,rho] && 
                 FreeQ[#,k[used1]] && 
                 FreeQ[#,k[used2]])&] /;
    SameQ[Head[expr],Times] && 
    (Or @@ ((FreeQ[#,rho] && FreeQ[#,k[used1]] && FreeQ[#,k[used2]])& /@ List @@ expr))
contract2[expr_,a__]:= contract3[expr,a] /; !SameQ[Head[expr],Plus] 

contract3[expr_Times,used1_,used2_,pcount_,rhocount1_]:= 
  Block[{pref=1, rest=1},
        Do[If[MemberQ[{delm,epsilon},Head[expr[[j]]] ],
                pref *= expr[[j]],
                rest *= expr[[j]] ],
            {j,Length[expr]} ];
        pref * contract4[rest,used1,used2,pcount,rhocount1,pref]]
contract3[expr_,a__]:= contract4[expr,a,1] /; !(Head[expr]===Times)

contract4[expr_Plus,a__]:= contract4[#,a]& /@ expr
contract4[expr_,used1_,used2_,pcount_,rhocount1_,pref_]:=
      Block[{expr1}, expr1 = canonical[expr /. k[used1] ->  p[pcount] 
                                            /. k[used2] -> If[rhocount1!=0,-p[pcount],p[pcount]]];
                     expr1 = expr1 * nDim^(Length[Union[rhos[expr],rhos[pref]]] -
                                           Length[Union[rhos[expr1],rhos[pref]]])]

rhos[expr_] := expr[[Sequence @@ #]]& /@ Position[expr,rho[_]]


contractF1[vertex_,usedf1_,usedf2_,pcount_,bfcount_,frhocount1_,frhocount2_]:=
            contractF2[vertex /. cf[usedf1]  -> bf[bfcount] 
                             /. cf[usedf2]  -> bf[bfcount]
                             /. fmu[usedf1] -> frho[frhocount1]
                             /. fmu[usedf2] -> frho[frhocount2],
                      usedf1,usedf2,pcount]

contractF2[vertex_,usedf1_,usedf2_,pcount_]:=
      vertex /; FreeQ[vertex,k[usedf1]]&&FreeQ[vertex,k[usedf2]]
contractF2[vertex_Plus,a__]:= contractF2[#,a]& /@ vertex
contractF2[expr_,usedf1_,usedf2_,pcount_]:=
    contractF2[Select[expr,(!FreeQ[#,frho] || 
                           !FreeQ[#,k[usedf1]] || 
                           !FreeQ[#,k[usedf2]])&],usedf1,usedf2,pcount] *
    Select[expr,(FreeQ[#,frho] && 
                 FreeQ[#,k[usedf1]] && 
                 FreeQ[#,k[usedf2]])&] /;
    SameQ[Head[expr],Times] && 
    (Or @@ ((FreeQ[#,frho] && FreeQ[#,k[usedf1]] && FreeQ[#,k[usedf2]])& /@ List @@ expr))
contractF2[expr_,a__]:= contractF3[expr,a] /; !SameQ[Head[expr],Plus] 

contractF3[expr_Times,usedf1_,usedf2_,pcount_]:= 
  Block[{pref=1, rest=1},
        Do[If[MemberQ[{delm,epsilon},Head[expr[[j]]] ],
                pref *= expr[[j]],
                rest *= expr[[j]] ],
            {j,Length[expr]} ];
        pref * contractF4[rest,usedf1,usedf2,pcount,pref]]
contractF3[expr_,a__]:= contractF4[expr,a,1] /; !(Head[expr]===Times)

contractF4[expr_Plus,a__]:= contractF4[#,a]& /@ expr
contractF4[expr_,usedf1_,usedf2_,pcount_,pref_]:=
      Block[{expr1}, expr1 = canonical[expr /. k[usedf1] ->  p[pcount] 
                                            /. k[usedf2] -> p[pcount]];
                     expr1 = expr1 * nDim^(Length[Union[frhos[expr],frhos[pref]]] -
                                           Length[Union[frhos[expr1],frhos[pref]]])]

frhos[expr_] := expr[[Sequence @@ #]]& /@ Position[expr,frho[_]]











