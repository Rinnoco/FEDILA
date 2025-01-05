(* The folowing program is producing fermion vertices with stout links for nS=1 smearing steps*)

makestoutvertexU[nQ_,nB_] :=
  Module[{Ut,Ut1,Ut2},
	 Ut1 = makestoutvertexUpart1[nQ,nB];
	 Ut2 = If[(nB + nQ)< 3,0,makestoutvertexUpart2[nQ,nB]];
	 If[(nB + nQ) > 5,
         Print["The terms with products of two or more traces are missing!"]];
	 Ut = Ut1 + Ut2;
	 Ut]

  makestoutvertexUpart1[nQ_,nB_] := delta[-k[1] + k[2]]*delm[rho[1],rho[1]]*openspur[cf[1],cf[2]] /; ((nQ + nB)=== 0)

makestoutvertexUpart1[nQ_,nB_] :=
  Module[{listOFlinks,prefactorlist,listOFlinksnew,imin,imax,newentry,
	  prefactornewentry,Ut1},
	 listOFlinks = {{},{2,1,-2,-1},{-2,1,2,-1},{1,2,-1,-2},{1,-2,-1,2}};
	 prefactorlist = Join[{1},w[1]*{1,1,-1,-1}];
	 listOFlinksnew = listOFlinks;
	 imin = 2;
	 Do[
	    imax = n+1; 
	    Do[
	       Do[
		  newentry = Join[listOFlinks[[i]],
		 listOFlinks[[j]] /. {a___,2,b_,-2,c___} -> {a,imax,b,-imax,c}
		                  /. {a___,-2,b_,2,c___} -> {a,-imax,b,imax,c}];
		  prefactornewentry = w[n]*(prefactorlist[[i]] /. w[_] -> 1)*
		                           (prefactorlist[[j]] /. w[_] -> 1);
		  AppendTo[listOFlinksnew,newentry];
		  AppendTo[prefactorlist,prefactornewentry],
		  {j,2,5}],
	       {i,imin,Length[listOFlinks]}];
	    imin = Length[listOFlinks] + 1;
	    listOFlinks = listOFlinksnew,
	      {n,2,nQ+nB}];
	 listOFlinks = Append[#,1]& /@ listOFlinks;
	 listOFlinks = (listOFlinks //. {a___,i_?NumberQ,j_?NumberQ,c___} :> {a,c} /; i+j===0
			);	       
	 prefactorlist = prefactorlist /. w[i_] :> w^i/(2^i * Factorial[i]); 
    (*	 Ut1 = Sum[prefactorlist[[i]]*makefermionvertex[listOFlinks[[i]],nQ,nB],{i,Length[listOFlinks]}]; *)
    Ut1 = Inner[Times,prefactorlist,Fold[Flatten[{#1,makefermionvertexnew[#2,nQ,nB]}]&,{},listOFlinks],Plus];
	 Ut1]

(* THE FOLLOWING IS WORKING ONLY FOR nB + nQ < 6 !!! *)

makestoutvertexUpart2[nQ_,nB_] :=
  Module[{},
	 listOFlinks = {{2,1,-2,-1},{-2,1,2,-1},{1,2,-1,-2},{1,-2,-1,2}};
	 Ut2 = 0;
	 Do[
	    nQimin = If[nBi>3,0,3-nBi];
	    Do[
	       Ut2a = Table[makegluonvertex[listOFlinks[[i]],nQi,nBi],{i,Length[listOFlinks]}];
	       Ut2a = Expand[(Ut2a[[1]]+Ut2a[[2]]-Ut2a[[3]]-Ut2a[[4]])*(-w/(2*Nc))];
	       Ut2b = makestoutvertexUpart1[nQ-nQi,nB-nBi] /. k[i_] :> k[i + nQi] /. mu[i_] :> mu[i + nQi] /. c[i_] :> c[i + nQi] /. q[i_] :> q[i + nBi] /. nu[i_] :> nu[i + nBi] /. a[i_] :> a[i + nBi] /. cf[i_] :> cf[i + nQi] /. rho[i_] -> rho[i + 2];
	       Ut2 = Ut2 + Expand[Ut2a*Ut2b] /. delta[a_]*delta[b_] :> delta[a+b],
		   {nQi,nQimin,nQ}],	   
	    {nBi,0,nB}];
	 Ut2]

												       
(* in the above: rho[i_] -> rho[i+2] should be: rho[i_?((!(i===1))&)] :> rho[i+1]  
   same comment applies to makestoutvertexUdaggerpart2                               *)


makestoutvertexUdagger[nQ_,nB_] :=
  Module[{Ut,Ut1,Ut2},
	 Ut1 = makestoutvertexUdaggerpart1[nQ,nB];
	 Ut2 = If[(nB + nQ)< 3,0,makestoutvertexUpart2[nQ,nB]];
	 If[(nB + nQ) > 5,
         Print["The terms with products of two or more traces are missing!"]];
	 Ut = Ut1 + Ut2;
	 Ut]

(* in the above: makestoutvertexUpart2dagger!   *)

makestoutvertexUdaggerpart1[nQ_,nB_] := delta[-k[1] + k[2]]*delm[rho[1],rho[1]]*openspur[cf[1],cf[2]] /; ((nQ + nB)=== 0)

makestoutvertexUdaggerpart1[nQ_,nB_] :=
  Module[{listOFlinks,prefactorlist,listOFlinksnew,imin,imax,newentry,
	  prefactornewentry,Ut1},
	 listOFlinks = {{},{2,1,-2,-1},{-2,1,2,-1},{1,2,-1,-2},{1,-2,-1,2}};
	 prefactorlist = Join[{1},w[1]*{1,1,-1,-1}];
	 listOFlinksnew = listOFlinks;
	 imin = 2;
	 Do[
	    imax = n+1; 
	    Do[
	       Do[
		  newentry = Join[listOFlinks[[i]],
		 listOFlinks[[j]] /. {a___,2,b_,-2,c___} -> {a,imax,b,-imax,c}
		                  /. {a___,-2,b_,2,c___} -> {a,-imax,b,imax,c}];
		  prefactornewentry = w[n]*(prefactorlist[[i]] /. w[_] -> 1)*
		                           (prefactorlist[[j]] /. w[_] -> 1);
		  AppendTo[listOFlinksnew,newentry];
		  AppendTo[prefactorlist,prefactornewentry],
		  {j,2,5}],
	       {i,imin,Length[listOFlinks]}];
	    imin = Length[listOFlinks];
	    listOFlinks = listOFlinksnew,
	      {n,2,nQ+nB}];
	 listOFlinks = Prepend[#,-1]& /@ listOFlinks;
	 listOFlinks = (listOFlinks //. {a___,i_?NumberQ,j_?NumberQ,c___} :> {a,c} /; i+j===0
			);	       
    prefactorlist = prefactorlist /. w[i_] :> (-1)^i*w^i/(2^i * Factorial[i]);
    (*         Ut1 = Sum[prefactorlist[[i]]*makefermionvertex[listOFlinks[[i]],nQ,nB],{i,Length[listOFlinks]}]; *)
    Ut1 = Inner[Times,prefactorlist,Fold[Flatten[{#1,makefermionvertexnew[#2,nQ,nB]}]&,{},listOFlinks],Plus];
	 Ut1]

(* THE FOLLOWING IS WORKING ONLY FOR nB + nQ < 6 !!! *)

makestoutvertexUdaggerpart2[nQ_,nB_] :=
  Module[{},
	 listOFlinks = {{2,1,-2,-1},{-2,1,2,-1},{1,2,-1,-2},{1,-2,-1,2}};
	 Ut2 = 0;
	 Do[
	    nQimin = If[nBi>3,0,3-nBi];
	    Do[
	       Ut2a = Table[makegluonvertex[listOFlinks[[i]],nQi,nBi],{i,Length[listOFlinks]}];
	       Ut2a = Expand[(Ut2a[[1]]+Ut2a[[2]]-Ut2a[[3]]-Ut2a[[4]])*(w/(2*Nc))];
	       Ut2b = makestoutvertexUpart1[nQ-nQi,nB-nBi] /. k[i_] :> k[i + nQi] /. mu[i_] :> mu[i + nQi] /. c[i_] :> c[i + nQi] /. q[i_] :> q[i + nBi] /. nu[i_] :> nu[i + nBi] /. a[i_] :> a[i + nBi] /. rho[i_] -> rho[i + 2];
	       Ut2 = Ut2 + Expand[Ut2a*Ut2b] /. delta[a_]*delta[b_] :> delta[a+b],
		   {nQi,nQimin,nQ}],	   
	    {nBi,0,nB}];
	 Ut2]

(* one must include in the above: /. cf[i_] :> cf[i + nQi]    *)

makefermionvertex[listOFlinks_, nQ_, nB_] :=
  Module[{ll,f,BQ,BQlist,
          offsets,
          fieldslist, weightlist, fieldslistnew, weightlistnew,
          vertex},

(* offsets = {{-3},{-3},{-3,1},{-3,1,2},{-3,1,2,3,-2},{-3,1,2,3,-2,-1}}                 *)

         offsets = Table[If[Sign[listOFlinks[[i]]] > 0,
                            Take[listOFlinks,i-1],
                            Take[listOFlinks,i]],
                         {i, Length[listOFlinks]}];

(* offsets = {{-3},{-3},{-3,1},{-3,1,2},{1},{}}                                         *)

         offsets = (offsets //. {a___,i_?NumberQ,b___,j_?NumberQ,c___} :> {a,b,c} /; i+j===0);

(* offsets = {{-rho[3]},{-rho[3]},{-rho[3],rho[1]},{-rho[3],rho[1],rho[2]},{rho[1]},{}} *)

         offsets = Map[rho,offsets,{2}];
         offsets = (offsets /. rho[a_?Negative] :> - rho[-a]);

(* ll = {{-1,rho[3],{-rho[3]}},
         { 1,rho[1],{-rho[3]}},
         { 1,rho[2],{-rho[3],rho[1]}},
         { 1,rho[3],{-rho[3],rho[1],rho[2]}},
         {-1,rho[2],{rho[1]}},
         {-1,rho[1],{}}}                                                                *)

         ll = Table[{Sign[listOFlinks[[i]]],
                     rho[Abs[listOFlinks[[i]]]],
                     offsets[[i]]},                     
                    {i, Length[listOFlinks]}];

         fieldslist = Expand[(Sum[f[i],{i,2*Length[listOFlinks]}])^(nQ+nB) / Factorial[nQ+nB]];
         weightlist = (List @@ fieldslist) /. f[_] -> 1;
         fieldslist = (List @@ fieldslist) / ((List @@ fieldslist) /. f[_]->1);
         fieldslist = List /@ fieldslist;
         fieldslist = fieldslist //. {a___, b_ c_, d___} :> {a,b,c,d};
         fieldslist = fieldslist //. {a___, b_^i_, d___} :> {a,b,b^(i-1),d};
         fieldslist = Map[(#[[1]])& , fieldslist, {2}];
         Do[If[ll[[i,1]]==1, BQ[2i-1]=1; BQ[2i]=0, BQ[2i-1]=0; BQ[2i]=1],
            {i,Length[listOFlinks]}];
         ll = Join @@ (({#,#})& /@ ll);
         BQlist = Map[BQ, fieldslist, {2}];
         BQlist = (Plus @@ #)& /@ BQlist;
         fieldslistnew = {};
         weightlistnew = {};
         Do[If[BQlist[[i]]==nQ, AppendTo[fieldslistnew,fieldslist[[i]]];
                                AppendTo[weightlistnew,weightlist[[i]]]],
            {i,Length[BQlist]}];
         fieldslist = fieldslistnew;
         weightlist = weightlistnew;

         resultlist = {};
         Do[temp = 1;
            spurlist = {};
            jQ = 0; jB = 0;
            Do[If[BQ[fieldslist[[i,j]]]==1,
                  jQ = jQ + 1;
                  AppendTo[spurlist, c[jQ]]; 
                  temp = temp * delm[mu[jQ],ll[[fieldslist[[i,j]],2]]]*
                         ll[[fieldslist[[i,j]],1]] *
                         Product[phi2[2 k[jQ], ll[[fieldslist[[i,j]],3,ii]]],
                                 {ii,Length[ll[[fieldslist[[i,j]],3]]]}],
                  jB = jB + 1; 
                  AppendTo[spurlist, a[jB]]; 
                  temp = temp * delm[nu[jB],ll[[fieldslist[[i,j]],2]]]*
                         ll[[fieldslist[[i,j]],1]] *
                         Product[phi2[2 q[jB], ll[[fieldslist[[i,j]],3,ii]]],
                                 {ii,Length[ll[[fieldslist[[i,j]],3]]]}]],
               {j,nQ+nB}];
            AppendTo[resultlist,temp * (openspur @@ Append[Prepend[spurlist,cf[nQ+1]],cf[nQ+2]])],
            {i,Length[fieldslist]}];

         vertex = Sum[weightlist[[i]] * resultlist[[i]],
                      {i,Length[fieldslist]}];

         vertex = (g im)^nQ * (alatt im)^nB *
                  delta[(Plus @@ (k /@ Range[nQ])) + (Plus @@ (q /@ Range[nB])) - k[nQ+1] + k[nQ+2]] *
                  Product[phi2[k[j],mu[j]],{j,nQ}] * Product[phi2[q[j],nu[j]],{j,nB}] *
		  (Times @@ (delm[rho[#],rho[#]]& /@ Union[Abs[listOFlinks]])) *
                  vertex
         ]



makefermionvertexnew[listOFlinks_, nQ_, nB_] :=
  Module[{ll,f,BQ,BQlist,
          offsets,
          fieldslist, weightlist,
          vertex},

(* offsets = {{-3},{-3},{-3,1},{-3,1,2},{-3,1,2,3,-2},{-3,1,2,3,-2,-1}}                 *)

         offsets = Table[If[Sign[listOFlinks[[i]]] > 0,
                            Take[listOFlinks,i-1],
                            Take[listOFlinks,i]],
                         {i, Length[listOFlinks]}];

(* offsets = {{-3},{-3},{-3,1},{-3,1,2},{1},{}}                                         *)

         offsets = (offsets //. {a___,i_?NumberQ,b___,j_?NumberQ,c___} :> {a,b,c} /; i+j===0);

(* offsets = {{-rho[3]},{-rho[3]},{-rho[3],rho[1]},{-rho[3],rho[1],rho[2]},{rho[1]},{}} *)

         offsets = Map[rho,offsets,{2}];
         offsets = (offsets /. rho[a_?Negative] :> - rho[-a]);

(* ll = {{-1,rho[3],{-rho[3]}},
         { 1,rho[1],{-rho[3]}},
         { 1,rho[2],{-rho[3],rho[1]}},
         { 1,rho[3],{-rho[3],rho[1],rho[2]}},
         {-1,rho[2],{rho[1]}},
         {-1,rho[1],{}}}                                                                *)

         ll = Table[{Sign[listOFlinks[[i]]],
                     rho[Abs[listOFlinks[[i]]]],
                     offsets[[i]]},                     
                    {i, Length[listOFlinks]}];
	 Do[If[ll[[i,1]]==1, BQ[2i-1]=1; BQ[2i]=0, BQ[2i-1]=0; BQ[2i]=1],
            {i,Length[listOFlinks]}];
         ll = Join @@ (({#,#})& /@ ll);
         fieldslist = Expand[(Sum[f[i],{i,2*Length[listOFlinks]}])^(nQ+nB) / Factorial[nQ+nB]];
(* In the case of a list with 17 elements (Q*Q*Q*Q*U), 
   where Q is the exponent appearing in the definition of stout links,
   the above statement can be simplified as (assuming that neighboring links which are inverse of 
   each other have NOT been eliminated from the list):
   (This is correct assuming that nQ+nB=4, so that only 1 gluon is taken from every Q  )
         If[Length[listOFlinks]===17,
            fieldslist = Expand[(f[1] +f[2] +f[3] +f[4] +f[5] +f[6] +f[7] +f[8])*
                                (f[9] +f[10]+f[11]+f[12]+f[13]+f[14]+f[15]+f[16])*
                                (f[17]+f[18]+f[19]+f[20]+f[21]+f[22]+f[23]+f[24])*
                                (f[25]+f[26]+f[27]+f[28]+f[29]+f[30]+f[31]+f[32])],
            fieldslist = Expand[(Sum[f[i],{i,2*Length[listOFlinks]}])^(nQ+nB) / Factorial[nQ+nB]]];  *)
	 weightlist = (List @@ fieldslist) /. f[_] -> 1;
	 fieldslist = (List @@ fieldslist) / ((List @@ fieldslist) /. f[_]->1);
	 fieldslist = (If[Head[#] === Times,List @@ #,List[#]])& /@ fieldslist;
	 fieldslist = Map[(# /. f[b_]^i_ :> (Sequence @@ Table[f[b],{j,i}]))&,fieldslist,{2}];
	 BQlist = fieldslist /. f[i_] :> BQ[i];
	 BQlist = (Plus @@ #)& /@ BQlist;
	 poslist = Position[BQlist,nQ];
	 weightlist = weightlist[[#[[1]]]]& /@ poslist; 
       	 fieldslist = fieldslist[[#[[1]]]]& /@ poslist;
	 fieldslist = (#*(Q /@ Range[Length[#]]))& /@ fieldslist;
	 fieldslist = fieldslist /. f[i_]*Q[j_] :> If[BQ[i] === 1, f[i]*Q[j],f[i]*B[j]];
         fieldslist = reduceQ /@ fieldslist;
	 fieldslist = reduceB /@ fieldslist;
	 openspurlist = fieldslist /. f[i_]*Q[j_] :> c[j] /. f[i_]*B[j_] :> a[j];
	 openspurlist = (openspur @@ Append[Prepend[#,cf[nQ+1]],cf[nQ+2]])& /@ openspurlist;
	 resultlist = fieldslist /. f[i_]*Q[j_] :> delm[mu[j],ll[[i,2]]]*ll[[i,1]]*Product[phi2[2 k[j], ll[[i,3,ii]]],{ii,Length[ll[[i,3]]]}];
	 resultlist = resultlist /. f[i_]*B[j_] :> delm[nu[j], ll[[i,2]]]*ll[[i,1]]*Product[phi2[2 q[j], ll[[i,3,ii]]],{ii,Length[ll[[i,3]]]}]; 
	 resultlist = (Times @@ #)& /@ resultlist;	 
	 vertex = Inner[Times,weightlist,resultlist*openspurlist,Plus];
         vertex = (g im)^nQ * (alatt im)^nB *
                  delta[(Plus @@ (k /@ Range[nQ])) + (Plus @@ (q /@ Range[nB])) - k[nQ+1] + k[nQ+2]] *
                  Product[phi2[k[j],mu[j]],{j,nQ}] * Product[phi2[q[j],nu[j]],{j,nB}] *
		  (Times @@ (delm[rho[#],rho[#]]& /@ Union[Abs[listOFlinks]])) *
                  vertex
         ]


reduceQ[a_] := Block[{listQ},
		 listQ = Union[ (a[[ Sequence @@ # ]]) & /@ Position[a,Q[_] ] ];
	  	 a /. Inner[Rule,listQ,Array[Q[#]&,Length[listQ]],List]
			    ]

reduceB[a_] := Block[{listB},
		 listB = Union[ (a[[ Sequence @@ # ]]) & /@ Position[a,B[_] ] ];
	  	 a /. Inner[Rule,listB,Array[B[#]&,Length[listB]],List]
			    ]
