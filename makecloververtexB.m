(* This variant is to be applied to the clover term; thus, the relevant lists of
   links are: {1,2,-1,-2}, {2,-1,-2,1}, {-1,-2,1,2}, {-2,1,2,-1}
              {2,1,-2,-1}, {1,-2,-1,2}, {-2,-1,2,1}, {-1,2,1,-2}
   We have defined: sigma[i, mu, nu, j] = im/2 [gamma_mu, gamma_nu]_{ij}                   *)


(* This module takes as input a list of links (listOFlinks) around a closed loop,
   such as:
               {-3,1,2,3,-2,-1}
   and produces the corresponding vertex with nQ quantum gluons and nB background gluons
   The indices 1,2,3, etc. as they appear above, are intended to be freely summed
   over.                                                                                *)

makecloververtex[listOFlinks_, nQ_, nB_] :=
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
                  sigma[fmu[nQ+1], rho[1], rho[2], fmu[nQ+2]] *
                  vertex
         ]
