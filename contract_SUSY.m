(* To make this version run faster, instances of:
        canonical // rorder // collectCFirst 
   have been replaced by:
        canonical // collectCFirst                 *)
(* In this version, use of collectCFirst has been eliminated
   altogether, since it lead to an imcompatible input format for 
   contract1                                                      *)

(* Contraction of a list of vertices, which may contain gluons, gluinos, ghosts, quarks
   and/or squarks (plus/minus)

   Note: 1) No extra factors of (-1) are assigned to closed loops of fermions
         2) The (ij)th element of the matrix `contractionsGh' indicates
            the number of contractions among antighosts from the ith
            and ghosts from the jth vertex. Consequently, this matrix 
            is not symmetric; in this case, 'contract' should be
            called separately for each version of the matrix
         3) The (ij)th element of the matrix `contractionsQ' indicates
            the number of contractions among antiquarks from the ith
            and quarks from the jth vertex.
	    The (ij)th element of the matrix `contractionsg' indicates
            the number of contractions among antigluino from the ith
            and gluino from the jth vertex.
	    The (ij)th element of the symmetric matrix `contractionsgbgb' indicates
            the number of contractions among antigluinos from the ith
            and the jth vertex.
	    The (ij)th element of the symmetric matrix `contractionsgg' indicates
            the number of contractions among gluinos from the ith
            and the jth vertex.
	    The (ij)th element of the matrix `contractionsAp' indicates
            the number of contractions among squark A+dagger from the ith
            and A+ from the jth vertex.
	    The (ij)th element of the matrix `contractionsAm' indicates
            the number of contractions among squark A-dagger from the ith
            and A- from the jth vertex.
         4) Each vertex is intended to be multiplied by:
              Gluon[k[1],mu[1],c[1]] * ... * Gluon[k[Ngluon],mu[Ngluon],c[Ngluon]] *
	      gluinobar[k[Ngluon+1],fmu[Ngluon+1],c[Ngluon+1]] * ... * gluinobar[k[Ngluon+Ngluinobar],fmu[Ngluon+Ngluinobar],c[Ngluon+Ngluino]] * ...
	      (similarly for gluino[k[...],fmu[...], c[...]],
	                     ghostbar[k[...],c[...]],
			     ghost[k[...],c[...]],
			     Psibar[k[...],fmu[...], cf[...]],
			     Psi[k[...],fmu[...], cf[...]],
			     Aplusdag[k[...],cf[...]],
			     Aplus[k[...],cf[...]],
			     Aminusdag[k[...],cf[...]],
			     Aminus[k[...],cf[...]])   
         5) Each vertex will be of the form:
            {{Ngluon, Nghostpair, Ngluinobar, Ngluino, Nquarkbar, Nquark, NAplusdag, NAplus, NAminusdag, NAminus}, expression}, 
              where:  Ngluon    is the number of gluon legs, and similarly for all other Nxxx
              expression is the expression for the vertex itself
	 6) The final Green's function will depend on:
	      q[i]   (momenta)
	      nu[i]  (Lorentz)
	      a[i]   (color adjoint)
	      fnu[i] (Dirac)
	      af[i]  (color fundamental)
	      where the first values of the index i refer to external gluons, the next values to external gluinobar, and so on, in the order:
	         {gluon, gluinobar, gluino, ghostbar, ghost, Psibar, Psi, Aplusdag, Aplus, Aminusdag, Aminus}
              Note that, in case the vertices of the Green's function contain "open" indices, these indices must be given values which do not
	      clash with the values assigned to external fields by "contract"
                                                                                                                                   *)


contract[vertices_, contractionsG_, contractionsGh_, contractionsQ_] :=
    contract[vertices, contractionsG, contractionsGh,
             ConstantArray[0, {Length[vertices],Length[vertices]}],
	     ConstantArray[0, {Length[vertices],Length[vertices]}],
	     ConstantArray[0, {Length[vertices],Length[vertices]}],
	     contractionsQ,
	     ConstantArray[0, {Length[vertices],Length[vertices]}],
	     ConstantArray[0, {Length[vertices],Length[vertices]}]]
									      
									      
contract[vertices_, contractionsG_, contractionsGh_, contractionsg_,
         contractionsgbgb_, contractionsgg_, contractionsQ_,
	 contractionsAp_, contractionsAm_] := 
  Block[{pcount=0, pdep, pdeprules, qrules,                            
         bcount=0, bdep, bdeprules, arules,
         rhocount=0, rhodep, rhodeprules, nurules,
         bfcount=0, bfdep, bfdeprules, afrules,
	 frhocount=0, frhodep, frhodeprules, fnurules,
	 idep, iexternal,
	 localvertices, numbervertices,
	 ordersG, ordersGh, ordersgb, ordersg, ordersQb, ordersQ, ordersApd, ordersAp, ordersAmd, ordersAm, 
	 externalsG, externalsgb, externalsg, externalsaGh, externalsGh, externalsQb, externalsQ, externalsApd, externalsAp, externalsAmd, externalsAm,
	 usedG, usedgb, usedg, usedaGh, usedGh, usedQb, usedQ, usedApd, usedAp, usedAmd, usedAm,
         extindex=0, propprod=1},

        localvertices = (#[[2]])& /@ vertices;
        numbervertices=Length[vertices];
        ordersG   = (#[[1,1]])&  /@ vertices; (* How many gluons      are contained in vertex1, vertex2, etc. *)
        ordersGh  = (#[[1,2]])&  /@ vertices; (* How many ghost pairs are contained in vertex1, vertex2, etc. *)
        ordersgb  = (#[[1,3]])&  /@ vertices; (* How many gluinobars  are contained in vertex1, vertex2, etc. *)
        ordersg   = (#[[1,4]])&  /@ vertices; (* How many gluinos     are contained in vertex1, vertex2, etc. *)
        ordersQb  = (#[[1,5]])&  /@ vertices; (* How many antiquarks  are contained in vertex1, vertex2, etc. *)
        ordersQ   = (#[[1,6]])&  /@ vertices; (* How many quarks      are contained in vertex1, vertex2, etc. *)
        ordersApd = (#[[1,7]])&  /@ vertices; (* How many Aplusdag    are contained in vertex1, vertex2, etc. *)
        ordersAp  = (#[[1,8]])&  /@ vertices; (* How many Aplus       are contained in vertex1, vertex2, etc. *)
        ordersAmd = (#[[1,9]])&  /@ vertices; (* How many Aminusdag   are contained in vertex1, vertex2, etc. *)
        ordersAm  = (#[[1,10]])& /@ vertices; (* How many Aminus      are contained in vertex1, vertex2, etc. *)
        externalsG =Table[ordersG[[i]]-Sum[contractionsG[[i,j]],{j, numbervertices}],
	                  {i, numbervertices}];   (* How many gluons  from the ith vertex remain external after contraction *)
        externalsgb=Table[ordersgb[[i]]-Sum[contractionsg[[i,j]],{j, numbervertices}]-Sum[contractionsgbgb[[i,j]],{j,numbervertices}],
	                  {i, numbervertices}];  (* How many antigluinos  from the ith vertex remain external after contraction *)
        externalsg =Table[ordersg[[i]]-Sum[contractionsg[[j,i]],{j, numbervertices}]-Sum[contractionsgg[[i,j]],{j,numbervertices}],
	                  {i, numbervertices}];  (* How many gluinos  from the ith vertex remain external after contraction *)
        externalsaGh=Table[ordersGh[[i]]-Sum[contractionsGh[[i,j]],{j, numbervertices}],
	                   {i, numbervertices}]; (* How many antighs from the ith vertex remain external after contraction *)
        externalsGh=Table[ordersGh[[i]]-Sum[contractionsGh[[j,i]],{j, numbervertices}],
	                  {i, numbervertices}];  (* How many ghosts  from the ith vertex remain external after contraction *)
        externalsQb=Table[ordersQb[[i]]-Sum[contractionsQ[[i,j]],{j, numbervertices}],
	                  {i, numbervertices}];  (* How many antiqus from the ith vertex remain external after contraction *)
        externalsQ=Table[ordersQ[[i]]-Sum[contractionsQ[[j,i]],{j, numbervertices}],
	                 {i, numbervertices}]; (* How many quarks  from the ith vertex remain external after contraction *)
        externalsApd=Table[ordersApd[[i]]-Sum[contractionsAp[[i,j]],{j, numbervertices}],
	                  {i, numbervertices}]; (* How many A+dag from the ith vertex remain external after contraction *)
        externalsAp=Table[ordersAp[[i]]-Sum[contractionsAp[[j,i]],{j, numbervertices}],
	                  {i, numbervertices}]; (* How many A+ from the ith vertex remain external after contraction *)
        externalsAmd=Table[ordersAmd[[i]]-Sum[contractionsAm[[i,j]],{j, numbervertices}],
	                  {i, numbervertices}]; (* How many A-dag from the ith vertex remain external after contraction *)
        externalsAm=Table[ordersAm[[i]]-Sum[contractionsAm[[j,i]],{j, numbervertices}],
	                  {i, numbervertices}]; (* How many A- from the ith vertex remain external after contraction *)

        usedG   = externalsG;
	usedgb  = externalsgb  + ordersG;
	usedg   = externalsg   + ordersG + ordersgb;
        usedaGh = externalsaGh + ordersG + ordersgb + ordersg;
        usedGh  = externalsGh  + ordersG + ordersgb + ordersg + ordersGh;
        usedQb  = externalsQb  + ordersG + ordersgb + ordersg + ordersGh + ordersGh;
        usedQ   = externalsQ   + ordersG + ordersgb + ordersg + ordersGh + ordersGh + ordersQb;
        usedApd = externalsApd + ordersG + ordersgb + ordersg + ordersGh + ordersGh + ordersQb + ordersQ;
        usedAp  = externalsAp  + ordersG + ordersgb + ordersg + ordersGh + ordersGh + ordersQb + ordersQ + ordersApd;
        usedAmd = externalsAmd + ordersG + ordersgb + ordersg + ordersGh + ordersGh + ordersQb + ordersQ + ordersApd + ordersAp;
        usedAm  = externalsAm  + ordersG + ordersgb + ordersg + ordersGh + ordersGh + ordersQb + ordersQ + ordersApd + ordersAp + ordersAmd;


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


(* Total symmetrization of the vertex list. We assume that a vertex could contain more than one field of the following types:
   Gluon, A+, A+dag, A-, A-dag                                                                                                   *)

        Do[localvertices[[i]] =
             symmetrize[localvertices[[i]], 1, ordersG[[i]]]
              // Expand // renamem // canonical ;
	   offset = ordersG[[i]] + 2*ordersGh[[i]] + ordersgb[[i]] + ordersg[[i]] + ordersQb[[i]] + ordersQ[[i]];
	   localvertices[[i]] =
             symmetrize[localvertices[[i]], offset+1, offset+ordersApd[[i]]]
              // Expand // renamem // canonical ;
	   offset = offset + ordersApd[[i]];
	   localvertices[[i]] =
             symmetrize[localvertices[[i]], offset+1, offset+ordersAp[[i]]]
              // Expand // renamem // canonical ;
	   offset = offset + ordersAp[[i]];
	   localvertices[[i]] =
             symmetrize[localvertices[[i]], offset+1, offset+ordersAmd[[i]]]
              // Expand // renamem // canonical ;
	   offset = offset + ordersAmd[[i]];
	   localvertices[[i]] =
             symmetrize[localvertices[[i]], offset+1, offset+ordersAm[[i]]]
              // Expand // renamem // canonical ,
         {i, numbervertices}];    

(* Remember that, in what follows, indices are assigned to external fields without any symmetrization;
   such a symmetrization (over indices of same-type external fields) will have to be performed by hand
   after the command contract has finished. This will amount to adding together various mirror diagrams. *)

(* Rename indices which remain external after contractions *)

        Do[qrules = Table[Rule[k[iexternal], q[extindex+iexternal]], 
                          {iexternal, externalsG[[i]] }];
           arules = Table[Rule[c[iexternal], a[extindex+iexternal]],
                          {iexternal, externalsG[[i]] }];
           nurules= Table[Rule[mu[iexternal],nu[extindex+iexternal]],
                          {iexternal, externalsG[[i]] }];
           If[externalsG[[i]] !=0,localvertices[[i]] = localvertices[[i]] /. qrules /. arules /. nurules];
           extindex += externalsG[[i]],
           {i, numbervertices}];
        Do[qrules = Table[Rule[k[ordersG[[i]]+iexternal], q[extindex+iexternal]], 
                          {iexternal, externalsgb[[i]] }];
           arules = Table[Rule[c[ordersG[[i]]+iexternal], a[extindex+iexternal]],
                          {iexternal, externalsgb[[i]] }];
           fnurules= Table[Rule[fmu[ordersG[[i]]+iexternal],fnu[extindex+iexternal]],
                          {iexternal, externalsgb[[i]] }];
           If[externalsgb[[i]] !=0,localvertices[[i]] = localvertices[[i]] /. qrules /. arules /. fnurules];
           extindex += externalsgb[[i]],
           {i, numbervertices}];
        Do[qrules = Table[Rule[k[ordersG[[i]]+ordersgb[[i]]+iexternal], q[extindex+iexternal]], 
                          {iexternal, externalsg[[i]] }];
           arules = Table[Rule[c[ordersG[[i]]+ordersgb[[i]]+iexternal], a[extindex+iexternal]],
                          {iexternal, externalsg[[i]] }];
           fnurules= Table[Rule[fmu[ordersG[[i]]+ordersgb[[i]]+iexternal],fnu[extindex+iexternal]],
                          {iexternal, externalsg[[i]] }];
           If[externalsg[[i]] !=0,localvertices[[i]] = localvertices[[i]] /. qrules /. arules /. fnurules];
           extindex += externalsg[[i]],
           {i, numbervertices}];
        Do[qrules = Table[Rule[k[ordersG[[i]]+ordersgb[[i]]+ordersg[[i]]+iexternal], q[extindex+iexternal]], 
                          {iexternal, externalsaGh[[i]] }];
           arules = Table[Rule[c[ordersG[[i]]+ordersgb[[i]]+ordersg[[i]]+iexternal], a[extindex+iexternal]],
                          {iexternal, externalsaGh[[i]] }];
           If[externalsaGh[[i]] !=0,localvertices[[i]] = localvertices[[i]] /. qrules /. arules];
           extindex += externalsaGh[[i]],
           {i, numbervertices}];
        Do[qrules = Table[Rule[k[ordersG[[i]]+ordersgb[[i]]+ordersg[[i]]+ordersGh[[i]]+iexternal], q[extindex+iexternal]], 
                          {iexternal, externalsGh[[i]] }];
           arules = Table[Rule[c[ordersG[[i]]+ordersgb[[i]]+ordersg[[i]]+ordersGh[[i]]+iexternal], a[extindex+iexternal]],
                          {iexternal, externalsGh[[i]] }];
           If[externalsGh[[i]] !=0,localvertices[[i]] = localvertices[[i]] /. qrules /. arules];
           extindex += externalsGh[[i]],
           {i, numbervertices}];
        Do[qrules = Table[Rule[k[ordersG[[i]]+ordersgb[[i]]+ordersg[[i]]+ordersGh[[i]]+ordersGh[[i]]+iexternal], q[extindex+iexternal]], 
                          {iexternal, externalsQb[[i]] }];
           afrules = Table[Rule[cf[ordersG[[i]]+ordersgb[[i]]+ordersg[[i]]+ordersGh[[i]]+ordersGh[[i]]+iexternal], af[extindex+iexternal]],
                          {iexternal, externalsQb[[i]] }];
           fnurules= Table[Rule[fmu[ordersG[[i]]+ordersgb[[i]]+ordersg[[i]]+ordersGh[[i]]+ordersGh[[i]]+iexternal],fnu[extindex+iexternal]],
                          {iexternal, externalsQb[[i]] }];
           If[externalsQb[[i]] !=0,localvertices[[i]] = localvertices[[i]] /. qrules /. afrules /. fnurules];
           extindex += externalsQb[[i]],
           {i, numbervertices}];
        Do[qrules = Table[Rule[k[ordersG[[i]]+ordersgb[[i]]+ordersg[[i]]+ordersGh[[i]]+ordersGh[[i]]+ordersQb[[i]]+iexternal], q[extindex+iexternal]], 
                          {iexternal, externalsQ[[i]] }];
           afrules = Table[Rule[cf[ordersG[[i]]+ordersgb[[i]]+ordersg[[i]]+ordersGh[[i]]+ordersGh[[i]]+ordersQb[[i]]+iexternal], af[extindex+iexternal]],
                          {iexternal, externalsQ[[i]] }];
           fnurules= Table[Rule[fmu[ordersG[[i]]+ordersgb[[i]]+ordersg[[i]]+ordersGh[[i]]+ordersGh[[i]]+ordersQb[[i]]+iexternal],fnu[extindex+iexternal]],
                          {iexternal, externalsQ[[i]] }];
           If[externalsQ[[i]] !=0,localvertices[[i]] = localvertices[[i]] /. qrules /. afrules /. fnurules];
           extindex += externalsQ[[i]],
           {i, numbervertices}];
        Do[qrules = Table[Rule[k[ordersG[[i]]+ordersgb[[i]]+ordersg[[i]]+ordersGh[[i]]+ordersGh[[i]]+ordersQb[[i]]+ordersQ[[i]]+iexternal], q[extindex+iexternal]], 
                          {iexternal, externalsApd[[i]] }];
           afrules = Table[Rule[cf[ordersG[[i]]+ordersgb[[i]]+ordersg[[i]]+ordersGh[[i]]+ordersGh[[i]]+ordersQb[[i]]+ordersQ[[i]]+iexternal], af[extindex+iexternal]],
                          {iexternal, externalsApd[[i]] }];
           If[externalsApd[[i]] !=0,localvertices[[i]] = localvertices[[i]] /. qrules /. afrules];
           extindex += externalsApd[[i]],
           {i, numbervertices}];
        Do[qrules = Table[Rule[k[ordersG[[i]]+ordersgb[[i]]+ordersg[[i]]+ordersGh[[i]]+ordersGh[[i]]+ordersQb[[i]]+ordersQ[[i]]+ordersApd[[i]]+iexternal], q[extindex+iexternal]], 
                          {iexternal, externalsAp[[i]] }];
           afrules = Table[Rule[cf[ordersG[[i]]+ordersgb[[i]]+ordersg[[i]]+ordersGh[[i]]+ordersGh[[i]]+ordersQb[[i]]+ordersQ[[i]]+ordersApd[[i]]+iexternal], af[extindex+iexternal]],
                          {iexternal, externalsAp[[i]] }];
           If[externalsAp[[i]] !=0,localvertices[[i]] = localvertices[[i]] /. qrules /. afrules];
           extindex += externalsAp[[i]],
           {i, numbervertices}];
        Do[qrules = Table[Rule[k[ordersG[[i]]+ordersgb[[i]]+ordersg[[i]]+ordersGh[[i]]+ordersGh[[i]]+ordersQb[[i]]+ordersQ[[i]]+ordersApd[[i]]+ordersAp[[i]]+iexternal], q[extindex+iexternal]], 
                          {iexternal, externalsAmd[[i]] }];
           afrules = Table[Rule[cf[ordersG[[i]]+ordersgb[[i]]+ordersg[[i]]+ordersGh[[i]]+ordersGh[[i]]+ordersQb[[i]]+ordersQ[[i]]+ordersApd[[i]]+ordersAp[[i]]+iexternal], af[extindex+iexternal]],
                          {iexternal, externalsAmd[[i]] }];
           If[externalsAmd[[i]] !=0,localvertices[[i]] = localvertices[[i]] /. qrules /. afrules];
           extindex += externalsAmd[[i]],
           {i, numbervertices}];
        Do[qrules = Table[Rule[k[ordersG[[i]]+ordersgb[[i]]+ordersg[[i]]+ordersGh[[i]]+ordersGh[[i]]+ordersQb[[i]]+ordersQ[[i]]+ordersApd[[i]]+ordersAp[[i]]+ordersAmd[[i]]+iexternal], q[extindex+iexternal]], 
                          {iexternal, externalsAm[[i]] }];
           afrules = Table[Rule[cf[ordersG[[i]]+ordersgb[[i]]+ordersg[[i]]+ordersGh[[i]]+ordersGh[[i]]+ordersQb[[i]]+ordersQ[[i]]+ordersApd[[i]]+ordersAp[[i]]+ordersAmd[[i]]+iexternal], af[extindex+iexternal]],
                          {iexternal, externalsAm[[i]] }];
           If[externalsAm[[i]] !=0,localvertices[[i]] = localvertices[[i]] /. qrules /. afrules];
           extindex += externalsAm[[i]],
           {i, numbervertices}];

(* We have reached up to here. In what follows, the 3 "Do" blocks must be replaced by 8 blocks (one for each incidence matrix) *)

(* Self contractions of vertices, and contractions of the ith and jth vertex;
   These two operations are performed simultaneously, in order to respect the
   order of indices, as imposed by `symmetrizepartially' above               *)

        Do[Do[++usedG[[i]];++usedG[[i]];
              ++pcount;++bcount;++rhocount;++rhocount;
              localvertices[[i]] =
                contract1[localvertices[[i]], usedG[[i]]-1, usedG[[i]],
                          pcount, bcount, rhocount-1, rhocount];
              propprod *= prop[p[pcount], rho[rhocount-1], rho[rhocount]],
              {contractionsG[[i,i]]/2}];
           Do[Do[localvertices[[i]] = 
                   localvertices[[i]] /. k[++usedG[[i]] ] -> p[++pcount]
                                     /. c[usedG[[i]] ] -> b[++bcount]
                                     /. mu[usedG[[i]] ] -> rho[++rhocount];
                 localvertices[[j]] = 
                   localvertices[[j]] /. k[++usedG[[j]] ] -> -p[pcount]
                                     /. c[usedG[[j]] ] -> b[bcount]
                                     /. mu[usedG[[j]] ] -> rho[++rhocount];
                 propprod *= prop[p[pcount], rho[rhocount-1], rho[rhocount]],
                 {contractionsG[[i,j]]}],
              {j, i+1, numbervertices}],
           {i, numbervertices}];


(* <l(p1)^c1_i1 lbar(p2)^c2_i2> = d^{c1,c2} delta(p1-p2) propF[p2,i2,i1,rho[20]] * 2  (with possibly zero mass) 
                                = d^{c1,c2} delta(p1-p2) propg[p2,i2,i1,rho[20]]                                  *)
          Do[Do[Do[localvertices[[i]] = 
                    localvertices[[i]] /. k[++usedgb[[i]]] -> p[++pcount]
                                       /. c[usedgb[[i]]] -> b[++bcount]
                                       /. fmu[usedgb[[i]]] -> frho[++frhocount];
                    localvertices[[j]] = 
                    localvertices[[j]] /. k[++usedg[[j]]] -> p[pcount]
                                       /. c[usedg[[j]]] -> b[bcount]
                                       /. fmu[usedg[[j]]] -> frho[++frhocount];
                    propprod *= propg[p[pcount],frho[frhocount-1],frho[frhocount],rho[++rhocount]],
                    {contractionsg[[i,j]]}],
              {j, numbervertices}],
           {i, numbervertices}];

(* In the loop which follows, we consider only cases where the two gluinobars which are being contracted
   do not emanate from the same vertex. Similarly for contractions among two gluinos, further below       *)


(* <lbar(p1)^c1_i1 lbar(p2)^c2_i2> = d^{c1,c2} delta(-p1-p2) C_{i1,j} propF[p2,i2,j,rho[20]] * 2
                                   = d^{c1,c2} delta(-p1-p2) C_{i1,j} propg[p2,i2,j,rho[20]]       *)
          Do[Do[Do[localvertices[[i]] = 
                    localvertices[[i]] /. k[++usedgb[[i]]] -> -p[++pcount]
                                       /. c[usedgb[[i]]] -> b[++bcount]
                                       /. fmu[usedgb[[i]]] -> frho[++frhocount];
                    localvertices[[j]] = 
                    localvertices[[j]] /. k[++usedgb[[j]]] -> p[pcount] 
                                       /. c[usedgb[[j]]] -> b[bcount]
                                       /. fmu[usedgb[[j]]] -> frho[++frhocount];
                    propprod *= dtrace[frho[frhocount-1], Charge, frho[frhocount+1]] *
		                    propg[p[pcount],frho[frhocount],frho[frhocount+1],rho[++rhocount]];
		    ++frhocount,
                   {contractionsgbgb[[i,j]]}],
              {j, i+1, numbervertices}],
           {i, numbervertices}];

(* Given that lbarT(p1) = C l(-p1), and Cdag C = 1, the correct expression for l in terms of lbar
 should be: lT(-p1) = lbar(p1) Cstar = - lbar(p1) Cdagger
   If we wanted to adopt the basis in which C = -i gamma0 gamma2, then: Cstar = -C, and thus we could write:
   l(p2) = C lbarT(-p2) ---> lT(p2) = - lbar(-p2) C                                                 *)
(*   <l(p1)^c1_i1 l(p2)^c2_i2> = d^{c1,c2} delta(p1+p2) propF[p1,j,i1,rho[20]] * 2 (- Cdagger_{j,i2})
                               = d^{c1,c2} delta(p1+p2) propg[p1,j,i1,rho[20]] *   (- Cdagger_{j,i2})         *)
          Do[Do[Do[localvertices[[i]] = 
                    localvertices[[i]] /. k[++usedg[[i]]] -> p[++pcount]
                                       /. c[usedg[[i]]] -> b[++bcount]
                                       /. fmu[usedg[[i]]] -> frho[++frhocount];
                    localvertices[[j]] = 
                    localvertices[[j]] /. k[++usedg[[j]]] -> -p[pcount] 
                                       /. c[usedg[[j]]] -> b[bcount]
                                       /. fmu[usedg[[j]]] -> frho[++frhocount];
                    propprod *= - propg[p[pcount],frho[frhocount+1],frho[frhocount-1],rho[++rhocount]] *
		                      dtrace[frho[frhocount+1], Chargedag, frho[frhocount]];
		    ++frhocount,
                   {contractionsgg[[i,j]]}],
              {j, i+1, numbervertices}],
           {i, numbervertices}];



    
        Do[Do[If[i==j,
                 Do[++usedGh[[i]];++usedaGh[[i]];++pcount;++bcount;
                    localvertices[[i]] =
                      contract1[localvertices[[i]],usedaGh[[i]],usedGh[[i]],
                                pcount, bcount, 0, 0];
                    propprod *= propG[p[pcount]],
                    {contractionsGh[[i,i]]}],
                 Do[localvertices[[i]] = 
                      localvertices[[i]] /. k[++usedaGh[[i]]] -> p[++pcount]
                                        /. c[usedaGh[[i]]] -> b[++bcount];
                    localvertices[[j]] = 
                      localvertices[[j]] /. k[++usedGh[[j]]] -> p[pcount]
                                        /. c[usedGh[[j]]] -> b[bcount];
                    propprod *= propG[p[pcount]],  (* Note: propG stands for a GHOST propagator! *)
                    {contractionsGh[[i,j]]}]],
              {j, numbervertices}],
           {i, numbervertices}];
	   
          Do[Do[If[i==j,
                 Do[++usedQb[[i]];++usedQ[[i]];++pcount;++bfcount;
                    ++frhocount;++frhocount;++rhocount;
                    localvertices[[i]] =
                      contractF1[localvertices[[i]],usedQb[[i]],usedQ[[i]],
                                pcount, bfcount, frhocount-1, frhocount];
                    propprod *= propF[p[pcount],frho[frhocount-1],frho[frhocount],rho[rhocount]],
                    {contractionsQ[[i,i]]}],
                 Do[localvertices[[i]] = 
                    localvertices[[i]] /. k[++usedQb[[i]]] -> p[++pcount]
                                      /. cf[usedQb[[i]]] -> bf[++bfcount]
                                      /. fmu[usedQb[[i]]] -> frho[++frhocount];
                    localvertices[[j]] = 
                    localvertices[[j]] /. k[++usedQ[[j]]] -> p[pcount]
                                      /. cf[usedQ[[j]]] -> bf[bfcount]
                                      /. fmu[usedQ[[j]]] -> frho[++frhocount];
                    propprod *= propF[p[pcount],frho[frhocount-1],frho[frhocount]                               ,rho[++rhocount]],
                    {contractionsQ[[i,j]]}]],
              {j, numbervertices}],
           {i, numbervertices}];


(* propA[p] = 1/(4 s2sq[p] + mSQUARK^2)        *)
          Do[Do[Do[localvertices[[i]] = 
                    localvertices[[i]] /. k[++usedApd[[i]]] -> p[++pcount]
                                       /. cf[usedApd[[i]]]  -> bf[++bfcount] ;
                    localvertices[[j]] = 
                    localvertices[[j]] /. k[++usedAp[[j]]] -> p[pcount]
                                       /. cf[usedAp[[j]]] -> bf[bfcount];
                    propprod *= propA[p[pcount]],
                    {contractionsAp[[i,j]]}],
              {j, numbervertices}],
           {i, numbervertices}];


          Do[Do[Do[localvertices[[i]] = 
                    localvertices[[i]] /. k[++usedAmd[[i]]] -> p[++pcount]
                                       /. cf[usedAmd[[i]]]  -> bf[++bfcount] ;
                    localvertices[[j]] = 
                    localvertices[[j]] /. k[++usedAm[[j]]] -> p[pcount]
                                       /. cf[usedAm[[j]]] -> bf[bfcount];
                    propprod *= propA[p[pcount]],
                    {contractionsAm[[i,j]]}],
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











