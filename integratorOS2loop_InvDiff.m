(* A few further changes implemented 12/2005, to produce Fortran files with
   shorter lines: indexov -> jov, indexiw -> jiw,
   some continuation lines written after: b(j,4,ir) = ...
                                     and: result = ...                        *)
(* This version of integrator contains definitions relevant to overlap
   fermions, and the Iwasaki gluonic propagator                               *)
(* NB: rho indices, assumed distinct, are NOT summed over their range of 
   values                                                                     *)

(* In this version on integrator it is assumed that each summand in the 
   integrand is multiplied by a linear combination of var[i]; accordingly, 
   the result is also given as a linear combination.                          *)

(* In order to avoid a plethora of Lorentz indices, we allow also expressions of
   the form s2sq[a] (= \sum_\rho s2[a,rho]^2), 
            sisq[a] (= \sum_\rho s2[2a,rho]^2) and 
            s2qu[a] (= \sum_\rho s2[a,rho]^4)       
   (a = p[1], p[2] or p[1]+p[2])                                              *)

(* To save on CPU time, the program evaluates the integral for up to 300 
   sextuplets of values for (r,m,c0,c1,c2,c3) (the Iwasaki parameters) 
   simultaneously                                                             *)

(* Further reduction of CPU time is achieved by a pre-evaluation of the Iwasaki
   propagator, for all possible values of its momentum and of the Iwasaki
   parameters                                                                 *)

(* An optional fourth argument ("gauge") may be used for the gauge parameter xi
   (gauge -> 0: Feynman gauge, gauge -> 1: Landau gauge). Default: gauge -> 0 *)

(* A list of dynamically generated objects, named t[i], is also accepted in the
   expression. The integrator is provided with a list of definitions for the 
   t[i], named tlist. Default: tlist -> {}                                    *)

(* Among the original expression, and the one with {p[1]->p[2],p[2]->p[1]}, 
   the program selects the one leading to the shortest inner loop   25/8/2006 *)

(* Code is written only for elements of tlist which appear in expr  28/9/2006 *)

(* A new list, "xlist", is introduced here, in order to precalculate common 
   factors (independent of prop, dprop),
   like (1+mO[p[1]] mO[p[2]] omegainvO[p[1]] omegainvO[p[2]]). 
   Unlike tlist, this one does not involve any summation over dummy rho 
   indices.                                                                   *)

(* Insertions 30/9/2019: We include definitions of the first and second
   derivatives of fermion (fhat) and gluon propagators (hat2,prop,dprop).     *)

(* Insertions 7/11/2019: We include definitions of the inverse gluon propagator
   (propinv), as well as definitions of the difference between propagators of 
   different momenta (hat2diff, fhatdiff, dfhatdiff, propdiffperiodic, 
   dpropdiffperiodic, hat2invdiff, fhatinvdiff, propinvdiffperiodic).         *)

integrator2::usage = StringJoin[
  "integrator2[integrand_, propagators_, file_] takes as input               \n
   an integrand with the topology of theta, in the form of a sum of products \n
   of numbers and/or s2 and/or c2 and/or m(p) (the fermion mass) and/or r    \n
   (the Wilson parameter) and/or propagators (fhat, hat2, dprop) and/or the  \n
   Iwasaki parameters cprop0, cprop1, cprop2, cprop3; thus, no factors of g, \n
   hat2, Nc, i0, epsilon, etc. are allowed.                                  \n
      In this version, occurences expressions from the overlap formalism     \n
      are also permitted in the integrand, in particular:                    \n
            mO[p[1]], omegaO[p[1]], omegaO[p[1]+p[2]], omegainvO[p[1]], etc. \n
            omegaplusinvO[p[1],p[2]], omegaplusinvO[p[1],p[1]+p[2]],         \n
            omegaplusinvO[0,p[1]],    omegabO[p[1]], omegabinvO[p[1]]        \n
            (and similarly for p[2])                                         \n 
      The propagators carry momentum p[1], p[2], p[1]+p[2]; they can be      \n
   bosonic, fermionic, or any algebraic expression thereof, e.g.             \n
     hat2[p[2]]^3*(fhat[p[2]]-fhat[p[1]]+hat2[p[1]+p[2]]-hat2[p[1]])*        \n
          (hat2[p[1]]-fhat[p[1]])^2                                          \n
   Integration over p[1] is the last to be performed.                        \n
      The Lorentz indices can be rho[i], i=1,2,3,4; they are taken in the    \n
   i-th direction.                                                           \n
      The output, written in `file', is a fortran code for the evaluation of \n
   the integral.
      Additionally, the staggered propagator fhatSF can also be used in this \n
   version." ]

integrator2::wrongArgument = "integrator2 called with inappropriate argument"

(* --- change --- *)
integrator2[integrand_, ___]:= 
   Message[integrator2::wrongArgument] /; 
      !(Complement[Union[If[Head[#]===Symbol,#,Head[#]]& /@ Variables[integrand]],
		   {s2,c2,s2sq,sisq,s2qu,c2sq,cisq,r,m,var,hat2,fhat,fhatSF,prop,dprop,propinv,cprop0,cprop1,
		       cprop2,cprop3,cc1,cc2,mO,omegaO,omegainvO,omegaplusinvO,omegabO,omegabinvO,x,t,
		       deriv,deriv2,dfhat,
		       hat2diff,fhatdiff,dfhatdiff,propdiffperiodic, 
   dpropdiffperiodic, hat2invdiff, fhatinvdiff, propinvdiffperiodic}]==={})
(* --- end change --- *)

integrator2[integrand_, propagators_, file_, options___]:= 
  Block[
    {integrandlocal = integrand, propagatorslocal = propagators,
     expr, variables, variablelist, varlist, varlength, rulelist, factorlist, proplist,
     dummy1, dummy2, expr1, expr2, expr3, expr4, index1, index2, index3, index,optionlist,
     gauge, gaugelocal, tlist, tlistlocal, tlistTrueFalse, 
     xlist, xlistlocal, xlistTrueFalse, xlistlocalorig,
     temp, defaultlist, substlist,
     exprS, expr1S, expr2S, expr3S, expr4S, index1S, index2S, index3S, indexS,
     proplistS, tlistlocalS, xlistlocalS, xlistlocalorigS, factorlistS, flagp1p2=0},
    defaultlist = {gauge -> 0, tlist -> {}, xlist -> {}};
    optionlist = List[options];
    gaugelocal = gauge /. optionlist /. defaultlist;
    tlistlocal = tlist /. optionlist /. defaultlist;
    xlistlocalorig = xlist /. optionlist /. defaultlist;
    xlistlocal = xlistlocalorig;
    tlistTrueFalse = Table[!FreeQ[integrandlocal,t[i]],
                           {i,Length[tlistlocal]}];
    xlistTrueFalse = Table[!FreeQ[integrandlocal,x[i]],
                           {i,Length[xlistlocal]}];
    w[a__] := WriteString[ToString[file], "      ", a, "\n"];
    wc[a__]:= WriteString[ToString[file], "     &", a, "\n"];

Label[p1p2];
    expr = List /@ (If[Head[integrandlocal]===Plus, List@@integrandlocal, List[integrandlocal]]);

    variables = Select[Variables[integrandlocal],(FreeQ[#,p[2]] && FreeQ[#,t] && FreeQ[#,x])&];
    variablelist = Table[Cases[Select[variables, (!FreeQ[#,s2] || !FreeQ[#,c2])&],_[_,rho[j]]],{j,4}];
    (* --- change --- *)
    variablelist = 
      Append[Drop[variablelist,-1], 
             Join[variablelist[[-1]],
                  Select[variables,(!FreeQ[#,p[1]] && (FreeQ[#,rho] || (!FreeQ[#,dprop]) || (!FreeQ[#,prop]) || (!FreeQ[#,propinv]) || (!FreeQ[#,deriv]) || (!FreeQ[#,deriv2]) || (!FreeQ[#, propdiffperiodic]) || (!FreeQ[#,dpropdiffperiodic]) || (!FreeQ[#,propinvdiffperiodic])))&]]];
    (* --- end change --- *)
    variables = Complement[Variables[integrandlocal],variables];
    variablelist = Join[variablelist,Table[Cases[Select[variables, (!FreeQ[#,s2] || !FreeQ[#,c2])&],_[_,rho[j]]],{j,4}]];
    (* --- change --- *)
    variablelist =
      Append[Drop[variablelist,-1],
             Join[variablelist[[-1]],
                  Select[variables,(FreeQ[#,rho] || (!FreeQ[#,dprop]) || (!FreeQ[#,prop]) || (!FreeQ[#,propinv]) || (!FreeQ[#,deriv]) || (!FreeQ[#,deriv2]) || (!FreeQ[#, propdiffperiodic]) || (!FreeQ[#,dpropdiffperiodic]) || (!FreeQ[#,propinvdiffperiodic]))&]]];
    (* --- end change --- *)

    Do[rulelist = Rule[#,1]& /@ (variablelist[[-j]]);
       expr = (Join[{(#[[1]]) /. rulelist},
                    {(#[[1]]) / ((#[[1]]) /. rulelist)},
                    Drop[#,1]])& /@ expr,
       {j,Length[variablelist]}];

    varlist = Union[integrandlocal[[Sequence @@ #]]& /@ Position[integrandlocal,var[_]]];
    varlength = Max[(#[[1]])& /@ varlist, 1];
    factorlist = ((#[[1]])& /@ expr);
    factorlist = Table[# /. var[j]->1 /. var[_]->0,{j,varlength}]& /@ factorlist;
    factorlist = factorlist /. 
         r -> r[jov[ir]] /. m -> m[jov[ir]] /. mO -> m[jov[ir]] /. 
         cprop0 -> cprop0[jiw[ir]] /. cprop1 -> cprop1[jiw[ir]] /.
         cprop2 -> cprop2[jiw[ir]] /. cprop3 -> cprop3[jiw[ir]] /.
         cc1 -> cc1[jiw[ir]] /. cc2 -> cc2[jiw[ir]];
    factorlist = Map[FortranForm,factorlist,{2}];

    proplist = {Select[propagatorslocal*dummy1*dummy2, FreeQ[#,p[2]]&]
                 /. dummy1 -> 1 /. dummy2 -> 1};
    proplist = {proplist[[1]], propagatorslocal/proplist[[1]]};
    proplist = proplist /.
       {fhat[p[1]]->fhat1[jov[ir]], fhat[p[2]]->fhat2[jov[ir]], 
        hat2[p[1]]-> hat1, hat2[p[2]]-> hat2,
	fhatSF[p[1]]->fhatSF1[jov[ir]], fhatSF[p[2]]->fhatSF2[jov[ir]],
        fhat[p[1]+p[2]]->fhat12[jov[ir]], 
        hat2[p[1]+p[2]]-> hat12,
        fhatSF[p[1]+p[2]]->fhatSF12[jov[ir]]};
    proplist = FortranForm /@ proplist;

    expr = Drop[#,1]& /@ expr;

(* --- addition --- *)

    deriv2[a_,b__] := deriv2[a, Sequence @@ Sort[{b}]] /;  !OrderedQ[{b}];
    
    expr = expr /. {deriv[hat2[p[1]],a_] :> derhat["i",a],
                    deriv[hat2[p[2]],a_] :> derhat["j",a],
                    deriv[hat2[p[1]+p[2]],a_] :> derhat["ij",a],
                    deriv2[hat2[p[1]],a__] :> der2hat["i",a],
                    deriv2[hat2[p[2]],a__] :> der2hat["j",a],
                    deriv2[hat2[p[1]+p[2]],a__] :> der2hat["ij",a]};
 
    expr = expr /. derhat[a_,rho[i_]] :> 
    derhat[Sequence @@ (ToExpression[StringJoin[a,ToString[#],"n"]]& /@ DeleteDuplicates[{i,Sequence @@ Range[4]}])]*sgn[Sequence @@ ToExpression[StringJoin[a,ToString[i]]]];
 
    expr = expr /. der2hat[a_,rho[i_],rho[j_]] :> 
    ToExpression[StringJoin["der2hat",Sequence @@ (rorderall[reducerho[{rho[i],rho[j]}]] /. rho[s_] :> ToString[s])]][Sequence @@ (ToExpression[StringJoin[a,ToString[#],"n"]]& /@ DeleteDuplicates[{i,j,Sequence @@ Range[4]}])]*((Times @@ (sgn[Sequence @@ ToExpression[StringJoin[a,ToString[#]]]]& /@ {i,j})) //. sgn[b_]^k_ :> sgn[b]^(k-2));

    expr = expr /. {deriv[fhat[p[1]],a_] :> derfhat["i",a],
                    deriv[fhat[p[2]],a_] :> derfhat["j",a],
                    deriv[fhat[p[1]+p[2]],a_] :> derfhat["ij",a],
                    deriv2[fhat[p[1]],a__] :> der2fhat["i",a],
                    deriv2[fhat[p[2]],a__] :> der2fhat["j",a],
                    deriv2[fhat[p[1]+p[2]],a__] :> der2fhat["ij",a]};
    
    expr = expr /. derfhat[a_,rho[i_]] :> 
    derfhat[Sequence @@ (ToExpression[StringJoin[a,ToString[#],"n"]]& /@ DeleteDuplicates[{i,Sequence @@ Range[4]}])]*sgn[Sequence @@ ToExpression[StringJoin[a,ToString[i]]]];
    
    expr = expr /. der2fhat[a_,rho[i_],rho[j_]] :> 
    ToExpression[StringJoin["der2fhat",Sequence @@ (rorderall[reducerho[{rho[i],rho[j]}]] /. rho[s_] :> ToString[s])]][Sequence @@ (ToExpression[StringJoin[a,ToString[#],"n"]]& /@ DeleteDuplicates[{i,j,Sequence @@ Range[4]}])]*((Times @@ (sgn[Sequence @@ ToExpression[StringJoin[a,ToString[#]]]]& /@ {i,j})) //. sgn[b_]^k_ :> sgn[b]^(k-2));

    expr = expr /. {deriv[dfhat[p[1]],a_] :> derdfhat["i",a],
                    deriv[dfhat[p[2]],a_] :> derdfhat["j",a],
                    deriv[dfhat[p[1]+p[2]],a_] :> derdfhat["ij",a],
                    deriv2[dfhat[p[1]],a__] :> der2dfhat["i",a],
                    deriv2[dfhat[p[2]],a__] :> der2dfhat["j",a],
                    deriv2[dfhat[p[1]+p[2]],a__] :> der2dfhat["ij",a]};
    
    expr = expr /. derdfhat[a_,rho[i_]] :> 
    derdfhat[Sequence @@ (ToExpression[StringJoin[a,ToString[#],"n"]]& /@ DeleteDuplicates[{i,Sequence @@ Range[4]}])]*sgn[Sequence @@ ToExpression[StringJoin[a,ToString[i]]]];
    
    expr = expr /. der2dfhat[a_,rho[i_],rho[j_]] :> 
    ToExpression[StringJoin["der2dfhat",Sequence @@ (rorderall[reducerho[{rho[i],rho[j]}]] /. rho[s_] :> ToString[s])]][Sequence @@ (ToExpression[StringJoin[a,ToString[#],"n"]]& /@ DeleteDuplicates[{i,j,Sequence @@ Range[4]}])]*((Times @@ (sgn[Sequence @@ ToExpression[StringJoin[a,ToString[#]]]]& /@ {i,j})) //. sgn[b_]^k_ :> sgn[b]^(k-2));
    
    expr = expr /. {deriv[prop[p[1],a__],b_] :> derprop["i",a,b],
                    deriv[prop[p[2],a__],b_] :> derprop["j",a,b],
                    deriv[prop[p[1]+p[2],a__],b_] :> derprop["ij",a,b],
                    deriv2[prop[p[1],a__],b__] :> der2prop["i",a,b],
                    deriv2[prop[p[2],a__],b__] :> der2prop["j",a,b],
                    deriv2[prop[p[1]+p[2],a__],b__] :> der2prop["ij",a,b]};

    sort[a_,b_,b_]:= sort[b,a,b] /; !(a === b) ;
    sort[a_,a_,b_,a_]:= sort[a,a,a,b] /; !(a === b);
    sort[a_,b_,b_,b_]:= sort[b,a,b,b] /; !(a === b); 
    sort[a_,b_,b_,a_]:= sort[a,b,a,b] /; !(a === b);
    sort[a_,b_,b_,c_]:= sort[b,a,b,c] /; (!(a === b) && !(a === c) && !(b === c)); 
    sort[a_,b_,c_,b_]:= sort[b,a,b,c] /; (!(a === b) && !(a === c) && !(b === c));
    sort[a_,b_,c_,a_]:= sort[a,b,a,c] /; (!(a === b) && !(a === c));

    expr = expr /. derprop[a_,b__] :> 
    ToExpression[StringJoin["derprop",Sequence @@ ((List @@ rorderall[reducerho[sort[b]]]) /. rho[s_] :> ToString[s])]][Sequence @@ (ToExpression[StringJoin[a,ToString[#],"n"]]& /@ DeleteDuplicates[{Sequence @@ (sort[b] /. rho[s_] :> s),Sequence @@ Range[4]}]),jiw[ir]]*sgn[Sequence @@ ToExpression[StringJoin[a,ToString[({b}[[-1]] /. rho[s_] :> s)]]]];

    expr = expr /. der2prop[a_,b__] :> 
    ToExpression[StringJoin["der2prop",Sequence @@ ((List @@ rorderall[reducerho[sort[b]]]) /. rho[s_] :> ToString[s])]][Sequence @@ (ToExpression[StringJoin[a,ToString[#],"n"]]& /@ DeleteDuplicates[{Sequence @@ (sort[b] /. rho[s_] :> s),Sequence @@ Range[4]}]),jiw[ir]]*((Times @@ (sgn[Sequence @@ ToExpression[StringJoin[a,ToString[#]]]]& /@ (Drop[List[b],2] /. rho[s_] :> s))) //. sgn[c_]^k_ :> sgn[c]^(k-2));

    expr = expr /. der2prop1234[a__] :> 0;

expr = expr /. {deriv[dprop[p[1],a__],b_] :> derdprop["i",a,b],
                    deriv[dprop[p[2],a__],b_] :> derdprop["j",a,b],
                    deriv[dprop[p[1]+p[2],a__],b_] :> derdprop["ij",a,b],
                    deriv2[dprop[p[1],a__],b__] :> der2dprop["i",a,b],
                    deriv2[dprop[p[2],a__],b__] :> der2dprop["j",a,b],
                    deriv2[dprop[p[1]+p[2],a__],b__] :> der2dprop["ij",a,b]};

    expr = expr /. derdprop[a_,b__] :> 
    ToExpression[StringJoin["derdprop",Sequence @@ ((List @@ rorderall[reducerho[sort[b]]]) /. rho[s_] :> ToString[s])]][Sequence @@ (ToExpression[StringJoin[a,ToString[#],"n"]]& /@ DeleteDuplicates[{Sequence @@ (sort[b] /. rho[s_] :> s),Sequence @@ Range[4]}]),jiw[ir]]*sgn[Sequence @@ ToExpression[StringJoin[a,ToString[({b}[[-1]] /. rho[s_] :> s)]]]];

    expr = expr /. der2dprop[a_,b__] :> 
    ToExpression[StringJoin["der2dprop",Sequence @@ ((List @@ rorderall[reducerho[sort[b]]]) /. rho[s_] :> ToString[s])]][Sequence @@ (ToExpression[StringJoin[a,ToString[#],"n"]]& /@ DeleteDuplicates[{Sequence @@ (sort[b] /. rho[s_] :> s),Sequence @@ Range[4]}]),jiw[ir]]*((Times @@ (sgn[Sequence @@ ToExpression[StringJoin[a,ToString[#]]]]& /@ (Drop[List[b],2] /. rho[s_] :> s))) //. sgn[c_]^k_ :> sgn[c]^(k-2));

    expr = expr /. der2dprop1234[a__] :> 0;

    expr = expr /. {hat2diff[p[1]+p[2],p[2]] -> hat2[p[1]+p[2]] - hat2[p[2]], fhatdiff[p[1]+p[2],p[2]] -> fhat[p[1]+p[2]] - fhat[p[2]], dfhatdiff[p[1]+p[2],p[2]] -> dfhat[p[1]+p[2]] - dfhat[p[2]], propdiffperiodic[p[1]+p[2],p[2],a_,b_] :> prop[p[1]+p[2],a,b] - prop[p[2],a,b] c2[p[1],a] c2[p[1],b], dpropdiffperiodic[p[1]+p[2],p[2],a_,b_] :> dprop[p[1]+p[2],a,b] - dprop[p[2],a,b] c2[p[1],a] c2[p[1],b], hat2invdiff[p[1]+p[2],p[2]] -> 4*(s2sq[p[1]+p[2]] - s2sq[p[2]]), fhatinvdiff[p[1]+p[2],p[2]] -> sisq[p[1]+p[2]] + 4 s2sq[p[1]+p[2]]^2 - sisq[p[2]] - 4 s2sq[p[2]]^2, propinvdiffperiodic[p[1]+p[2],p[2],a_,b_] :> propinv[p[1]+p[2],a,b] c2[p[1],b] - propinv[p[2],a,b] c2[p[1],a]};

(* --- end addition --- *)

    expr = expr /. (a_[b_,rho[n_]] :>
                    a[b /. {p[1] :> ToExpression[StringJoin["i",ToString[n]]],
                            p[2] :> ToExpression[StringJoin["j",ToString[n]]]}]);
    substlist = {s2sq[p[1]]->s2sq1, s2sq[p[2]]->s2sq2, s2sq[p[1]+p[2]]->s2sq12,
                 sisq[p[1]]->sisq1, sisq[p[2]]->sisq2, sisq[p[1]+p[2]]->sisq12,
                 s2qu[p[1]]->s2qu1, s2qu[p[2]]->s2qu2, s2qu[p[1]+p[2]]->s2qu12,
                 c2sq[p[1]]->c2sq1, c2sq[p[2]]->c2sq2, c2sq[p[1]+p[2]]->c2sq12,
                 cisq[p[1]]->cisq1, cisq[p[2]]->cisq2, cisq[p[1]+p[2]]->cisq12,
                 omegaO[p[1]]->omegao1[jov[ir]], 
                 omegainvO[p[1]]->omegainvo1[jov[ir]],
                 omegabO[p[1]]->omegabo1[jov[ir]], 
                 omegabinvO[p[1]]->omegabinvo1[jov[ir]], 
                 mO[p[1]]->mo1[jov[ir]],
                 omegaO[p[2]]->omegao2[jov[ir]], 
                 omegainvO[p[2]]->omegainvo2[jov[ir]],
                 omegabO[p[2]]->omegabo2[jov[ir]], 
                 omegabinvO[p[2]]->omegabinvo2[jov[ir]], 
                 mO[p[2]]->mo2[jov[ir]],
                 omegaO[p[1]+p[2]]->omegao12[jov[ir]], 
                 omegainvO[p[1]+p[2]]->omegainvo12[jov[ir]],
                 omegabO[p[1]+p[2]]->omegabo12[jov[ir]], 
                 omegabinvO[p[1]+p[2]]->omegabinvo12[jov[ir]], 
                 mO[p[1]+p[2]]->mo12[jov[ir]],
                 omegaplusinvO[0,p[1]]->omegaplusinvo1[jov[ir]],
                 omegaplusinvO[0,p[2]]->omegaplusinvo2[jov[ir]],
                 omegaplusinvO[0,p[1]+p[2]]->omegaplusinvo12[jov[ir]],
                 omegaplusinvO[p[1],p[2]]->omegaplusinvo1p2[jov[ir]],
                 omegaplusinvO[p[1],p[1]+p[2]]->omegaplusinvo1p12[jov[ir]],
                 omegaplusinvO[p[2],p[1]+p[2]]->omegaplusinvo2p12[jov[ir]],
                 m[p[1]]->m1[jov[ir]], m[p[2]]->m2[jov[ir]],
                 m[p[1]+p[2]]->m12[jov[ir]],
                 s2[2 a__]^2 :> si2[a],  c2[2 a__]^2 :> ci2[a],
                 s2[a__]^2 :> s22[a], c2[a__]^2 :> c22[a],
                 s2[2 a__] :> si[a],  c2[2 a__] :> ci[a],
                 s2[a__]^4 :> s24[a], c2[a__]^4 :> c24[a],
                 fhat[p[1]]-> fhat1[jov[ir]], hat2[p[1]]->hat1,
		 fhatSF[p[1]]-> fhatSF1[jov[ir]],
                 fhat[p[2]]-> fhat2[jov[ir]], hat2[p[2]]->hat2,
		 fhatSF[p[2]]-> fhatSF2[jov[ir]],
                 fhat[p[1]+p[2]]-> fhat12[jov[ir]], hat2[p[1]+p[2]]->hat12,
		 fhatSF[p[1]+p[2]]-> fhatSF12[jov[ir]],
		 (* --- addition --- *)
                 dfhat[p[1]]-> dfhat1[jov[ir]],
		 dfhat[p[2]]-> dfhat2[jov[ir]],
		 dfhat[p[1]+p[2]]-> dfhat12[jov[ir]]
		 (* --- end addition --- *)
                 };
    expr = expr /. substlist;
    xlistlocal = xlistlocalorig /. substlist;
    xlistlocal = xlistlocal /. mO -> m[jov[ir]];
    expr = expr /. {dprop[p[1],a__] :> dprop["i",a],
                    dprop[p[2],a__] :> dprop["j",a],
                    dprop[p[1]+p[2],a__] :> dprop["ij",a]};
    expr = expr /. dprop[a_,rho[i_],rho[j_]] :> 
             dpropn[Sequence @@ (ToExpression[StringJoin[a,ToString[#],"n"]]& /@ {i,j}),
                    Sequence @@ (ToExpression[StringJoin[a,ToString[#],"h"]]& /@ 
                                                            Complement[Range[4],{i,j}]),
                    jiw[ir]]                     /; (!(i===j));
    expr = expr /. dprop[a_,rho[i_],rho[i_]] :> 
             dpropd[Sequence @@ (ToExpression[StringJoin[a,ToString[#],"h"]]& /@ {i}),
                    Sequence @@ (ToExpression[StringJoin[a,ToString[#],"h"]]& /@ 
                                                            Complement[Range[4],{i}]),
                    jiw[ir]];
    expr = expr /. {prop[p[1],a__] :> prop["i",a],
                    prop[p[2],a__] :> prop["j",a],
                    prop[p[1]+p[2],a__] :> prop["ij",a]};
    expr = expr /. prop[a_,rho[i_],rho[j_]] :> 
             propn[Sequence @@ (ToExpression[StringJoin[a,ToString[#],"n"]]& /@ {i,j}),
                    Sequence @@ (ToExpression[StringJoin[a,ToString[#],"h"]]& /@ 
                                                            Complement[Range[4],{i,j}]),
                    jiw[ir]]                     /; (!(i===j));
    expr = expr /. prop[a_,rho[i_],rho[i_]] :> 
             propd[Sequence @@ (ToExpression[StringJoin[a,ToString[#],"h"]]& /@ {i}),
                    Sequence @@ (ToExpression[StringJoin[a,ToString[#],"h"]]& /@ 
                                                            Complement[Range[4],{i}]),
                    jiw[ir]];
    expr = expr /. {propinv[p[1],a__] :> propinv["i",a],
                    propinv[p[2],a__] :> propinv["j",a],
                    propinv[p[1]+p[2],a__] :> propinv["ij",a]};
    expr = expr /. propinv[a_,rho[i_],rho[j_]] :> 
             propinvn[Sequence @@ (ToExpression[StringJoin[a,ToString[#],"n"]]& /@ {i,j}),
                    Sequence @@ (ToExpression[StringJoin[a,ToString[#],"h"]]& /@ 
                                                            Complement[Range[4],{i,j}]),
                    jiw[ir]]                     /; (!(i===j));
    expr = expr /. propinv[a_,rho[i_],rho[i_]] :> 
             propinvd[Sequence @@ (ToExpression[StringJoin[a,ToString[#],"h"]]& /@ {i}),
                    Sequence @@ (ToExpression[StringJoin[a,ToString[#],"h"]]& /@ 
                                                            Complement[Range[4],{i}]),
                    jiw[ir]];
    
    expr = Map[FortranForm,expr,{2}];

    expr1 = Union[Take[#,{5,8}]& /@ expr];
    expr2 = Union[Take[#,{6,8}]& /@ expr];
    expr3 = Union[Take[#,{7,8}]& /@ expr];
    expr4 = Union[Take[#,{8,8}]& /@ expr];
    index3 = Table[Position[expr4,Drop[expr3[[j]],1]][[1,1]],{j,Length[expr3]}];
    index2 = Table[Position[expr3,Drop[expr2[[j]],1]][[1,1]],{j,Length[expr2]}];
    index1 = Table[Position[expr2,Drop[expr1[[j]],1]][[1,1]],{j,Length[expr1]}];
    index  = Table[Position[expr1,Take[expr[[j]],{5, 8}]][[1,1]],
                   {j,Length[expr]}];
    If[flagp1p2 == 0, flagp1p2 = 1; 
                      integrandlocal = integrandlocal /. {p[1]->p[2], p[2]->p[1]};
                      propagatorslocal = propagatorslocal /. {p[1]->p[2], p[2]->p[1]};
                      tlistlocalS = tlistlocal;
                      tlistlocal = tlistlocal /. {p[1]->p[2], p[2]->p[1]};
                      xlistlocalS = xlistlocal;
                      xlistlocalorig = xlistlocalorig /. {p[1]->p[2], p[2]->p[1]};
                      exprS = expr; 
                      expr1S = expr1; expr2S = expr2; expr3S = expr3; expr4S = expr4; 
                      index1S = index1; index2S = index2; index3S = index3; 
                      indexS = index;
                      proplistS = proplist; factorlistS = factorlist;
                      Goto[p1p2]];
    If[Length[expr4S] < Length[expr4],  
           tlistlocal = tlistlocalS;
           xlistlocalorig = xlistlocalorig /. {p[1]->p[2], p[2]->p[1]};
           xlistlocal = xlistlocalS;
           expr = exprS; 
           expr1 = expr1S; expr2 = expr2S; expr3 = expr3S; expr4 = expr4S; 
           index1 = index1S; index2 = index2S; index3 = index3S; index = indexS;
           proplist = proplistS; factorlist = factorlistS];

    w["program main"];
    w["implicit real*8 (a-h,o-z)"];
    w["real*8 k2p1, k4p1, k2p2, k4p2, k2p12, k4p12"];
    w["real*8 m, m1, m2, m12, mo1, mo2, mo12"];
    w["real*8 rtemp, mtemp, c0temp, c1temp, c2temp, c3temp"];
    w["parameter (l = ",Length[expr],")"];
    w["dimension a(l,4,300), b(l,4,300)"];
    w["dimension s2(-500:500), c2(-500:500), s22(-500:500), c22(-500:500)"];
    w["dimension s24(-500:500), c24(-500:500), s2hat(-500:500)"];
    w["dimension si(-500:500), ci(-500:500), si2(-500:500), ci2(-500:500)"];
    w["dimension r(3), r24(3), r12(3), m(3)"];
    w["dimension cprop0(3), cprop1(3), cprop2(3), cprop3(3)"];
    w["dimension cc1(3), cc2(3)"];
    w["dimension jov(300), jiw(300)"];
    w["dimension fhat1(3), fhat2(3), fhat12(3)"];
    w["dimension fhatSF1(3), fhatSF2(3), fhatSF12(3)"];
    (* --- addition --- *)
    w["dimension dfhat1(3), dfhat2(3), dfhat12(3)"];
    (* --- end addition --- *)
    w["dimension m1(3), m2(3), m12(3)"];
    (* --- change --- *)
    w["dimension dpropd(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension propd(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension dpropn(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension propn(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension propinvd(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension propinvn(-19:19,-19:19,-19:19,-19:19,3)"];
    (* --- end change --- *)
    (* --- addition --- *)
    w["real*8 g(4,4), ginv(4,4)"];
    w["integer indx(4), rho, sigma"];
    w["real*8 dhat(4), dvfhat(4), d2hat(4,4), dv2fhat(4,4)"];
    w["real*8 derpropinv(4,4,4), der2propinv(4,4,4,4)"];
    w["dimension derhat(-19:19,-19:19,-19:19,-19:19)"];
    w["dimension der2hat11(-19:19,-19:19,-19:19,-19:19)"];
    w["dimension der2hat12(-19:19,-19:19,-19:19,-19:19)"];
    w["dimension derfhat(-19:19,-19:19,-19:19,-19:19)"];
    w["dimension der2fhat11(-19:19,-19:19,-19:19,-19:19)"];
    w["dimension der2fhat12(-19:19,-19:19,-19:19,-19:19)"];
    w["dimension derdfhat(-19:19,-19:19,-19:19,-19:19)"];
    w["dimension der2dfhat11(-19:19,-19:19,-19:19,-19:19)"];
    w["dimension der2dfhat12(-19:19,-19:19,-19:19,-19:19)"];
    w["dimension derprop111(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension derprop112(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension derprop121(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension derprop123(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension derdprop111(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension derdprop112(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension derdprop121(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension derdprop123(-19:19,-19:19,-19:19,-19:19,3)"];   
    w["dimension der2prop1111(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension der2prop1112(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension der2prop1122(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension der2prop1123(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension der2prop1211(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension der2prop1212(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension der2prop1213(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension der2prop1233(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension der2dprop1111(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension der2dprop1112(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension der2dprop1122(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension der2dprop1123(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension der2dprop1211(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension der2dprop1212(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension der2dprop1213(-19:19,-19:19,-19:19,-19:19,3)"];
    w["dimension der2dprop1233(-19:19,-19:19,-19:19,-19:19,3)"];
    (* --- end addition --- *)
    w["dimension modn(-39:80), modh(-39:80), sgn(-39:80)"];
    w["dimension omegainvo1(3), omegabinvo1(3), omegaplusinvo1(3)"];
    w["dimension omegao1(3), mo1(3), omegabo1(3)"];
    w["dimension omegainvo2(3), omegabinvo2(3), omegaplusinvo2(3)"];
    w["dimension omegao2(3), mo2(3), omegabo2(3)"];
    w["dimension omegainvo12(3),omegabinvo12(3),omegaplusinvo12(3)"];
    w["dimension omegao12(3), mo12(3), omegabo12(3)"];
    w["dimension omegaplusinvo1p2(3),omegaplusinvo1p12(3)"];
    w["dimension omegaplusinvo2p12(3)"];
    w["dimension result(",varlength,")"];
    If[Length[tlistlocal]>0, w["dimension t(",Length[tlistlocal],")"]];
    If[Length[xlistlocal]>0, w["dimension x(",Length[xlistlocal],")"]];
    w[""];
    w["pi = 4.0*atan(1.d0)"];
    WriteString[ToString[file], "CCCC  ",
                "Enter minimum and maximum length of lattice (even, < 41)", "\n"];
    w["read(*,*) nmin, nmax"];
    WriteString[ToString[file], "CCCC  ",
                "Write up to 300 sextuplets of values for r, m, c0, c1, c2, c3, one set per line", "\n"];
    WriteString[ToString[file], "CCCC  ",
                "NB: No more than 3 different values for overlap parameters; idem for Iwasaki", "\n"];
    w["ir    = 1"];
    w["iov   = 1"];
    w["iiw   = 1"];
    w["iovflag = 1"];
    w["iiwflag = 1"];
    WriteString[ToString[file], "  1   read(*,*,end=2) rtemp, mtemp, \n"];
    wc["      c0temp, c1temp, c2temp, c3temp"];
    w["do iov2 = 1, iov - 1"];
    w[" if((rtemp-r(iov2)).lt.1.d-9 .and. (mtemp-m(iov2)).lt.1.d-9) then"];
    w["  jov(ir) = iov2"];
    w["  iovflag = 0"];
    w[" endif"];
    w["enddo"];
    w["if(iovflag.eq.1) then"];
    w[" r(iov) = rtemp"];
    w[" m(iov) = mtemp"];
    w[" jov(ir) = iov"];
    w[" iov = iov + 1"];
    w["endif"];
    w["iovflag = 1"];
    w["do iiw2 = 1, iiw - 1"];
    w[" if((c0temp-cprop0(iiw2)).lt.1.d-9 .and. "];
    wc[" (c1temp-cprop1(iiw2)).lt.1.d-9 .and. "];
    wc[" (c2temp-cprop2(iiw2)).lt.1.d-9 .and. "];
    wc[" (c3temp-cprop3(iiw2)).lt.1.d-9) then"];
    w["  jiw(ir) = iiw2"];
    w["  iiwflag = 0"];
    w[" endif"];
    w["enddo"];
    w["if(iiwflag.eq.1) then"];
    w[" cprop0(iiw) = c0temp"];
    w[" cprop1(iiw) = c1temp"];
    w[" cprop2(iiw) = c2temp"];
    w[" cprop3(iiw) = c3temp"];
    w[" cc1(iiw) = cprop2(iiw) + cprop3(iiw)"];
    w[" cc2(iiw) = cprop1(iiw) - cprop2(iiw) - cprop3(iiw)"];
    w[" jiw(ir) = iiw"];
    w[" iiw = iiw + 1"];
    w["endif"];
    w["iiwflag = 1"];
    w["ir = ir + 1"];
    w["goto 1"];
    WriteString[ToString[file], "  2   nr = ir - 1 \n"];
    w["iov = iov - 1"];
    w["iiw = iiw - 1"];
    w["do ir = 1, iov"];
    w[" r24(ir) = 4.d0*r(ir)**2"];
    w[" r12(ir) = 2.d0*r(ir)"];
    w["enddo"];
    w[""];
    w["do 1000 n = nmin, nmax, 2"];
    w["nmod2 = mod(n,2)"];
    w["nhalf = n/2"];
    w["n4 = n*4"];
    w["do i = -12*n,12*n"];
    w[" s2(i) = sin(i*pi/n)"];
    w[" c2(i) = cos(i*pi/n)"];
    w[" s22(i) = s2(i)**2"];
    w[" c22(i) = c2(i)**2"];
    w[" s24(i) = s2(i)**4"];
    w[" c24(i) = c2(i)**4"];
    w[" s2hat(i) = 2.d0*s2(i)"];
    w[" si(i) = sin(2*i*pi/n)"];
    w[" ci(i) = cos(2*i*pi/n)"];
    w[" si2(i) = si(i)**2"];
    w[" ci2(i) = ci(i)**2"];
    w["enddo"];
    w[""];
    w["do i = 1-n, 2*n"];
    w[" itemp = mod(i+n,2*n)-n"];
    w[" if(itemp.gt.0) itemp = min(itemp, n-itemp)"];
    w[" if(itemp.lt.0) itemp = max(itemp,-n-itemp)"];
    w[" modn(i) = itemp"];
    w[" modh(i) = min(mod(i+n,n), n - mod(i+n,n))"];
    w[" if ((i.ge.1).and.(i.le.nhalf)) sgn(i)=1"];
    w[" if ((i.gt.nhalf).and.(i.le.3*nhalf)) sgn(i)=-1"];
    w[" if ((i.gt.3*nhalf).and.(i.le.2*n)) sgn(i)=1"];
    w["enddo"];
    w[""];
    w[" do i1 = -nhalf, nhalf"];
    w[" do i2 = -nhalf, nhalf"];
    w[" do i3 = -nhalf, nhalf"];
    w[" do i4 = -nhalf, nhalf"];
    w[" if (i1.eq.0.and.i2.eq.0.and.i3.eq.0.and.i4.eq.0) goto 1001"];
    w[""];
    w[" do ir = 1, nr"]; 
    w[" s2sq1 = (s22(i1)+s22(i2)+s22(i3)+s22(i4))"];
    w[" sisq1 = (si2(i1)+si2(i2)+si2(i3)+si2(i4))"];
    w[" hat1 = 0.25d0/s2sq1"];
    w[" k2p1  =    4* (s22(i1)+s22(i2)+s22(i3)+s22(i4))"];
    w[" k4p1  =   16* (s24(i1)+s24(i2)+s24(i3)+s24(i4))"];
    w[" m1(jov(ir)) = m(jov(ir)) + r12(jov(ir))*s2sq1"];
    w[" fhat1(jov(ir)) = 1.d0/(m1(jov(ir))**2 + sisq1)"];
    w[""];
    w[" do mu = 1, 4"];
    w[" if (mu.eq.1) imu = i1"];
    w[" if (mu.eq.2) imu = i2"];
    w[" if (mu.eq.3) imu = i3"];
    w[" if (mu.eq.4) imu = i4"];
    w[" dhat(mu) = -2*si(imu)*hat1**2"];
    w[" dvfhat(mu) = -(si(2*imu)+r12(jov(ir))*si(imu)*m1(jov(ir)))*fhat1(jov(ir))**2"];
    w[" do nu = 1, mu"];
    w["  if (nu.eq.1) inu = i1"];
    w["  if (nu.eq.2) inu = i2"];
    w["  if (nu.eq.3) inu = i3"];
    w["  if (nu.eq.4) inu = i4"];
    w["  d2hat(mu,nu) = 8*si(imu)*si(inu)*hat1**3"];
    w["  if (mu.eq.nu) d2hat(mu,nu) = d2hat(mu,nu) -2*ci(imu)*hat1**2"];
    w["  if (nu.lt.mu) d2hat(nu,mu) = d2hat(mu,nu)"];
    w["  dv2fhat(mu,nu) = -si(imu)*si(inu)*r12(jov(ir))*fhat1(jov(ir))**2"];
    wc["     +2*(si(2*imu) + r12(jov(ir))*si(imu)*m1(jov(ir)))*"];
    wc["       (si(2*inu) + r12(jov(ir))*si(inu)*m1(jov(ir)))*fhat1(jov(ir))**3"];
    w["  if (mu.eq.nu) dv2fhat(mu,nu) = dv2fhat(mu,nu)"];
    wc["    -(2*ci(2*imu)+r12(jov(ir))*ci(imu)*m1(jov(ir)))*fhat1(jov(ir))**2"];
    w["  if (nu.lt.mu) dv2fhat(nu,mu) = dv2fhat(mu,nu)"];
    w[" enddo"];
    w[" enddo"];
    w[" derhat(i1,i2,i3,i4) = dhat(1)"];
    w[" derfhat(i1,i2,i3,i4) = dvfhat(1)"];
    w[" derdfhat(i1,i2,i3,i4) = dvfhat(1) - dhat(1)"];
    w[" der2hat11(i1,i2,i3,i4) = d2hat(1,1)"];
    w[" der2hat12(i1,i2,i3,i4) = d2hat(1,2)"];
    w[" der2fhat11(i1,i2,i3,i4) = dv2fhat(1,1)"];
    w[" der2fhat12(i1,i2,i3,i4) = dv2fhat(1,2)"];
    w[" der2dfhat11(i1,i2,i3,i4) = dv2fhat(1,1) - d2hat(1,1)"];
    w[" der2dfhat12(i1,i2,i3,i4) = dv2fhat(1,2) - d2hat(1,2)"];     
    w["   dummy = (1-cc1(jiw(ir))*k2p1)"];
    w["   do mu = 1, 4"];
    w["    if (mu.eq.1) imu = i1"];
    w["    if (mu.eq.2) imu = i2"];
    w["    if (mu.eq.3) imu = i3"];
    w["    if (mu.eq.4) imu = i4"];
    w["    do nu = 1, mu"];
    w["     if (nu.eq.1) inu = i1"];
    w["     if (nu.eq.2) inu = i2"];
    w["     if (nu.eq.3) inu = i3"];
    w["     if (nu.eq.4) inu = i4"];
    w["     g(mu,nu) = (1-dummy) * (2*s2(imu))*(2*s2(inu))"];
    wc["     + cc2(jiw(ir)) *(2*s2(imu))**3*(2*s2(inu))"];
    wc["     + cc2(jiw(ir)) *(2*s2(imu))*(2*s2(inu))**3"];
    w["     if (mu.eq.nu) g(mu,nu) = g(mu,nu) + dummy * k2p1"];
    wc["     - cc2(jiw(ir)) * k4p1 - cc2(jiw(ir)) * k2p1 * (2*s2(imu))**2"];
    w["     if (nu.lt.mu) g(nu,mu) = g(mu,nu)"];        
    w["     do rho = 1, 4"];
    w["        if (rho.eq.1) irho = i1"];
    w["        if (rho.eq.2) irho = i2"];
    w["        if (rho.eq.3) irho = i3"];
    w["        if (rho.eq.4) irho = i4"];
    w["        derpropinv(mu,nu,rho) = 2*cc1(jiw(ir))*si(irho)*s2hat(imu)"];
    wc["       *s2hat(inu)"];
    w["        if (rho.eq.mu) derpropinv(mu,nu,rho) = derpropinv(mu,nu,rho)"];
    wc["        + cc1(jiw(ir))*k2p1*s2hat(inu)*c2(irho)"];
    wc["        +3*cc2(jiw(ir))*si(irho)*s2hat(irho)*s2hat(inu)"];
    wc["        +cc2(jiw(ir))*s2hat(inu)**3*c2(irho)"];
    w["        if (rho.eq.nu) derpropinv(mu,nu,rho) = derpropinv(mu,nu,rho)"];
    wc["         + cc1(jiw(ir))*k2p1*s2hat(imu)*c2(irho)"];
    wc["         +3*cc2(jiw(ir))*si(irho)*s2hat(irho)*s2hat(imu)"];
    wc["         +cc2(jiw(ir))*s2hat(imu)**3*c2(irho)"];
    w["        if (mu.eq.nu) then"];
    w["          derpropinv(mu,nu,rho) = derpropinv(mu,nu,rho)"];
    wc["         + 2*si(irho) -4*cc1(jiw(ir))*k2p1*si(irho)"];
    wc["         -2*cc2(jiw(ir))*si(irho)*(s2hat(imu)**2 + 2*s2hat(irho)**2)"];
    w["           if(rho.eq.mu) derpropinv(mu,nu,rho) ="];
    wc["          derpropinv(mu,nu,rho) - 2*cc2(jiw(ir))*k2p1*si(irho)"];
    w["        endif"];
    w["        if (nu.lt.mu) derpropinv(nu,mu,rho) = derpropinv(mu,nu,rho)"];
    w["        do sigma = 1, rho"];
    w["           if (sigma.eq.1) isigma = i1"];
    w["           if (sigma.eq.2) isigma = i2"];
    w["           if (sigma.eq.3) isigma = i3"];
    w["           if (sigma.eq.4) isigma = i4"];
    w["           der2propinv(mu,nu,rho,sigma) = 0.d0"];
    w["           if(rho.eq.sigma) der2propinv(mu,nu,rho,sigma) ="];
    wc["           der2propinv(mu,nu,rho,sigma)"];
    wc["           +2*cc1(jiw(ir))*ci(irho)*s2hat(imu)*s2hat(inu)"];
    w["           if(rho.eq.mu) der2propinv(mu,nu,rho,sigma) ="];
    wc["           der2propinv(mu,nu,rho,sigma)"];
    wc["           + 2*cc1(jiw(ir))*c2(irho)*si(isigma)*s2hat(inu)"];
    w["           if(rho.eq.nu) der2propinv(mu,nu,rho,sigma) ="];
    wc["           der2propinv(mu,nu,rho,sigma)"];
    wc["           + 2*cc1(jiw(ir))*c2(irho)*si(isigma)*s2hat(imu)"];
    w["           if(sigma.eq.mu) then"];
    w["             der2propinv(mu,nu,rho,sigma) ="];
    wc["           der2propinv(mu,nu,rho,sigma)"];
    wc["           + 2*cc1(jiw(ir))*si(irho)*s2hat(inu)*c2(isigma)"];
    w["             if(rho.eq.nu) der2propinv(mu,nu,rho,sigma) ="];
    wc["             der2propinv(mu,nu,rho,sigma)"];
    wc["             +cc1(jiw(ir))*k2p1*c2(irho)*c2(isigma)"];
    wc["             +3*cc2(jiw(ir))*si(isigma)*s2hat(isigma)*c2(irho)"];
    wc["             +3*cc2(jiw(ir))*si(irho)*s2hat(irho)*c2(isigma)"];
    w["             if(rho.eq.sigma) der2propinv(mu,nu,rho,sigma) ="];
    wc["             der2propinv(mu,nu,rho,sigma)"];
    wc["             -0.25d0*cc1(jiw(ir))*k2p1*s2hat(irho)*s2hat(inu)"];
    wc["             +3*cc2(jiw(ir))*(s2hat(irho)*ci(irho)+si(irho)*c2(irho))"];
    wc["             *s2hat(inu) - 0.25d0*cc2(jiw(ir))*s2hat(irho)*"];
    wc["             s2hat(inu)**3"];
    w["           endif"];
    w["           if(sigma.eq.nu) then"];
    w["              der2propinv(mu,nu,rho,sigma) ="];
    wc["            der2propinv(mu,nu,rho,sigma)"];
    wc["            + 2*cc1(jiw(ir))*si(irho)*s2hat(imu)*c2(isigma)"];
    w["              if(rho.eq.mu) der2propinv(mu,nu,rho,sigma) ="];
    wc["              der2propinv(mu,nu,rho,sigma)"];
    wc["              +cc1(jiw(ir))*k2p1*c2(irho)*c2(isigma)"];
    wc["              +3*cc2(jiw(ir))*si(isigma)*s2hat(isigma)*c2(irho)"];
    wc["              +3*cc2(jiw(ir))*si(irho)*s2hat(irho)*c2(isigma)"];
    w["              if(rho.eq.sigma) der2propinv(mu,nu,rho,sigma) ="];
    wc["              der2propinv(mu,nu,rho,sigma)"];
    wc["              -0.25d0*cc1(jiw(ir))*k2p1*s2hat(irho)*s2hat(imu)"];
    wc["              +3*cc2(jiw(ir))*(s2hat(irho)*ci(irho)+si(irho)*c2(irho))"];
    wc["              *s2hat(imu) - 0.25d0*cc2(jiw(ir))*s2hat(irho)"];
    wc["              *s2hat(imu)**3"];
    w["            endif"];
    w["            if(mu.eq.nu) then"];
    w["               der2propinv(mu,nu,rho,sigma) ="];
    wc["             der2propinv(mu,nu,rho,sigma)"];
    wc["             - 8*cc1(jiw(ir))*si(irho)*si(isigma)"];
    w["               if(rho.eq.mu) der2propinv(mu,nu,rho,sigma) ="];
    wc["               der2propinv(mu,nu,rho,sigma)"];
    wc["               -4*cc2(jiw(ir))*si(irho)*si(isigma)"];
    w["               if(sigma.eq.mu) der2propinv(mu,nu,rho,sigma) ="];
    wc["               der2propinv(mu,nu,rho,sigma)"];
    wc["               -4*cc2(jiw(ir))*si(irho)*si(isigma)"];
    w["               if(rho.eq.sigma) then"];
    w["                  der2propinv(mu,nu,rho,sigma) ="];
    wc["                der2propinv(mu,nu,rho,sigma)+2*ci(irho)"];
    wc["                -4*cc1(jiw(ir))*k2p1*ci(irho)"];
    wc["                -2*cc2(jiw(ir))*ci(irho)*s2hat(imu)**2"];
    wc["                -4*cc2(jiw(ir))*ci(irho)*s2hat(irho)**2"];
    wc["                -8*cc2(jiw(ir))*si(irho)**2"];
    w["                  if(rho.eq.mu) der2propinv(mu,nu,rho,sigma) ="];
    wc["                  der2propinv(mu,nu,rho,sigma)"];
    wc["                  -2*cc2(jiw(ir))*k2p1*ci(irho)"];
    w["               endif"];
    w["            endif"];
    w["            if (nu.lt.mu) der2propinv(nu,mu,rho,sigma) ="];
    wc["            der2propinv(mu,nu,rho,sigma)"];
    w["            if (sigma.lt.rho) der2propinv(mu,nu,sigma,rho) ="];
    wc["            der2propinv(mu,nu,rho,sigma)"];
    w["            if (nu.lt.mu .and. sigma.lt.rho)"];
    wc["            der2propinv(nu,mu,sigma,rho) ="];
    wc["            der2propinv(mu,nu,rho,sigma)"];
    w["         enddo"];
    w["      enddo"];
    w["   enddo"];
    w["  enddo"];
    w["  propinvn(i1,i2,i3,i4,jiw(ir)) = g(1,2)"];
    w["  propinvd(i1,i2,i3,i4,jiw(ir)) = g(1,1)"];
    w["  do mu = 1,4"];
    w["     do nu = 1,4"];
    w["        ginv(mu,nu) = 0.d0"];
    w["     enddo"];
    w["     ginv(mu,mu) = 1.d0"];
    w["  enddo"];
    w["  call ludcmp(g,4,4,indx,d)"];
    w["  do nu = 1, 4"];
    w["     call lubksb(g,4,4,indx,ginv(1,nu))"];
    w["  enddo"];
    w["  propn(i1,i2,i3,i4,jiw(ir)) = ginv(1,2)"];
    w["  dpropn(i1,i2,i3,i4,jiw(ir)) = ginv(1,2)"];
    w["  propd(i1,i2,i3,i4,jiw(ir)) = ginv(1,1)"];
    w["  dpropd(i1,i2,i3,i4,jiw(ir)) = ginv(1,1) - hat1"];
    w["  derprop111(i1,i2,i3,i4,jiw(ir)) = 0.d0"];
    w["  derprop112(i1,i2,i3,i4,jiw(ir)) = 0.d0"];
    w["  derprop121(i1,i2,i3,i4,jiw(ir)) = 0.d0"];
    w["  derprop123(i1,i2,i3,i4,jiw(ir)) = 0.d0"];
    w["  der2prop1111(i1,i2,i3,i4,jiw(ir)) = 0.d0"];
    w["  der2prop1112(i1,i2,i3,i4,jiw(ir)) = 0.d0"];
    w["  der2prop1211(i1,i2,i3,i4,jiw(ir)) = 0.d0"];
    w["  der2prop1122(i1,i2,i3,i4,jiw(ir)) = 0.d0"];
    w["  der2prop1212(i1,i2,i3,i4,jiw(ir)) = 0.d0"];
    w["  der2prop1123(i1,i2,i3,i4,jiw(ir)) = 0.d0"];
    w["  der2prop1233(i1,i2,i3,i4,jiw(ir)) = 0.d0"];
    w["  der2prop1213(i1,i2,i3,i4,jiw(ir)) = 0.d0"];
    w["  do mu1 = 1,4"];
    w["     do mu2 = 1,4"];
    w["        derprop111(i1,i2,i3,i4,jiw(ir)) = derprop111(i1,i2,i3,i4,jiw(ir))"];
    wc["       - ginv(1,mu1)*derpropinv(mu1,mu2,1)*ginv(mu2,1)"];
    w["        derprop112(i1,i2,i3,i4,jiw(ir)) = derprop112(i1,i2,i3,i4,jiw(ir))"];
    wc["       - ginv(1,mu1)*derpropinv(mu1,mu2,2)*ginv(mu2,1)"];
    w["        derprop121(i1,i2,i3,i4,jiw(ir)) = derprop121(i1,i2,i3,i4,jiw(ir))"];
    wc["       - ginv(1,mu1)*derpropinv(mu1,mu2,1)*ginv(mu2,2)"];
    w["        derprop123(i1,i2,i3,i4,jiw(ir)) = derprop123(i1,i2,i3,i4,jiw(ir))"];
    wc["       - ginv(1,mu1)*derpropinv(mu1,mu2,3)*ginv(mu2,2)"];
    w["        der2prop1111(i1,i2,i3,i4,jiw(ir)) = der2prop1111(i1,i2,i3,i4,jiw(ir))"];
    wc["       - ginv(1,mu1)*der2propinv(mu1,mu2,1,1)*ginv(mu2,1)"];
    w["        der2prop1112(i1,i2,i3,i4,jiw(ir)) = der2prop1112(i1,i2,i3,i4,jiw(ir))"];
    wc["       - ginv(1,mu1)*der2propinv(mu1,mu2,1,2)*ginv(mu2,1)"];
    w["        der2prop1211(i1,i2,i3,i4,jiw(ir)) = der2prop1211(i1,i2,i3,i4,jiw(ir))"];
    wc["       - ginv(1,mu1)*der2propinv(mu1,mu2,1,1)*ginv(mu2,2)"];
    w["        der2prop1122(i1,i2,i3,i4,jiw(ir)) = der2prop1122(i1,i2,i3,i4,jiw(ir))"];
    wc["       - ginv(1,mu1)*der2propinv(mu1,mu2,2,2)*ginv(mu2,1)"];
    w["        der2prop1212(i1,i2,i3,i4,jiw(ir)) = der2prop1212(i1,i2,i3,i4,jiw(ir))"];
    wc["       - ginv(1,mu1)*der2propinv(mu1,mu2,1,2)*ginv(mu2,2)"];
    w["        der2prop1123(i1,i2,i3,i4,jiw(ir)) = der2prop1123(i1,i2,i3,i4,jiw(ir))"];
    wc["       - ginv(1,mu1)*der2propinv(mu1,mu2,2,3)*ginv(mu2,1)"];
    w["        der2prop1233(i1,i2,i3,i4,jiw(ir)) = der2prop1233(i1,i2,i3,i4,jiw(ir))"];
    wc["       - ginv(1,mu1)*der2propinv(mu1,mu2,3,3)*ginv(mu2,2)"];
    w["        der2prop1213(i1,i2,i3,i4,jiw(ir)) = der2prop1213(i1,i2,i3,i4,jiw(ir))"];
    wc["       - ginv(1,mu1)*der2propinv(mu1,mu2,1,3)*ginv(mu2,2)"];         
    w["      do mu3 = 1,4"];
    w["        do mu4 = 1,4"];
    w["         der2prop1111(i1,i2,i3,i4,jiw(ir)) = der2prop1111(i1,i2,i3,i4,jiw(ir))"];
    wc["        +ginv(1,mu1)*derpropinv(mu1,mu2,1)*ginv(mu2,mu3)"];
    wc["        *derpropinv(mu3,mu4,1)*ginv(mu4,1)"];
    wc["        +ginv(1,mu1)*derpropinv(mu1,mu2,1)*ginv(mu2,mu3)"];
    wc["        *derpropinv(mu3,mu4,1)*ginv(mu4,1)"];
    w["        der2prop1112(i1,i2,i3,i4,jiw(ir)) = der2prop1112(i1,i2,i3,i4,jiw(ir))"];
    wc["        +ginv(1,mu1)*derpropinv(mu1,mu2,1)*ginv(mu2,mu3)"];
    wc["        *derpropinv(mu3,mu4,2)*ginv(mu4,1)"];
    wc["        +ginv(1,mu1)*derpropinv(mu1,mu2,2)*ginv(mu2,mu3)"];
    wc["        *derpropinv(mu3,mu4,1)*ginv(mu4,1)"];
    w["        der2prop1211(i1,i2,i3,i4,jiw(ir)) = der2prop1211(i1,i2,i3,i4,jiw(ir))"];
    wc["        +2*ginv(1,mu1)*derpropinv(mu1,mu2,1)*ginv(mu2,mu3)"];
    wc["        *derpropinv(mu3,mu4,1)*ginv(mu4,2)"];            
    w["        der2prop1122(i1,i2,i3,i4,jiw(ir)) = der2prop1122(i1,i2,i3,i4,jiw(ir))"];
    wc["        +2*ginv(1,mu1)*derpropinv(mu1,mu2,2)*ginv(mu2,mu3)"];
    wc["        *derpropinv(mu3,mu4,2)*ginv(mu4,1)"];
    w["        der2prop1212(i1,i2,i3,i4,jiw(ir)) = der2prop1212(i1,i2,i3,i4,jiw(ir))"];
    wc["        +ginv(1,mu1)*derpropinv(mu1,mu2,1)*ginv(mu2,mu3)"];
    wc["        *derpropinv(mu3,mu4,2)*ginv(mu4,2)"];
    wc["        +ginv(1,mu1)*derpropinv(mu1,mu2,2)*ginv(mu2,mu3)"];
    wc["        *derpropinv(mu3,mu4,1)*ginv(mu4,2)"];
    w["        der2prop1123(i1,i2,i3,i4,jiw(ir)) = der2prop1123(i1,i2,i3,i4,jiw(ir))"];
    wc["        +ginv(1,mu1)*derpropinv(mu1,mu2,2)*ginv(mu2,mu3)"];
    wc["        *derpropinv(mu3,mu4,3)*ginv(mu4,1)"];
    wc["        +ginv(1,mu1)*derpropinv(mu1,mu2,3)*ginv(mu2,mu3)"];
    wc["        *derpropinv(mu3,mu4,2)*ginv(mu4,1)"];
    w["        der2prop1233(i1,i2,i3,i4,jiw(ir)) = der2prop1233(i1,i2,i3,i4,jiw(ir))"];
    wc["        +2*ginv(1,mu1)*derpropinv(mu1,mu2,3)*ginv(mu2,mu3)"];
    wc["        *derpropinv(mu3,mu4,3)*ginv(mu4,2)"];
    w["        der2prop1213(i1,i2,i3,i4,jiw(ir)) = der2prop1213(i1,i2,i3,i4,jiw(ir))"];
    wc["        +ginv(1,mu1)*derpropinv(mu1,mu2,1)*ginv(mu2,mu3)"];
    wc["        *derpropinv(mu3,mu4,3)*ginv(mu4,2)"];
    wc["        +ginv(1,mu1)*derpropinv(mu1,mu2,3)*ginv(mu2,mu3)"];
    wc["        *derpropinv(mu3,mu4,1)*ginv(mu4,2)"];
    w["        enddo"];
    w["       enddo"];
    w["      enddo"];
    w["     enddo"];     
    w["     derdprop111(i1,i2,i3,i4,jiw(ir)) = derprop111(i1,i2,i3,i4,jiw(ir))"]; 
    wc["        -dhat(1)"]; 
    w["     derdprop112(i1,i2,i3,i4,jiw(ir)) = derprop112(i1,i2,i3,i4,jiw(ir))"]; 
    wc["        -dhat(2)"]; 
    w["     derdprop121(i1,i2,i3,i4,jiw(ir)) = derprop121(i1,i2,i3,i4,jiw(ir))"]; 
    w["     derdprop123(i1,i2,i3,i4,jiw(ir)) = derprop123(i1,i2,i3,i4,jiw(ir))"]; 
    w["     der2dprop1111(i1,i2,i3,i4,jiw(ir)) = der2prop1111(i1,i2,i3,i4,jiw(ir))"]; 
    wc["        -d2hat(1,1)"]; 
    w["     der2dprop1112(i1,i2,i3,i4,jiw(ir)) = der2prop1112(i1,i2,i3,i4,jiw(ir))"]; 
    wc["        -d2hat(1,2)"]; 
    w["     der2dprop1211(i1,i2,i3,i4,jiw(ir)) = der2prop1211(i1,i2,i3,i4,jiw(ir))"]; 
    w["     der2dprop1122(i1,i2,i3,i4,jiw(ir)) = der2prop1122(i1,i2,i3,i4,jiw(ir))"]; 
    wc["        -d2hat(2,2)"]; 
    w["     der2dprop1212(i1,i2,i3,i4,jiw(ir)) = der2prop1212(i1,i2,i3,i4,jiw(ir))"]; 
    w["     der2dprop1123(i1,i2,i3,i4,jiw(ir)) = der2prop1123(i1,i2,i3,i4,jiw(ir))"]; 
    wc["        -d2hat(2,3)"]; 
    w["     der2dprop1233(i1,i2,i3,i4,jiw(ir)) = der2prop1233(i1,i2,i3,i4,jiw(ir))"]; 
    w["     der2dprop1213(i1,i2,i3,i4,jiw(ir)) = der2prop1213(i1,i2,i3,i4,jiw(ir))"]; 
    w["  enddo"]; 
WriteString[ToString[file], " 1001 ", "continue", "\n"];
    w["  enddo"]; 
    w["  enddo"]; 
    w["  enddo"]; 
    w["  enddo"];
    w[""];
    w["do i = 1,l"];
    w["do ir = 1,nr"];
    w["a(i,1,ir) = 0.d0"];
    w["enddo"];
    w["enddo"];
    w["do i1 = nhalf,n"];
    w[" i1n  = modn(i1)"];
    w[" i1h  = modh(i1)"];
    w[" do i = 1,l"];
    w[" do ir = 1,nr"];
    w[" a(i,2,ir) = 0.d0"];
    w[" enddo"];
    w[" enddo"];
    w[" do i2 = nhalf,n"];
    w["  i2n  = modn(i2)"];
    w["  i2h  = modh(i2)"];
    w["  do i = 1,l"];
    w["  do ir = 1,nr"];
    w["  a(i,3,ir) = 0.d0"];
    w["  enddo"];
    w["  enddo"];
    w["  do i3 = nhalf,n"];
    w["   i3n  = modn(i3)"];
    w["   i3h  = modh(i3)"];
    w["   do i = 1,l"];
    w["   do ir = 1,nr"];
    w["   a(i,4,ir) = 0.d0"];
    w["   enddo"];
    w["   enddo"];
    w["   do i4 = nhalf,n"];
    w["    i4n  = modn(i4)"];
    w["    i4h  = modh(i4)"];
    w["    s2sq1 = (s22(i1)+s22(i2)+s22(i3)+s22(i4))"];
    w["    sisq1 = (si2(i1)+si2(i2)+si2(i3)+si2(i4))"];
    w["    c2sq1 = (c22(i1)+c22(i2)+c22(i3)+c22(i4))"];
    w["    cisq1 = (ci2(i1)+ci2(i2)+ci2(i3)+ci2(i4))"];
    If[!FreeQ[{expr,xlistlocal},s2qu1],
       w["    s2qu1 = (s24(i1)+s24(i2)+s24(i3)+s24(i4))"]];
    w["    if (sisq1.gt.1e-9) then"];
    If[!FreeQ[{expr,proplist,xlistlocal},hat1]
      || !FreeQ[{expr,proplist,xlistlocal},dfhat1],
       w["     hat1 = 0.25d0/s2sq1"]];
    w["     do ir = 1,iov"];
    If[!FreeQ[{expr,proplist,xlistlocal},fhat1],
       w["     m1(ir) = m(ir) + r12(ir)*s2sq1"];
       w["     fhat1(ir) = 1.d0/(m1(ir)**2 + sisq1)"]];
    If[!FreeQ[{expr,proplist,xlistlocal},fhatSF1],
       w["     fhatSF1(ir) = 1.d0/(m(ir)**2 + sisq1)"]];
    (* --- addition --- *)
    If[!FreeQ[{expr,proplist,xlistlocal},dfhat1],
       w["     dfhat1(ir) = fhat1(ir) - hat1"]];
    (* --- end addition --- *)
    If[!FreeQ[{integrand,xlistlocalorig},mO] || !FreeQ[{integrand,xlistlocalorig},omegaO] || 
       !FreeQ[{integrand,xlistlocalorig},omegainvO] || !FreeQ[{integrand,xlistlocalorig},omegaplusinvO] || 
       !FreeQ[{integrand,xlistlocalorig},omegabO] || !FreeQ[{integrand,xlistlocalorig},omegabinvO],
       w["     mo1(ir) = m(ir) - r12(ir)*s2sq1"];
       w["     omegao1(ir) = sqrt(sisq1 + mo1(ir)**2)"];
       w["     omegainvo1(ir) = 1.d0/omegao1(ir)"];
       w["     omegaplusinvo1(ir) = 1.d0/(omegao1(ir)+ m(ir))"];
       w["     omegabo1(ir) = (omegao1(ir)-mo1(ir))"];
       w["     omegabinvo1(ir) = 1.d0/(omegao1(ir)-mo1(ir))"]];
    w["     enddo"];
    Do[If[tlistTrueFalse[[i]] && (FreeQ[tlistlocal[[i]],p[2]]),
          w["          t(",i,") = 0.d0"];
          Do[wc["            + ", 
                FortranForm[tlistlocal[[i]]
                   /. s2[b_] :> s2[b /. {p[1] :> ToExpression[StringJoin["i",ToString[k]]],
                                         p[2] :> ToExpression[StringJoin["j",ToString[k]]]}]
                   /. c2[b_] :> c2[b /. {p[1] :> ToExpression[StringJoin["i",ToString[k]]],
                                         p[2] :> ToExpression[StringJoin["j",ToString[k]]]}]]],
             {k,4}]],
       {i, Length[tlistlocal]}];
    w["     do i = 1,",Length[expr1]];
    w["     do ir = 1,nr"];
    w["     b(i,1,ir) = 0.d0"];
    w["     enddo"];
    w["     enddo"];
    w["     do j1 = 1,n"];
    w["      j1n  = modn(j1)"];
    w["      j1h  = modh(j1)"];
    w["      ij1n = modn(i1+j1)"];
    w["      ij1h = modh(i1+j1)"];
    w["      do i = 1,",Length[expr2]];
    w["      do ir = 1,nr"];
    w["      b(i,2,ir) = 0.d0"];
    w["      enddo"];
    w["      enddo"];
    w["      do j2 = 1,n"];
    w["       j2n  = modn(j2)"];
    w["       j2h  = modh(j2)"];
    w["       ij2n = modn(i2+j2)"];
    w["       ij2h = modh(i2+j2)"];
    w["       do i = 1,",Length[expr3]];
    w["       do ir = 1,nr"];
    w["       b(i,3,ir) = 0.d0"];
    w["       enddo"];
    w["       enddo"];
    w["       do j3 = 1,n"];
    w["        j3n  = modn(j3)"];
    w["        j3h  = modh(j3)"];
    w["        ij3n = modn(i3+j3)"];
    w["        ij3h = modh(i3+j3)"];
    w["        do i = 1,",Length[expr4]];
    w["        do ir = 1,nr"];
    w["        b(i,4,ir) = 0.d0"];
    w["        enddo"];
    w["        enddo"];
    w["        do j4 = 1,n"];
    w["         j4n  = modn(j4)"];
    w["         j4h  = modh(j4)"];
    w["         ij4n = modn(i4+j4)"];
    w["         ij4h = modh(i4+j4)"];
    w["         s2sq12 = (s22(j1+i1)+s22(j2+i2)+s22(j3+i3)+s22(j4+i4))"];
    w["         s2sq2  = (s22(j1)+s22(j2)+s22(j3)+s22(j4))"];
    w["         sisq12 = (si2(j1+i1)+si2(j2+i2)+si2(j3+i3)+si2(j4+i4))"];
    w["         sisq2  = (si2(j1)+si2(j2)+si2(j3)+si2(j4))"];
    w["         c2sq12 = (c22(j1+i1)+c22(j2+i2)+c22(j3+i3)+c22(j4+i4))"];
    w["         c2sq2  = (c22(j1)+c22(j2)+c22(j3)+c22(j4))"];
    w["         cisq12 = (ci2(j1+i1)+ci2(j2+i2)+ci2(j3+i3)+ci2(j4+i4))"];
    w["         cisq2  = (ci2(j1)+ci2(j2)+ci2(j3)+ci2(j4))"];
    w["         s2qu12 = (s24(j1+i1)+s24(j2+i2)+s24(j3+i3)+s24(j4+i4))"];
    w["         s2qu2  = (s24(j1)+s24(j2)+s24(j3)+s24(j4))"];
    w["         if (sisq12.gt.1e-9 .and. sisq2.gt.1e-9) then"];
    w["          hat2  = 0.25d0/s2sq2 "];
    w["          hat12 = 0.25d0/s2sq12"];
    Do[If[tlistTrueFalse[[i]] && (!FreeQ[tlistlocal[[i]],p[2]]),
          w["          t(",i,") = 0.d0"];
          Do[wc["            + ", 
                FortranForm[tlistlocal[[i]]
                   /. s2[b_] :> s2[b /. {p[1] :> ToExpression[StringJoin["i",ToString[k]]],
                                         p[2] :> ToExpression[StringJoin["j",ToString[k]]]}]
                   /. c2[b_] :> c2[b /. {p[1] :> ToExpression[StringJoin["i",ToString[k]]],
                                         p[2] :> ToExpression[StringJoin["j",ToString[k]]]}]]],
             {k,4}]],
       {i, Length[tlistlocal]}];
    w["          do ir = 1,iov"];
    If[!FreeQ[proplist,fhat2] || !FreeQ[expr,fhat2],
       w["           m2(ir) = m(ir) + r12(ir)*s2sq2"];
       w["           fhat2(ir) =1.d0/(m2(ir)**2 + sisq2 )"]];
    If[!FreeQ[proplist,fhatSF2] || !FreeQ[expr,fhatSF2],
       w["           fhatSF2(ir) =1.d0/(m(ir)**2 + sisq2 )"]];
    If[!FreeQ[proplist,fhat12] || !FreeQ[expr,fhat12],
       w["           m12(ir) = m(ir) + r12(ir)*s2sq12"];
       w["           fhat12(ir)=1.d0/(m12(ir)**2 + sisq12)"]];
    If[!FreeQ[proplist,fhatSF12] || !FreeQ[expr,fhatSF12],
       w["           fhatSF12(ir)=1.d0/(m(ir)**2 + sisq12)"]];
    (* --- addition --- *)
    If[!FreeQ[proplist,dfhat2] || !FreeQ[expr,dfhat2],
       w["           dfhat2(ir) = fhat2(ir) - hat2"]];
    If[!FreeQ[proplist,dfhat12] || !FreeQ[expr,dfhat12],
       w["           dfhat12(ir) = fhat12(ir) - hat12"]];
    (* --- end addition --- *)
    If[!FreeQ[{integrand,xlistlocalorig},mO] || !FreeQ[{integrand,xlistlocalorig},omegaO] || 
       !FreeQ[{integrand,xlistlocalorig},omegainvO] || !FreeQ[{integrand,xlistlocalorig},omegaplusinvO] || 
       !FreeQ[{integrand,xlistlocalorig},omegabO] || !FreeQ[{integrand,xlistlocalorig},omegabinvO],
       w["     mo2(ir) = m(ir) - r12(ir)*s2sq2"];
       w["     omegao2(ir) = sqrt(sisq2 + mo2(ir)**2)"];
       w["     omegainvo2(ir) = 1.d0/omegao2(ir)"];
       w["     omegaplusinvo2(ir) = 1.d0/(omegao2(ir)+ m(ir))"];
       w["     omegabo2(ir) = (omegao2(ir)-mo2(ir))"];
       w["     omegabinvo2(ir) = 1.d0/(omegao2(ir)-mo2(ir))"];
       w["     mo12(ir) = m(ir) - r12(ir)*s2sq12"];
       w["     omegao12(ir) = sqrt(sisq12 + mo12(ir)**2)"];
       w["     omegainvo12(ir) = 1.d0/omegao12(ir)"];
       w["     omegaplusinvo12(ir) = 1.d0/(omegao12(ir)+ m(ir))"];
       w["     omegabo12(ir) = (omegao12(ir)-mo12(ir))"];
       w["     omegabinvo12(ir) = 1.d0/(omegao12(ir)-mo12(ir))"];
       w["     omegaplusinvo1p2(ir) = 1.d0/(omegao1(ir)+ omegao2(ir))"];
       w["     omegaplusinvo1p12(ir) = 1.d0/(omegao1(ir)+ omegao12(ir))"];
       w["     omegaplusinvo2p12(ir) = 1.d0/(omegao2(ir)+ omegao12(ir))"]];
    w["          enddo"];
    w["          do ir = 1, nr"];
    Do[If[xlistTrueFalse[[i]],
          w["          x(",i,") = 0.d0"];
          If[Head[xlistlocal[[i]]]===Plus,
             Do[
                If[Head[xlistlocal[[i,j]]]===Times && Length[xlistlocal[[i,j]]]>5,
		   wc["  +", FortranForm[Take[xlistlocal[[i,j]],4]]];
                   If[Length[Drop[xlistlocal[[i,j]],4]]>4,
                      wc["  *", FortranForm[Take[Drop[xlistlocal[[i,j]],4],3]]];
                      wc["  *", FortranForm[Drop[Drop[xlistlocal[[i,j]],4],3]]],
                      wc["  *", FortranForm[Drop[xlistlocal[[i,j]],4]]]],
                   wc["  +", FortranForm[xlistlocal[[i,j]]]]],
                {j,Length[xlistlocal[[i]]]}],
             wc["  +", FortranForm[xlistlocal[[i]]]]]],
       {i, Length[xlistlocal]}];
    w["           prop = ", proplist[[2]]];
    Do[If[proplist[[2]]===FortranForm[1],
          w["b(",j,",4,ir) = b(",j,",4,ir) + "];
           If[Head[expr4[[j,1,1]]]===Times && Length[expr4[[j,1,1]]] > 4,
              wc["  ",Take[#,4]& /@ expr4[[j,1]],"*"];
               temp = Drop[#,4]& /@ expr4[[j,1]];
               If[Head[temp[[1]]]===Times && Length[temp[[1]]] > 4,
                  wc["  ",Take[#,4]& /@ temp,"*"];
	           wc["  ",Drop[#,4]& /@ temp],
                  wc["  ",temp]],
              wc["  ",expr4[[j,1]]]],
          If[expr4[[j,1]]===FortranForm[1],
             w["b(",j,",4,ir) = b(",j,",4,ir) + prop"],
             w["b(",j,",4,ir) = b(",j,",4,ir) + prop*"];
              wc["  ",expr4[[j,1]]]]],
       {j,Length[expr4]}];
    w["          enddo"];
    w["         endif"];
    w["        enddo"];
    w["        do ir = 1,nr"];
    Do[If[expr3[[j,1]]===FortranForm[1],
          w["b(",j,",3,ir) = b(",j,",3,ir) + b(",index3[[j]],",4,ir)"],
          w["b(",j,",3,ir) = b(",j,",3,ir) + b(",index3[[j]],",4,ir)*"];
          wc["  ",expr3[[j,1]]]],
       {j,Length[expr3]}];
    w["        enddo"];
    w["       enddo"];
    w["       do ir = 1,nr"];
    Do[If[expr2[[j,1]]===FortranForm[1],
          w["b(",j,",2,ir) = b(",j,",2,ir) + b(",index2[[j]],",3,ir)"],
          w["b(",j,",2,ir) = b(",j,",2,ir) + b(",index2[[j]],",3,ir)*"];
          wc["  ",expr2[[j,1]]]],
       {j,Length[expr2]}];
    w["       enddo"];
    w["      enddo"];
    w["      do ir = 1,nr"];
    Do[If[expr1[[j,1]]===FortranForm[1],
          w["b(",j,",1,ir) = b(",j,",1,ir) + b(",index1[[j]],",2,ir)"],
          w["b(",j,",1,ir) = b(",j,",1,ir) + b(",index1[[j]],",2,ir)*"];
          wc["  ",expr1[[j,1]]]],
       {j,Length[expr1]}];
    w["      enddo"];
    w["     enddo"];
    w["     do ir = 1,nr"];
    w["     prop  = ", proplist[[1]]];
    w["     if (i4.eq.n .or. (i4.eq.nhalf .and. nmod2.eq.0))"];
    wc["         prop = 0.5d0 * prop"];
    Do[If[expr[[j,4]]===FortranForm[1],
          w["a(",j,",4,ir) = a(",j,",4,ir) + prop*b(",index[[j]],",1,ir)"],
          w["a(",j,",4,ir) = a(",j,",4,ir) + prop*b(",index[[j]],",1,ir)*"];
          wc["  ",expr[[j,4]]]],
       {j,Length[expr]}];
    w["     enddo"];
    w["    endif"];
    w["   enddo"];
    w["   if (i3.eq.n .or. (i3.eq.nhalf .and. nmod2.eq.0)) then"];
    w["    do ir = 1,nr"];
    w["    do i = 1,l"];
    w["    a(i,4,ir) = a(i,4,ir) * 0.5d0"];
    w["    enddo"];
    w["    enddo"];
    w["   endif"];
    w["   do ir = 1,nr"];
    Do[If[expr[[j,3]]===FortranForm[1],
          w["a(",j,",3,ir) = a(",j,",3,ir) + a(",j,",4,ir)"],
          w["a(",j,",3,ir) = a(",j,",3,ir) + a(",j,",4,ir)*"];
          wc["  ",expr[[j,3]]]],
       {j,Length[expr]}];
    w["   enddo"];
    w["  enddo"];
    w["  if (i2.eq.n .or. (i2.eq.nhalf .and. nmod2.eq.0)) then"];
    w["   do ir = 1,nr"];
    w["   do i = 1,l"];
    w["   a(i,3,ir) = a(i,3,ir) * 0.5d0"];
    w["   enddo"];
    w["   enddo"];
    w["  endif"];
    w["  do ir = 1,nr"];
    Do[If[expr[[j,2]]===FortranForm[1],
          w["a(",j,",2,ir) = a(",j,",2,ir) + a(",j,",3,ir)"],
          w["a(",j,",2,ir) = a(",j,",2,ir) + a(",j,",3,ir)*"];
          wc["  ",expr[[j,2]]]],
       {j,Length[expr]}];
    w["  enddo"];
    w[" enddo"];
    w[" if (i1.eq.n .or. (i1.eq.nhalf .and. nmod2.eq.0)) then"];
    w["  do ir = 1,nr"];
    w["  do i = 1,l"];
    w["  a(i,2,ir) = a(i,2,ir) * 0.5d0"];
    w["  enddo"];
    w["  enddo"];
    w[" endif"];
    w[" do ir = 1,nr"];
    Do[If[expr[[j,1]]===FortranForm[1],
          w["a(",j,",1,ir) = a(",j,",1,ir) + a(",j,",2,ir)"],
          w["a(",j,",1,ir) = a(",j,",1,ir) + a(",j,",2,ir)*"];
          wc["  ",expr[[j,1]]]],
       {j,Length[expr]}];
    w[" enddo"];
    w["enddo"];
    w["do ir = 1,nr"];
    Do[w["result(",k,") = 0.d0"];
       Do[If[!(factorlist[[j,k]] === FortranForm[0]),
             w["result(",k,") = result(",k,") + a(",j,",1,ir) * "];
             wc["(",N[factorlist[[j,k]],16],")"]],
          {j,Length[expr]}];
       w["result(",k,") = result(",k,") * 2**4 / float(n)**8"],
       {k,varlength}];
    w[" write(*,1002) n,r(jov(ir)), m(jov(ir)),"];
    wc["    cprop0(jiw(ir)), cprop1(jiw(ir)),"];
    wc["    cprop2(jiw(ir)), cprop3(jiw(ir)), result"];
    w["enddo"];
    w["call flush(6)"];
    WriteString[ToString[file], " 1000 ", "continue", "\n"];
    w["stop"];
    WriteString[ToString[file], " 1002 ", 
     "format(I4,6(1X,F10.7),100(/,1X,E30.18E2,1X,E30.18E2,1X,E30.18E2))", "\n"];
    w["end"];

  ]
