A::usage = StringJoin[
   "A[l[i],c[j]] is the field of the i-th link of the loop. ",
   "A[k[i],mu[i],c[i]] is the field of the i-th leg of the vertex."];
k::usage = "k[i] is the momentum of the i-th leg of the vertex";
c::usage = "c[i] is the i-th color index";
mu::usage = "mu[i] is the i-th external (A) Lorentz index";
rho::usage = "rho[i] is the i-th Lorentz index to be summed over";
(* Print without new-line *)
PrintString[a__] := WriteString[$Output, a];
(* Output formats *)
Format[c[i_]] := Subscripted[c[i]];
Format[b[i_]] := Subscripted[b[i]];
Format[a[i_]] := Subscripted[a[i]];
Format[mu[i_]] := Subscripted[mu[i]];
Format[rho[i_]] := Subscripted[rho[i]];
Format[nu[i_]] := Subscripted[nu[i]];
Format[k[i_]] := Subscripted[k[i]];
Format[p[i_]] := Subscripted[p[i]];
Format[q[i_]] := Subscripted[q[i]];
Format[l[i_]] := Subscripted[l[i]];
Format[cf[i_]] := Subscripted[cf[i]];
Format[bf[i_]] := Subscripted[bf[i]];
Format[af[i_]] := Subscripted[af[i]];
Format[fmu[i_]] := Subscripted[fmu[i]];
Format[frho[i_]] := Subscripted[frho[i]];
Format[fnu[i_]] := Subscripted[fnu[i]];

(* Antisymmetric Ricci tensor *)
epsilon::usage = 
"epsilon[mu,nu,rho,sigma] is the Ricci tensor";
epsilon[___,a_,___,a_,___] := 0; 
epsilon[args__] := 
   (Signature[{args}] (epsilon @@ Sort[{args}]) /; !OrderedQ[{args}] );

(* Symmetric delta operators *)
delm::usage = "delm is the Cronecker delta for Lorentz indices";
delm[] = 1;
delm[_] := 1;
(* DANGEROUS: "Collect" gives wrong results with this:
 delm/: delm[a_,b__]^_ := delm[a,b]                *)
delm[args__] := delm @@ Sort[{args}] /; !OrderedQ[{args}]
renamem[expr_Plus] := renamem /@ expr
renamem[expr_. delm[a_,b__]] := delm[a,b] renamem[expr /. ((# -> a)& /@ {b})]
renamem[expr_] := expr /; FreeQ[expr,delm]

(* Simplify by collecting terms, color structure first *)
collectCFirst[expr_] := Block[
    {exprNew,varList,collectList,mapLevel,maxLevel,oldLevel},
    exprNew = Expand[expr];
    maxLevel = Depth[exprNew];
    exprNew = FactorTerms[exprNew];
    oldLevel = maxLevel;
    maxLevel = Depth[exprNew];
    mapLevel = 0;
    mapLevel += maxLevel - oldLevel;
    varList = Variables[exprNew];
    collectList = Append[Cases[varList,_A], g];
    exprNew = Map[ Collect[#1,collectList]&, exprNew, {mapLevel}];
    oldLevel = maxLevel;
    maxLevel = Depth[exprNew];
    mapLevel += maxLevel - oldLevel;
    collectList = Union[ Cases[varList,_f], Cases[varList,_spur],
			 Cases[varList,_delc] ];
    exprNew = Map[ Collect[#1,collectList]&, exprNew, {mapLevel}];
    oldLevel = maxLevel;
    maxLevel = Depth[exprNew];
    mapLevel += maxLevel - oldLevel;
    collectList = Union[Cases[varList,_delm], Cases[varList,_epsilon]];
    exprNew = Map[ Collect[#1,collectList]&, exprNew, {mapLevel}];
    Return[exprNew]
];
