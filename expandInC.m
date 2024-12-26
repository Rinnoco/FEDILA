(* 
   Cvitanovic algorithm for SU(N)
   cf. Comp. Pys. Commun. 48 (1988) 327.
   all formulae in \TeX notation!
   spur[a,b,c...] = \Tr\{T^a T^b T^c ...\};
   normalization: spur[a,b] = \delta_{ab}/2. 
*)
Ngluon = Nc^2 - 1;
spur[] = Nc;
(* 
   contractions: 
   T^a_{ij} T^a_{kl} = (\delta_{il}\delta_{jk}
              - \delta_{ij}\delta_{kl}/n)/2 
*)
spur [x___, xcontract_, y___, xcontract_, z___] := 
    (spur [y] * spur [x, z] - 
           spur [x, y, z] / Nc) / 2;
spur /: spur [x___, xcontract_, y___] *
        spur [t___, xcontract_, u___] :=
       (spur [x, u, t, y] - spur [x, y] *
             spur [t, u] / Nc) / 2;
spur /: spur [x___, xcontract_, y___] ^2 :=
       (spur [x, y, x, y] -
        spur [x, y]^2 / Nc) / 2;
(* 
   ciclicity of spur: try with & without 
*) 
spur [a_, x___, b_, y___] := 
      spur [b, y, a, x] /; !OrderedQ[{a,b}];

spur[_] = 0

(* ----------------------------------------------------------------- *)

(* NB: A minus sign that appeared in the rule below, which was meant to 
       take into account the effect of a closed fermion loop, has been
       removed, due to erroneous behaviour         16/11/2006        *)

openspur[i_,a___,i_] :=  spur[a];

openspur /: openspur[a__,i_] * openspur[i_,b__] := openspur[a,b];

openspur[i_,a___,b_,c___,b_,d___,j_] := (openspur[i,a,d,j] spur[c] - 
                                        openspur[i,a,c,d,j] / Nc) / 2;

openspur /: openspur [x__, xcontract_, y__] *
        spur [t___, xcontract_, u___] :=
       (openspur [x, u, t, y] - openspur [x, y] *
             spur [t, u] / Nc) / 2;

openspur /: openspur [x__, xcontract_, y__] *
        openspur [t___, xcontract_, u___] :=
       (openspur[x, u] * openspur[t, y] - openspur [x, y] *
             openspur [t, u] / Nc) / 2;

(* ----------------------------------------------------------------- *)

(* In what follows, X stands for an arbitrary product of 0 or more gamma matrices, 
   which is supposed to appear at most once                                        *)
dtracerules := 
  {dtrace[i_,a___,i_]:> gtrace[a],
   dtrace[a__,b_?(FreeQ[#,gamma5]&),b_,c__]:> dtrace[a,c] delm[b,b],
   dtrace[a__,gamma5,gamma5,c__]:> dtrace[a,c],
   dtrace[a__,b_?((FreeQ[#,gamma5] && FreeQ[#,X])&),c_?((FreeQ[#,gamma5] && FreeQ[#,X])&),d__]:>
           -dtrace[a,c,b,d]+ 2 dtrace[a,d] delm[b,c] /; !OrderedQ[{b,c}],
   dtrace[a__,b_?((FreeQ[#,gamma5] && FreeQ[#,X])&),gamma5,c__] :> - dtrace[a,gamma5,b,c],
   dtrace[a__,i_] * dtrace[i_,b__] :> dtrace[a,b]}
                     
(* ------------------------------------------------------------------- *)

(* In what follows, X stands for an arbitrary product of 0 or more gamma matrices, 
   which is supposed to appear at most once                                        *)
gtracerules = 
  {gtrace[]:> 4,
   gtrace[a___,gamma5,gamma5,b___] :> gtrace[a,b],
   gtrace[c_?(FreeQ[#,X]&)] :> 0,
   gtrace[a__,X,b___] :> gtrace[X,b,a],
   gtrace[a__,X[1],b___] :> gtrace[X[1],b,a],
   gtrace[a__?(FreeQ[#,X]&),X[i_],b___] :> gtrace[X[i],b,a],
   gtrace[a__]:>0 /; (FreeQ[{a},gamma5] && FreeQ[{a},X] && OddQ[Length[{a}]]),
   gtrace[gamma5,a___]:>0 /; (FreeQ[{a},gamma5] && FreeQ[{a},X] && OddQ[Length[{a}]]),
   gtrace[gamma5,a___]:>0 /; (FreeQ[{a},gamma5] && FreeQ[{a},X] && (Length[{a}]==2)),
   gtrace[a___,b_?(FreeQ[#,gamma5]&),b_,d___]:> gtrace[a,d] delm[b,b],
   gtrace[a___,b_?((FreeQ[#,gamma5] && FreeQ[#,X])&),gamma5,c___]:> - gtrace[a,gamma5,b,c],
   gtrace[a___,b_?(FreeQ[#,gamma5]&),c___,d_?((FreeQ[#,gamma5] && FreeQ[#,X])&),b_,e___]:>
                   - gtrace[a,b,c,b,d,e] + 2 gtrace[a,b,c,e] delm[b,d] /; !OrderedQ[{d,b}],
   gtrace[a_?(FreeQ[#,gamma5]&),x___,b_?(FreeQ[#,gamma5]&),y___]:>
                   gtrace[b,y,a,x] /; (!OrderedQ[{a,b}] && FreeQ[gtrace[a,x,b,y],X]),
   gtrace[gamma5,a_?(FreeQ[#,gamma5]&),x___,b_?(FreeQ[#,gamma5]&),y___]:>
                   gtrace[b,y,gamma5,a,x] /; (!OrderedQ[{a,b}] && FreeQ[gtrace[a,x,b,y],X]),
   gtrace[a___,b_?((FreeQ[#,gamma5] && FreeQ[#,X])&),c_?((FreeQ[#,gamma5] && FreeQ[#,X])&),d___]:>
           -gtrace[a,c,b,d]+ 2 gtrace[a,d] delm[b,c] /; !OrderedQ[{b,c}],
   gtrace[a_,b_]:> 4 delm[a,b] /; (FreeQ[{a,b},gamma5] && FreeQ[{a,b},X]),
   gtrace[a_,b_,c_,d_]:> 4 (delm[a,b] delm[c,d] - delm[a,c] delm[b,d] +
                            delm[a,d] delm[b,c]) /; (FreeQ[{a,b,c,d},gamma5] && FreeQ[{a,b,c,d},X]),
   gtrace[a_,b_,c_,d_,e_,f_] :>
      delm[a,b] gtrace[c,d,e,f] - delm[a,c] gtrace[b,d,e,f] +
      delm[a,d] gtrace[b,c,e,f] - delm[a,e] gtrace[b,c,d,f] +
      delm[a,f] gtrace[b,c,d,e] /; (FreeQ[{a,b,c,d,e,f},gamma5] && FreeQ[{a,b,c,d,e,f},X]),
   gtrace[aFirst_,aRest__] :>
      Module[{sum = 0, sign = 1},
             Do[sum = sum + sign * delm[aFirst,List[aRest][[i]]] * gtrace @@ Drop[List[aRest],{i}]; sign = - sign,
	        {i, Length[{aRest}]}];
	     sum] /; (FreeQ[{aFirst,aRest},gamma5] && FreeQ[{aFirst,aRest},X])}

(* A program to expand in color indices *)

expandInCnew[expr_] := combineNc[combineNc[expandInC[expr /. f[a_,b_,c_]:> 
                                         - 2 im (spur[a,b,c]-spur[a,c,b])]] /.
                       spur[a_,b_,c_]:> im/4 f[a,b,c] + 1/4 d[a,b,c] ]
d[args__] := d @@ Sort[{args}] /; !OrderedQ[{args}]
f[___,a_,___,a_,___] =0; 
f[args__] := (Signature[{args}] (f @@ Sort[{args}]) /;  !OrderedQ[{args}] );

expandInC[expr_Plus] := expandInC /@ expr

expandInC[expr_Times] := 
  expandInC[Select[expr,(!colorlessQ[#])&]] * Select[expr,colorlessQ] /;
    Or @@ (colorlessQ /@ List @@ expr)

expandInC[expr_Plus b_] := expandInC[b #]& /@ expr /; 
                           !purecolorQ[expr] && And @@ ((!colorlessQ[#])& /@ List @@ (expr b))

expandInC[expr_] := expr /; !MemberQ[{Times,Plus,Power},Head[expr]]

expandInC[expr_] := Expand[expr] /; purecolorQ[expr] 
                       
variables[expr_] := Complement[Union @@ (variables1 /@ Variables[expr]),
                               {Plus,Times, Power}]                       
variables1[expr_] := If[AtomQ[expr],
                        Variables[expr],
                        Union[Variables[Head[expr]],
                              Sequence @@ (variables1 /@ List @@ expr)]]

colorlessQ[expr_] := And @@ (FreeQ[expr,#]& /@ {delc,spur,openspur,f,d,Nc})

purecolorQ[expr_] := 
   Complement[variables[expr],{delc,spur,openspur,f,a,b,c,d,af,bf,cf,Nc}]==={}

(* combineNc[expr_] := 
                      (If[purecolorQ[#], Simplify[#], #, #] )&  //@ expr  *)

combineNc[expr_] := Factor[Simplify[expr]] /; purecolorQ[expr]
combineNc[expr_Plus] := If[purecolorQ[expr], Simplify[expr], combineNc /@ expr]
combineNc[expr_] := expr /; colorlessQ[expr]
combineNc[expr_Times] := 
  combineNc[Select[expr,(!colorlessQ[#])&]] * Select[expr,colorlessQ] /;
    Or @@ (colorlessQ /@ List @@ expr)
