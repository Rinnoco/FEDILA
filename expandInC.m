traceGen::usage     = "traceGen[a,b,...,c,d] is the trace of the product 
of generators: tr(T^a * T^b * ... * T^c * T^d)"

productGen::usage   = "productGen[i,a,b,...,c,d,j] is the product 
of generators: (T^a * T^b * ... * T^c * T^d)_{ij}"

traceDirac::usage   = "traceDirac[a,b,...,c,d] is the trace of a product of Dirac matrices.
The arguments of traceDirac can be: 
   gamma5, 
   nu[_] (an external Lorentz index taking values: 1,2,3,4), 
   rho[_] (a dummy Lorentz index taking values: 1,2,3,4,...,nDim),
   X, Y (unspecified Dirac matrices; each may appear at most once)
Example: traceDirac[gamma5,nu[3],X,rho[2],gamma5,Y] = 
            tr(gamma5 * gamma_nu[3] * X * gamma_rho[2] * gamma5 * Y)" 

productDirac::usage = "productDirac[i,a,b,...,c,d,j] is a product of Dirac matrices.
Example: productDirac[i,gamma5,nu[3],X,rho[2],gamma5,Y,j] = 
            (gamma5 * gamma_nu[3] * X * gamma_rho[2] * gamma5 * Y)_{ij}
The possible values for arguments a,b,...,c,d are:
   gamma5, 
   nu[_] (an external Lorentz index taking values: 1,2,3,4), 
   rho[_] (a dummy Lorentz index taking values: 1,2,3,4,...,nDim),
   X, Y (unspecified Dirac matrices; each may appear at most once)"

colorExpand::usage  = "colorExpand[expr_] performs color simplifications in expr, 
without expanding subexpressions which do not contain color indices "

Nc::usage           = "Nc is the number of colors "

productDiracRules4dim::usage     = "This is a set of substitution rules which may be applied repeatedly
in order to simplify products of Dirac matrices in 4 dimensions"

productDiracRulesDdim::usage     = "This is a set of substitution rules which may be applied repeatedly
in order to simplify products of Dirac matrices in nDim = 4-2e dimensions "

traceDiracRules4dim::usage       = "This is a set of substitution rules which may be applied repeatedly
in order to simplify traces of Dirac matrices in 4 dimensions"

traceDiracRulesDdim::usage       = "This is a set of substitution rules which may be applied repeatedly
in order to simplify traces of Dirac matrices in nDim = 4-2e 
dimensions;
hv = 0, 1 in the naive and tHooft-Veltman definitions of gamma5, 
respectively "

hv::usage           = " hv = 0 (1) in naive(tHooft-Veltman) definition of gamma5 "    

delm::usage       = "delm[a_,b_,...,c_] is a Kronecker delta whose 2 or more arguments
are Lorentz indices"

deltaColor::usage   = "deltaColor[a_,b_] is a Kronecker delta of two color indices 
in the adjoint representation"
SetAttributes[deltaColor, Orderless];


f::usage = 
"f[a,b,c] are the antisymmetric structure constants";

d::usage            = "d[a,b,c] is the symmetric trace of a 3-generator product: 
d[a,b,c] = 2 tr(T^a T^b T^c + T^a T^c T^b)  "

hold::usage         = "hold[a_] = (a)"

e::usage            = "e is related to the dimension (nDim) of spacetime, 
through: nDim = 4 - 2 e"

(*
   normalization: traceGen[a,b] = \delta_{ab}/2.
   Nc = number of colors
*)
traceGen[] = Nc;
(* 
   contractions: 
   T^a_{ij} T^a_{kl} = (\delta_{il}\delta_{jk}
              - \delta_{ij}\delta_{kl}/Nc)/2 
*)
traceGen [x___, xcontract_, y___, xcontract_, z___] := 
    (traceGen [y] * traceGen [x, z] - 
           traceGen [x, y, z] / Nc) / 2;
traceGen /: traceGen [x___, xcontract_, y___] *
        traceGen [t___, xcontract_, u___] :=
       (traceGen [x, u, t, y] - traceGen [x, y] *
             traceGen [t, u] / Nc) / 2;
traceGen /: traceGen [x___, xcontract_, y___] ^2 :=
       (traceGen [x, y, x, y] -
        traceGen [x, y]^2 / Nc) / 2;
	
(*    cyclicity of trace: *) 
traceGen [a_, x___, b_, y___] := 
      traceGen [b, y, a, x] /; !OrderedQ[{a,b}];

traceGen[_] = 0


(* ----------------------------------------------------------------- *)

productGen[i_,a___,i_] :=  traceGen[a];

productGen /: productGen[a__,i_] * productGen[i_,b__] := productGen[a,b];

productGen[i_,a___,b_,c___,b_,d___,j_] := (productGen[i,a,d,j] traceGen[c] - 
                                        productGen[i,a,c,d,j] / Nc) / 2;

productGen /: productGen [x__, xcontract_, y__] *
        traceGen [t___, xcontract_, u___] :=
       (productGen [x, u, t, y] - productGen [x, y] *
             traceGen [t, u] / Nc) / 2;

productGen /: productGen [x__, xcontract_, y__] *
        productGen [t___, xcontract_, u___] :=
       (productGen[x, u] * productGen[t, y] - productGen [x, y] *
             productGen [t, u] / Nc) / 2;

(* ----------------------------------------------------------------- *)

(* In what follows, X and Y stand for an arbitrary product of 0 or more gamma matrices, 
   which is supposed to appear at most once                                        *)
   
productDiracRules4dim := 
  {productDirac[i_,a___,i_]:> traceDirac[a],
   productDirac[a__,b_?(FreeQ[#,gamma5]&),b_,c__]:> productDirac[a,c] delm[b,b],
   productDirac[a__,gamma5,gamma5,c__]:> productDirac[a,c],
   productDirac[a__,b_?((FreeQ[#,gamma5] && FreeQ[#,X] && FreeQ[#,Y])&),c_?((FreeQ[#,gamma5] && FreeQ[#,X] && FreeQ[#,Y])&),d__]:>
           -productDirac[a,c,b,d]+ 2 productDirac[a,d] delm[b,c] /; !OrderedQ[{b,c}],
   productDirac[a__,b_?((FreeQ[#,gamma5] && FreeQ[#,X] && FreeQ[#,Y])&),gamma5,c__] :> - productDirac[a,gamma5,b,c],
   productDirac[a__,i_] * productDirac[i_,b__] :> productDirac[a,b]}

productDiracRulesDdim := 
  {productDirac[i_,a___,i_]:> traceDirac[a],
   productDirac[a__,b_?(FreeQ[#,gamma5]&),b_,c__]:> productDirac[a,c] delm[b,b],
   productDirac[a__,gamma5,gamma5,c__]:> productDirac[a,c],
   productDirac[a__,b_?((FreeQ[#,gamma5] && FreeQ[#,X] && FreeQ[#,Y])&),c_?((FreeQ[#,gamma5] && FreeQ[#,X] && FreeQ[#,Y])&),d__]:>
           -productDirac[a,c,b,d]+ 2 productDirac[a,d] delm[b,c] /; !OrderedQ[{b,c}],
   productDirac[a__,i_] * productDirac[i_,b__] :> productDirac[a,b]}
                  
(* ------------------------------------------------------------------- *)

(* In what follows, X and Y stand for an arbitrary product of 0 or more gamma matrices; 
   X and/or Y may appear at most once                                                    *)

traceDiracRules4dim = 
  {traceDirac[]:> 4,
   traceDirac[a___,gamma5,gamma5,b___] :> traceDirac[a,b],
   traceDirac[c_?((FreeQ[#,X] && FreeQ[#,Y])&)] :> 0,
   traceDirac[a__,X,b___] :> traceDirac[X,b,a],
   traceDirac[a__]:>0 /; (FreeQ[{a},gamma5] && FreeQ[{a},X] && FreeQ[{a},Y] && OddQ[Length[{a}]]),
   traceDirac[gamma5,a___]:>0 /; (FreeQ[{a},gamma5] && FreeQ[{a},X] && FreeQ[{a},Y] && OddQ[Length[{a}]]),
   traceDirac[gamma5,a___]:>0 /; (FreeQ[{a},gamma5] && FreeQ[{a},X] && FreeQ[{a},Y] && (Length[{a}]==2)),
   traceDirac[a___,b_?(FreeQ[#,gamma5]&),b_,d___]:> traceDirac[a,d] delm[b,b],
   traceDirac[a___,b_?((FreeQ[#,gamma5] && FreeQ[#,X] && FreeQ[#,Y])&),gamma5,c___]:> - traceDirac[a,gamma5,b,c],
   traceDirac[a___,b_?(FreeQ[#,gamma5]&),c___,d_?((FreeQ[#,gamma5] && FreeQ[#,X] && FreeQ[#,Y])&),b_,e___]:>
                   - traceDirac[a,b,c,b,d,e] + 2 traceDirac[a,b,c,e] delm[b,d] /; !OrderedQ[{d,b}],
   traceDirac[a_?(FreeQ[#,gamma5]&),x___,b_?(FreeQ[#,gamma5]&),y___]:>
                   traceDirac[b,y,a,x] /; (!OrderedQ[{a,b}] && FreeQ[traceDirac[a,x,b,y],X] && FreeQ[traceDirac[a,x,b,y],Y]),
   traceDirac[gamma5,a_?(FreeQ[#,gamma5]&),x___,b_?(FreeQ[#,gamma5]&),y___]:>
                   traceDirac[b,y,gamma5,a,x] /; (!OrderedQ[{a,b}] && FreeQ[traceDirac[a,x,b,y],X] && FreeQ[traceDirac[a,x,b,y],Y]),
   traceDirac[a_,b_]:> 4 delm[a,b] /; (FreeQ[{a,b},gamma5] && FreeQ[{a,b},X] && FreeQ[{a,b},Y]),
   traceDirac[a___,b_?((FreeQ[#,gamma5] && FreeQ[#,X] && FreeQ[#,Y])&),c_?((FreeQ[#,gamma5] && FreeQ[#,X] && FreeQ[#,Y])&),d___]:>
           -traceDirac[a,c,b,d]+ 2 traceDirac[a,d] delm[b,c] /; !OrderedQ[{b,c}],
   traceDirac[a_,b_,c_,d_]:> 4 (delm[a,b] delm[c,d] - delm[a,c] delm[b,d] +
                            delm[a,d] delm[b,c]) /; (FreeQ[{a,b,c,d},gamma5] && FreeQ[{a,b,c,d},X] && FreeQ[{a,b,c,d},Y]),
   traceDirac[a_,b_,c_,d_,e_,f_] :>
      delm[a,b] traceDirac[c,d,e,f] - delm[a,c] traceDirac[b,d,e,f] +
      delm[a,d] traceDirac[b,c,e,f] - delm[a,e] traceDirac[b,c,d,f] +
      delm[a,f] traceDirac[b,c,d,e] /; (FreeQ[{a,b,c,d,e,f},gamma5] && FreeQ[{a,b,c,d,e,f},X] && FreeQ[{a,b,c,d,e,f},Y]),
   traceDirac[aFirst_,aRest__] :>
      Module[{sum = 0, sign = 1},
             Do[sum = sum + sign * delm[aFirst,List[aRest][[i]]] * traceDirac @@ Drop[List[aRest],{i}]; sign = - sign,
	        {i, Length[{aRest}]}];
	     sum] /; (FreeQ[{aFirst,aRest},gamma5] && FreeQ[{aFirst,aRest},X] && FreeQ[{aFirst,aRest},Y])}

traceDiracRulesDdim = 
  {traceDirac[]:> 4,
   traceDirac[a__,X,b___] :> traceDirac[X,b,a],
   traceDirac[a___,gamma5,gamma5,b___] :> traceDirac[a,b],
   traceDirac[c_?((FreeQ[#,X] && FreeQ[#,Y])&)] :> 0,
   traceDirac[gamma5, nu[_]] :> 0,
   traceDirac[a__]:>0 /; (FreeQ[{a},gamma5] && FreeQ[{a},X] && FreeQ[{a},Y] && OddQ[Length[{a}]]), 
   traceDirac[gamma5,a___]:>0 /; (FreeQ[{a},gamma5] && FreeQ[{a},X] && FreeQ[{a},Y] && (Length[{a}]==2)),
   traceDirac[gamma5,a___]:>0 /; (FreeQ[{a},gamma5] && FreeQ[{a},X] && FreeQ[{a},Y] && OddQ[Length[{a}]]),
   traceDirac[gamma5,a___,gamma5,b___] :> 0 /; (FreeQ[{a,b},gamma5] && FreeQ[{a,b},X] && FreeQ[{a,b},Y] && OddQ[Length[{a,b}]]),
   traceDirac[gamma5,a___,gamma5] :> traceDirac[a],
   traceDirac[gamma5, a___, gamma5, nu[i_]] :> - traceDirac[a, nu[i]],
   traceDirac[a___, nu[i_], gamma5, b___] :> - traceDirac[a, gamma5, nu[i], b],
   traceDirac[a___, gamma5, nu[i_], gamma5, b___] :> - traceDirac[a, nu[i], b],
   traceDirac[a___, gamma5, nu[i_], nu[j_], gamma5, b___] :>  traceDirac[a,nu[i],nu[j],b],
   traceDirac[a___, rho[i_], gamma5, rho[i_], c___] :> hold[-4 + 2 e - 4 e hv] traceDirac[a, gamma5, c],
   traceDirac[a___, rho[i_], gamma5, nu[j_], rho[i_], c___] :>   hold[2 - 2 e + 4 e hv] traceDirac[a, gamma5, nu[j], c],
   traceDirac[a___, rho[i_], nu[j_], gamma5, rho[i_], c___] :> - hold[2 - 2 e + 4 e hv] traceDirac[a, gamma5, nu[j], c],
   traceDirac[a___, rho[i_], gamma5, rho[j_], gamma5, rho[i_], c___] :> hold[-2 + 2 e] traceDirac[a, gamma5, rho[j], gamma5, c],
   traceDirac[a___,b_?(FreeQ[#,gamma5]&),b_,d___]:> traceDirac[a,d] delm[b,b],
   traceDirac[a_?(FreeQ[#,gamma5]&),x___,b_?(FreeQ[#,gamma5]&),y___]:>
                   traceDirac[b,y,a,x] /; (!OrderedQ[{a,b}] && FreeQ[traceDirac[a,x,b,y],X] && FreeQ[traceDirac[a,x,b,y],Y]),
   traceDirac[gamma5,a_?(FreeQ[#,gamma5]&),x___,b_?(FreeQ[#,gamma5]&),y___]:>
                   traceDirac[b,y,gamma5,a,x] /; (!OrderedQ[{a,b}] && FreeQ[traceDirac[a,x,b,y],X] && FreeQ[traceDirac[a,x,b,y],Y]),
   traceDirac[a_,b_]:> 4 delm[a,b] /; (FreeQ[{a,b},gamma5] && FreeQ[{a,b},X] && FreeQ[{a,b},Y]),
   traceDirac[a___,b_?((FreeQ[#,gamma5] && FreeQ[#,X] && FreeQ[#,Y])&),c_?((FreeQ[#,gamma5] && FreeQ[#,X] && FreeQ[#,Y])&),d___]:>
           -traceDirac[a,c,b,d]+ 2 traceDirac[a,d] delm[b,c] /; !OrderedQ[{b,c}],
   traceDirac[a_,b_,c_,d_]:> 4 (delm[a,b] delm[c,d] - delm[a,c] delm[b,d] +
                            delm[a,d] delm[b,c]) /; (FreeQ[{a,b,c,d},gamma5] && FreeQ[{a,b,c,d},X] && FreeQ[{a,b,c,d},Y]),
   traceDirac[a_,b_,c_,d_,e_,f_] :>
      delm[a,b] traceDirac[c,d,e,f] - delm[a,c] traceDirac[b,d,e,f] +
      delm[a,d] traceDirac[b,c,e,f] - delm[a,e] traceDirac[b,c,d,f] +
      delm[a,f] traceDirac[b,c,d,e] /; (FreeQ[{a,b,c,d,e,f},gamma5] && FreeQ[{a,b,c,d,e,f},X] && FreeQ[{a,b,c,d,e,f},Y]),
   traceDirac[aFirst_,aRest__] :>
      Module[{sum = 0, sign = 1},
             Do[sum = sum + sign * delm[aFirst,List[aRest][[i]]] * traceDirac @@ Drop[List[aRest],{i}]; sign = - sign,
	        {i, Length[{aRest}]}];
	     sum] /; (FreeQ[{aFirst,aRest},gamma5] && FreeQ[{aFirst,aRest},X] && FreeQ[{aFirst,aRest},Y])}

(* A program to expand in color indices *)

colorExpand[expr_] := combineNc[combineNc[colorExpand1[expr /. f[a_,b_,c_]:> 
                                         - 2 im (traceGen[a,b,c]-traceGen[a,c,b])]] /.
                       traceGen[a_,b_,c_]:> im/4 f[a,b,c] + 1/4 d[a,b,c] ]
d[args__] := d @@ Sort[{args}] /; !OrderedQ[{args}]
f[___,a_,___,a_,___] =0; 
f[args__] := (Signature[{args}] (f @@ Sort[{args}]) /;  !OrderedQ[{args}] );

colorExpand1[expr_Plus] := colorExpand1 /@ expr

colorExpand1[expr_Times] := 
  colorExpand1[Select[expr,(!colorlessQ[#])&]] * Select[expr,colorlessQ] /;
    Or @@ (colorlessQ /@ List @@ expr)

colorExpand1[expr_Plus b_] := colorExpand1[b #]& /@ expr /; 
                           !purecolorQ[expr] && And @@ ((!colorlessQ[#])& /@ List @@ (expr b))

colorExpand1[expr_] := expr /; !MemberQ[{Times,Plus,Power},Head[expr]]

colorExpand1[expr_] := Expand[expr] /; purecolorQ[expr] 
                       
variables[expr_] := Complement[Union @@ (variables1 /@ Variables[expr]),
                               {Plus,Times, Power}]                       
variables1[expr_] := If[AtomQ[expr],
                        Variables[expr],
                        Union[Variables[Head[expr]],
                              Sequence @@ (variables1 /@ List @@ expr)]]

colorlessQ[expr_] := And @@ (FreeQ[expr,#]& /@ {delc,traceGen,productGen,f,d,Nc})

purecolorQ[expr_] := 
   Complement[variables[expr],{delc,traceGen,productGen,f,a,b,c,d,af,bf,cf,Nc}]==={}

(* combineNc[expr_] := 
                      (If[purecolorQ[#], Simplify[#], #, #] )&  //@ expr  *)

combineNc[expr_] := Factor[Simplify[expr]] /; purecolorQ[expr]
combineNc[expr_Plus] := If[purecolorQ[expr], Simplify[expr], combineNc /@ expr]
combineNc[expr_] := expr /; colorlessQ[expr]
combineNc[expr_Times] := 
  combineNc[Select[expr,(!colorlessQ[#])&]] * Select[expr,colorlessQ] /;
    Or @@ (colorlessQ /@ List @@ expr)
