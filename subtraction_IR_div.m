subtractionIRdiv[expr_Plus,n_] := subtractionIRdiv[#,n]& /@ expr

subtractionIRdiv[expr_,n_] := If[countlist[expr,powerlistq]>n,0,(expr /. flag -> 1 /. flag2 -> 1)] /; (countlist[expr,powerlistall] > (-4+n))

subtractionIRdiv[expr_,n_] :=
	   Module[{denominator,expr1,rule},
	         denominator = expr / (expr /. fhat[__]->1 /. hat2[_] -> 1 /. prop[__] -> 1);
		 rule= Switch[denominator,
	                      prop[p[a_] + b_. q[r_],c_,d_]^i_. hat2[p[a_]]^j_., denominator /. prop[p[a_] + b_. q[r_],c_,d_]^i_. hat2[p[a_]]^j_. :> Rule[p[a],-p[a] - b q[r]],
			      prop[p[a_] + b_. q[r_],c_,d_]^i_.,denominator /. prop[p[a_] + b_. q[r_],c_,d_]^i_. :> Rule[p[a],-p[a] - b q[r]],
			      fhat[p[a_] + b_. q[r_]]^i_. hat2[p[a_]]^j_.,denominator /. fhat[p[a_] + b_. q[r_]]^i_. hat2[p[a_]]^j_. :> Rule[p[a],-p[a] - b q[r]],
			      fhat[p[a_] + b_. q[r_]]^i_.,denominator /. fhat[p[a_] + b_. q[r_]]^i_. :> Rule[p[a],-p[a] - b q[r]],
			      hat2[p[a_] + b_. q[r_]]^i_ hat2[p[a_]],denominator /. hat2[p[a_] + b_. q[r_]]^i_ hat2[p[a_]] :> Rule[p[a],-p[a] - b q[r]],
			      hat2[p[a_] + b_. q[r_]]^i_.,denominator /. hat2[p[a_] + b_. q[r_]]^i_. :> Rule[p[a],-p[a] - b q[r]],
			      _, {}];
		  expr1 = canonical[expr /. rule];
		  Which[!((expr1 /. fhat[a_ + b_. q[i_]] :> 0 /. prop[a_ + b_. q[i_],c_,d_] :> 0 /. hat2[a_ + b_. q[i_]] :> 0)===0),(expr1 /. flag -> 1 /. flag2 -> 1),
		  	((expr1 /. fhat[a_ + b_. q[i_]] :> 0)===0) || ((expr1 /. fhat[a_] hat2[a_ + b_. q[i_]]^j_ :> 0) === 0) ,subtractionIRdiv6[expr1,n],
			((expr1 /. prop[a_ + b_. q[i_],c_,d_] :> 0)===0) || ((expr1 /. prop[a_,c_,d_] hat2[a_ + b_. q[i_]]^j_ :> 0) === 0),subtractionIRdiv7[expr1,n],
			(expr1 /. sisq[a_] :> 0) === 0,subtractionIRdiv1[expr1,n],
			((expr1 /. s2qu[a_ + b_. q[i_]] :> 0) === 0),subtractionIRdiv2[expr1,n],
			((expr1 /. s2sq[a_ + b_. q[i_]] :> 0) === 0),subtractionIRdiv3[expr1,n],
			((expr1 /. c2[a_ + b_. q[i_],c_] :> 0) === 0) || ((expr1 /. c2[a_,c_]^j_ :> 0) === 0) || ((expr1 /. c2[a_ b_,c_] :> 0) === 0),subtractionIRdiv4[expr1,n],
			((expr1 /. s2[a_ + b_. q[i_],c_] :> 0) === 0) && !((expr1 /. flag2 -> 0) === 0),subtractionIRdiv5[expr1,n],
			(expr1 /. fhat[a_] :> 0)===0,subtractionIRdiv6[expr1,n],
			(expr1 /. prop[a_,c_,d_] :> 0)===0,subtractionIRdiv7[expr1,n],
			True,(expr1 /. flag -> 1 /. flag2 -> 1)*div]]

subtractionIRdiv1[expr_,n_] := 
	 Module[{expr1},
	        expr1 = (expr //. sisq[a_]^i_. :> sisq[a]^(i-1) (4 s2sq[a] - 4 s2qu[a])) // Expand;
		expr1 = expr1 //. s2sq[a_]^i_. hat2[a_]^j_. :> 1/4 s2sq[a]^(i-1) hat2[a]^(j-1);
		subtractionIRdiv[expr1,n]]

subtractionIRdiv2[expr_,n_] := 
	 Module[{expr1},
		expr1 = expr /. e_. s2qu[a_ + b_. q[i_]]^j_. :> e s2qu[a+b q[i]]^(j-1) (s2qu[a] + s2[b q[i],rho[20]] s2[2a + b q[i],rho[20]] (s2[a+b q[i],rho[20]]^2 + s2[a,rho[20]]^2));
		expr1 = expr1 // Expand // reducerho // rorder;
		subtractionIRdiv[expr1,n]]

subtractionIRdiv3[expr_,n_] := 
	 Module[{expr1},
		expr1 = expr /. e_. s2sq[a_ + b_. q[i_]]^j_. :> e s2sq[a+b q[i]]^(j-1) (s2sq[a] + s2[b q[i],rho[20]] s2[2a + b q[i],rho[20]]);
		expr1 = expr1 // Expand // reducerho // rorder;
		expr1 = expr1 //. s2sq[a_]^i_. hat2[a_]^j_. :> 1/4 s2sq[a]^(i-1) hat2[a]^(j-1);
		subtractionIRdiv[expr1,n]]
					
subtractionIRdiv4[expr_,n_] := 
	 Module[{expr1},
		expr1 = (expr /. e_. c2[a_ + b_. q[i_],c_]^j_.:> e c2[a+b q[i],c]^(j-1) (c2[a,c] c2[b q[i],c] - s2[a,c] s2[b q[i],c])) // Expand // canonical;
		expr1 = replacec2all[expr1];
		expr1 = FixedPoint[replacec2exact,expr1];
	        expr1 = (expr1 // reducerho // rorder) /. nDim -> 4;
		expr1 = makes2sq[expr1] // reducerho // rorder;
	        expr1 = (expr1 //. sisq[a_]^i_. :> sisq[a]^(i-1) (4 s2sq[a] - 4 s2qu[a])) // Expand;
	        expr1 = expr1 //. s2sq[a_]^i_. hat2[a_]^j_. :> 1/4 s2sq[a]^(i-1) hat2[a]^(j-1);
	        expr1 = expr1 //. s2[a_,b_]^i_. c2[a_,b_]^j_. :> s2[a,b]^(i-1) c2[a,b]^(j-1) 1/2 s2[2a,b];
		subtractionIRdiv[expr1,n]]

subtractionIRdiv5[expr_,n_] := 
	 Module[{expr1},
		expr1 = Switch[expr,
		e_. s2[a_ + b_. q[i_],c_]^j_,expr /. e_. s2[a_ + b_. q[i_],c_]^j_ :> e s2[a+b q[i],c]^(j-1) (s2[a,c] c2[b q[i],c] + c2[a,c] s2[b q[i],c]),
		b_. hat2[p[i_] + q[j_]]^2 s2[2p[i_] + 2q[j_],a_] s2[c_ + d_. q[k_],e_], expr /. b_. hat2[p[i_] + q[j_]]^2 s2[2p[i_] + 2q[j_],a_] s2[c_ + d_. q[k_],e_] :> b hat2[p[i]+q[j]]^2 s2[2p[i] + 2q[j],a] (s2[c,e] c2[d q[k],e] + c2[c,e] s2[d q[k],e]),
		b_. hat2[p[i_] + q[j_]]^2 s2[p[i_] + q[j_],a_] s2[c_ + d_. q[k_],e_], expr /. b_. hat2[p[i_] + q[j_]]^2 s2[p[i_] + q[j_],a_] s2[c_ + d_. q[k_],e_] :> b hat2[p[i]+q[j]]^2 s2[p[i] + q[j],a] (s2[c,e] c2[d q[k],e] + c2[c,e] s2[d q[k],e]),
		b_. hat2[p[i_] + q[j_]]^2 s2[2p[i_] + 2q[j_],a_],expr*flag2,
		b_. hat2[p[i_] + q[j_]]^2 s2[p[i_] + q[j_],a_],expr*flag2,
		_,expr /. e_. s2[a_ + b_. q[i_],c_] :> e (s2[a,c] c2[b q[i],c] + c2[a,c] s2[b q[i],c])];
		expr1 = expr1 // Expand // canonical;
		expr1 = replaces2c2all[expr1];
		expr1 = FixedPoint[replacec2exact,expr1];
	        expr1 = (expr1 // reducerho // rorder) /. nDim -> 4;
		expr1 = makes2sq[expr1] // reducerho // rorder;
	        expr1 = (expr1 //. sisq[a_]^i_. :> sisq[a]^(i-1) (4 s2sq[a] - 4 s2qu[a])) // Expand;
	        expr1 = expr1 //. s2sq[a_]^i_. hat2[a_]^j_. :> 1/4 s2sq[a]^(i-1) hat2[a]^(j-1);
	        expr1 = expr1 //. s2[a_,b_]^i_. c2[a_,b_]^j_. :> s2[a,b]^(i-1) c2[a,b]^(j-1) 1/2 s2[2a,b];
		subtractionIRdiv[expr1,n]]

subtractionIRdiv6[expr_,n_] :=
            Module[{expr1},
	           expr1 = expr /. fhat[p[i_]]:> hat2[p[i]] + fhat[p[i]] hat2[p[i]] (4 s2qu[p[i]] - 4 s2sq[p[i]]^2);
		   expr1 = Expand[expr1];
		   expr1 = expr1 //. s2sq[a_]^i_. hat2[a_]^j_. :> 1/4 s2sq[a]^(i-1) hat2[a]^(j-1);
		   subtractionIRdiv[expr1,n]]

subtractionIRdiv7[expr_,n_] :=
            Module[{expr1,jmax},
	           If[(expr /. flag -> 0) ===0,subtractionIRdiv8[expr,n],
		   expr1 = expr;
	           jmax = Length[Union[rhos[expr1]]];
                   Do[If[MatchQ[Select[expr1,(!FreeQ[#,rho[j]])&],s2[a_,c_]*prop[a_,b___,c_,d___]?((!SameQ[#[[2]],#[[3]]])&)],
	     	         expr1 = Select[expr1,(FreeQ[#,rho[j]])&]*(Select[expr1,(!FreeQ[#,rho[j]])&] /. s2[a_,c_] prop[a_,b___,c_,d___] :> hat2[a] s2[a,b,d])],
	              {j,jmax}];
	           expr1 = expr1 // reducerho // rorder;
		   expr1 = expr1 //. s2sq[a_]^i_. hat2[a_]^j_. :> 1/4 s2sq[a]^(i-1) hat2[a]^(j-1);
		   expr1 = expr1 //. s2[a_,b_]^i_. c2[a_,b_]^j_. :> s2[a,b]^(i-1) c2[a,b]^(j-1) 1/2 s2[2a,b];
		   subtractionIRdiv[expr1*flag,n]]]

subtractionIRdiv8[expr_,n_] :=
            Module[{expr1},
	           expr1 = expr /. prop[p[i_],b_,c_]:> dprop[p[i],b,c] + delm[b,c] hat2[p[i]];
		   expr1 = Expand[expr1];
		   expr1 = expr1 // simplifydelm // reducerho // rorder;
		   expr1 = (expr1 // makes2sq // reducerho // rorder) /. nDim -> 4;
		   expr1 = (expr1 //. sisq[a_]^i_. :> sisq[a]^(i-1) (4 s2sq[a] - 4 s2qu[a])) // Expand;
		   expr1 = expr1 //. s2sq[a_]^i_. hat2[a_]^j_. :> 1/4 s2sq[a]^(i-1) hat2[a]^(j-1);
		   expr1 = expr1 //. s2[a_,b_]^i_. c2[a_,b_]^j_. :> s2[a,b]^(i-1) c2[a,b]^(j-1) 1/2 s2[2a,b];
		   subtractionIRdiv[expr1,n]]

					 
powerlistall = {{s2[_,_],1},{prop[__],-2},{hat2[__],-2},{fhat[__],-2},{s2sq[_],2},{sisq[_],2},{s2qu[_],4}}
powerlistq = {{s2[a_. q[i_],_],1},{s2sq[q[i_]],2},{sisq[q[i_]],2},{s2qu[q[i_]],4}}
