(* A program to simplify contractions in Lorentz indices, written in 
   term of sines and cosines                                           *) 

simplifydelm[expr_] := 
              expr  /;  FreeQ[expr,delm]

simplifydelm[expr_Plus] := 
                  simplifydelm /@ expr


simplifydelm[expr_Times] := 
    simplifydelm[Select[expr,(!FreeQ[#,rho] || !FreeQ[#,mu] || !FreeQ[#,nu])&]] *
                        Select[expr,(FreeQ[#,rho] && FreeQ[#,mu] && FreeQ[#,nu])&] /;
                              Or @@ ((FreeQ[#,rho] && FreeQ[#,mu] && FreeQ[#,nu])& /@ List @@ expr)  

simplifydelm[a_] := 
            simplifydelm1[ Expand[a] ]


simplifydelm1[a_] :=
              a  /; FreeQ[a,delm]

simplifydelm1[expr_Plus] :=
                     simplifydelm1 /@ expr

simplifydelm1[delm[a_,b__]^i_ c_. ] :=
               simplifydelm1[ delm[a,b]*c] 

simplifydelm1[delm[a_,b__,rho[i_]] c_. ] :=
               simplifydelm1[ delm[a,b] (c /. rho[i] -> a) ]  

simplifydelm1[ delm[a_,rho[i_]] b_. ] := 
   If[ TrueQ[ Head[a] == rho] && FreeQ[b,a] && FreeQ[b,rho[i]] ,
           nDim simplifydelm1[b] , simplifydelm1[b /. rho[i] -> a] ]           

simplifydelm1[ HoldPattern[delm[a___,mu[i_],mu[i_],x__]] b_. ] :=
                             simplifydelm1[ delm[a,mu[i],x] b ]

simplifydelm1[ HoldPattern[delm[a___,nu[i_],nu[i_],x__]] b_. ] :=
                             simplifydelm1[ delm[a,nu[i],x] b ]

simplifydelm1[ HoldPattern[delm[a__,mu[i_],mu[i_],x___]] b_. ] :=
                             simplifydelm1[ delm[a,mu[i],x] b ]

simplifydelm1[ HoldPattern[delm[a__,nu[i_],nu[i_],x___]] b_. ] :=
                             simplifydelm1[ delm[a,nu[i],x] b ]

simplifydelm1[ HoldPattern[delm[a___,mu[i_],x___]] HoldPattern[delm[b___,mu[i_],y___]] c___ ] :=
                              simplifydelm1[ delm[ mu[i], a, b, x, y] c ]

simplifydelm1[ HoldPattern[delm[a___,nu[i_],x___]] HoldPattern[delm[b___,nu[i_],y___]] c___ ] :=
                              simplifydelm1[ delm[ nu[i], a, b, x, y] c ]

simplifydelm1[HoldPattern[delm[a__?(FreeQ[{a},rho]&)]] b_. ] :=
	     If[ Length[Union[List[a]]] === 1 && !FreeQ[b,Union[List[a]][[1]]],
		 simplifydelm1[b] ,
		 delm[a] simplifydelm1[ 
	     b /.( (Rule[#, Sort[List[a]][[1]]] )& /@ Drop[ Sort[List[a]],1]) ]]

proprule :=
  { prop[a_,b_,c_] :> 
          hat2[a] ( delm[b,c] - 4 beta hat2[a] s2[a,b] s2[a,c] ),
    propG[a_] :> hat2[a], 
    propF[a_,b_,c_,d_] :> fhat[a] ( m[a] dtrace[c,b] - im dtrace[c,d,b] s2[2a,d])}
		      


