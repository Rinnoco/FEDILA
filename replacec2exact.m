(* Can be applied to the expression as a whole, which must have Head = Plus *)

replacec2exact[a_Plus]:= replacec2exact /@ a

(* We will omit the following, because it leads to expression which are not
   expanded, and this may lead to subsequent mistakes                       *)

(* replacec2exact[a_Times]:= Select[a,(FreeQ[#,c2] && FreeQ[#,rho])&] *
              replacec2exact[Expand[Select[a,(!(FreeQ[#,c2]&&FreeQ[#,rho]))&]]] /; 
              (Or @@ ((FreeQ[#,c2]&&FreeQ[#,rho])& /@ List @@ a))           *)

replacec2exact[c2[a_. q[j_],b_]^i_ c_.]:= 
     replace[c2[a q[j],b]^i c, {c2[a q[j],b]^i, c2[a q[j],b]^(i-2)}] -
      c2[a q[j],b]^(i-2) s2[a q[j],b]^2 c

replacec2exact[c2[a_. q[j_],b_] c_.]:=
     replace[c2[a q[j],b] c, {c2[a q[j],b],1}] - 2 s2[a q[j]/2,b]^2 c

replacec2exact[a_]:= a
