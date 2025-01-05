(* Can be applied to the expression as a whole, which must have Head = Plus *)

replacec2[a_Plus]:= replacec2 /@ a

(* We will omit the following, because it leads to expression which are not
   expanded, and this may lead to subsequent mistakes                       *)

(* replacec2[a_Times]:= Select[a,(FreeQ[#,c2] && FreeQ[#,rho])&] *
              replacec2[Expand[Select[a,(!(FreeQ[#,c2]&&FreeQ[#,rho]))&]]] /; 
              (Or @@ ((FreeQ[#,c2]&&FreeQ[#,rho])& /@ List @@ a))           *)

replacec2[c2[a_. q[j_],b_]^i_ c_.]:= 
     replace[c2[a q[j],b]^i c, {c2[a q[j],b]^i, c2[a q[j],b]^(i-2)}] -
      c2[a q[j],b]^(i-2) s2[q[j],b]^2 a^2 c

replacec2[c2[a_. q[j_],b_] c_.]:=
     replace[c2[a q[j],b] c, {c2[a q[j],b],1}] - (a^2)/2 s2[q[j],b]^2 c

replacec2[a_]:= a
