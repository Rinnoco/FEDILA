(* can be applied to the whole of an expression, whose Head must be Plus *)

replacec2p[a_Plus]:= replacec2p /@ a

replacec2p[c2[a_,b_]^i_ c_.]:= 
     replace[c2[a,b]^i c, {c2[a,b]^i, c2[a,b]^(i-2)}] -
      c2[a,b]^(i-2) s2[a,b]^2 c

replacec2p[c2[2 a_,b_] c_.]:=
     replace[c2[2a,b] c, {c2[2a,b],1}] - 2 canonical[s2[a,b]]^2 c

replacec2p[c2[4 a_,b_] c_.]:=
     replace[c2[4a,b] c, {c2[4a,b],1}] - 2 canonical[s2[2a,b]]^2 c

replacec2p[a_]:= a
