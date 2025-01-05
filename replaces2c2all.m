(* can be applied to the whole of an expression, whose Head must be Plus *)

replacec2all[a_Plus]:= replacec2all /@ a

replacec2all[a_]:= FixedPoint[replacec2all1,a] //. s2[b_,c_]^i_. c2[b_,c_]^j_. :> s2[b,c]^(i-1) c2[b,c]^(j-1) 1/2 s2[2b,c]

replacec2all1[a_Plus]:= replacec2all1 /@ a

replacec2all1[c2[a_,b_]^i_ c_.]:= 
  simplifydelm[Expand[c2[a,b]^(i-2) (delm[b,b] - s2[a,b]^2) c]]

replacec2all1[c2[2 a_,b_] c_.]:=
  simplifydelm[Expand[(delm[b,b] - 2 s2[a,b]^2) c]]

replacec2all1[c2[4 a_,b_] c_.]:=
     simplifydelm[Expand[(delm[b,b] - 2 s2[2a,b]^2) c]]

replacec2all1[c2[d_?((#>2)&) a_,b_] e_.] := canonical[Expand[(TrigExpand[Cos[d*a]] /. Cos[c_] :> c2[c,b] /. Sin[c_] :> s2[c,b]) e]]

replacec2all1[a_]:= a

replaces2c2all[a_Plus]:= replaces2c2all /@ a

replaces2c2all[a_]:= replacec2all[simplifydelm[replaces2c2all1[a]]]

replaces2c2all1[s2[d_?((#>1)&) a_,b_]^i_. e_.] := canonical[Expand[delm[b,b] (TrigExpand[Sin[d*a]^i] /. Cos[c_] :> c2[c,b] /. Sin[c_] :> s2[c,b]) replaces2c2all1[e]]]

replaces2c2all1[a_]:= a

