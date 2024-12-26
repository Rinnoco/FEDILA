canonical[f_] := f /.  
   s2[x_,y_]             :> If[!OrderedQ[{Expand[x],Expand[-x]}],
                               s2[Expand[x],y],
                               -s2[Expand[-x],y]] /.
   prod[x_,y_]           :> If[!OrderedQ[{Expand[x],Expand[-x]}],
                               prod[Expand[x],y],
			       -prod[Expand[-x],y]] /.
   prod[x_,y_]           :> If[!OrderedQ[{Expand[y],Expand[-y]}],
                               prod[x,Expand[y]],
			       -prod[x,Expand[-y]]] /.  
   slash[x_]             :> If[!OrderedQ[{Expand[x],Expand[-x]}],
                               slash[Expand[x]],
                               -slash[Expand[-x]]] /.
   prop[x_,y__]          :> prop[Sort[{Expand[x],Expand[-x]}][[2]],y] /.
   delta[x_]             :> delta[Sort[{Expand[x],Expand[-x]}][[2]]] /.
   hat2[x_,y___]         :> hat2[Sort[{Expand[x],Expand[-x]}][[2]],y] /.
   sisq[x_]              :> sisq[Sort[{Expand[x],Expand[-x]}][[2]]] /.
  dtrace[a__,-slash[b_],c__] :> -dtrace[a,slash[b],c] /.
  gtrace[a__,-slash[b_],c__] :> -gtrace[a,slash[b],c]
  
s2[-a_,b_] := - s2[a,b]
s2[0,a_] = 0
sisq[-a_] := sisq[a]
sisq[0] = 0
exp[0] = 1
hat2[-a_] := hat2[a]
prop[a_, b__] := prop[a, Sequence @@ Sort[{b}]] /;  !OrderedQ[{b}]
slash[0] = 0
dtrace[a__,0,b__] := 0
gtrace[a___,0,b___] := 0
prod[0,b_] := 0
prod[a_,0] := 0

count/: count[expr_,a_] := 
            Switch[Head[expr], Power, If[MatchQ[expr[[1]],a],expr[[2]],0],
                               Times, Plus @@ (count[#,a]& /@ (List@@expr)),
                               _,     If[MatchQ[expr,a],1,0]]

countlist[a_,b_]:= If[Head[b]===List,Plus @@((count[a,#[[1]]] #[[2]])& /@ b) ,count[a,b]]
