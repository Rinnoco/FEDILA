s2::usage = "s2[a_,b_] = Sin[a[b]/2]"
s2[-a_,b_] := - s2[a,b]
s2[0,a_] = 0
  
c2::usage = "c2[a_,b_] = Cos[a[b]/2]"
c2[-a_,b_] := c2[a,b]
c2[0,a_] := deltaL[a,a]
  
phi2::usage = "phi2[a_,b_] = Exp[I*a[b]/2]"
phi2[0,a_] := deltaL[a,a]
phi2[a_,-b_] := phi2[-a,b]

s2overs2::usage = "s2overs2[d_,a_,b_] = Sin[d*a[b]/2] / Sin[a[b]/2]"
s2overs2[d_, -a_, b_] := s2overs2[d,a,b]

canonical::usage =
"canonical[expr_] rewrites in a canonical form all functions in 
'expr' which are manifestly odd or even, e.g. selects among 
s2[x,y] and -s2[-x,y] according to alphabetical order
                                                          " 
canonical[f_] := f /.  
   s2[x_,y_]             :> If[!OrderedQ[{Expand[x],Expand[-x]}],
                               s2[Expand[x],y],-s2[Expand[-x],y]] /.
   c2[x_,y_]             :> c2[Sort[{Expand[x],Expand[-x]}][[2]],y] /.
   S2[x_,y_]             :> If[!OrderedQ[{Expand[x],Expand[-x]}],
                               S2[Expand[x],y],-S2[Expand[-x],y]] /.
   C2[x_,y_]             :> C2[Sort[{Expand[x],Expand[-x]}][[2]],y] /.
   prop[x_,y__]          :> prop[Sort[{Expand[x],Expand[-x]}][[2]],y] /.
   dprop[x_,y__]         :> dprop[Sort[{Expand[x],Expand[-x]}][[2]],y] /.
   omegaO[x_]            :> omegaO[Sort[{Expand[x],Expand[-x]}][[2]]] /.
   omegainvO[x_]         :> omegainvO[Sort[{Expand[x],Expand[-x]}][[2]]] /.
   omegabO[x_]           :> omegabO[Sort[{Expand[x],Expand[-x]}][[2]]] /.
   omegabinvO[x_]        :> omegabinvO[Sort[{Expand[x],Expand[-x]}][[2]]] /.
   omegaplusinvO[x_,y__] :> omegaplusinvO[Sort[{Expand[x],Expand[-x]}][[2]],y] /.
   omegaplusinvO[x__,y_] :> omegaplusinvO[x,Sort[{Expand[y],Expand[-y]}][[2]]] /.
   delta[x_]             :> delta[Sort[{Expand[x],Expand[-x]}][[2]]] /.
   deltaMod2[x_]         :> deltaMod2[Sort[{Expand[x],Expand[-x]}][[2]]] /.
   hat2[x_,y___]         :> hat2[Sort[{Expand[x],Expand[-x]}][[2]],y] /.
   fhat[x_,y___]         :> fhat[Sort[{Expand[x],Expand[-x]}][[2]],y] /.
   fhatSF[x_,y___]       :> fhatSF[Sort[{Expand[x],Expand[-x]}][[2]],y] /.
   sisq[x_]              :> sisq[Sort[{Expand[x],Expand[-x]}][[2]]] /.
   s2sq[x_]              :> s2sq[Sort[{Expand[x],Expand[-x]}][[2]]] /.
   s2qu[x_]              :> s2qu[Sort[{Expand[x],Expand[-x]}][[2]]] /.
   mO[x_]                :> mO[Sort[{Expand[x],Expand[-x]}][[2]]] /.
   m[x_]                 :> m[Sort[{Expand[x],Expand[-x]}][[2]]] /.
   prod[x_]              :> If[!OrderedQ[{Expand[x],Expand[-x]}],
                               prod[Factor[Expand[x]]],-prod[Factor[Expand[-x]]]]    

hat2::usage = "hat2[p_] = 1/4 / Sum[Sin[p[i]/2]^2, {i,4}]"
hat2[-p_] := hat2[p]

fhat::usage = "fhat[p_,mass_] = 
    1 / (Sum[Sin[p[i]]^2,{i,4}] + (mass + 2r Sum[Sin[p[i]/2]^2,{i,4}])^2)
fhat[p_] = fhat[p,0] 
(r is the Wilson coefficient)"
fhat[-a_,b___] := fhat[a,b]

fhatSF[-a_,b___] := fhatSF[a,b]

m::usage = "m[p_] = mass + 2r Sum[Sin[p[i]/2]^2,{i,4}], where 'mass' refers 
to the fermion mass, whose value may be chosen at will 
(r is the Wilson coefficient)."
m[-p_] := m[p]


count::usage = "count[expr_,a_], acting on a product 'expr', counts the factors
in expr which match the pattern 'a'.
If a factor matches 'a^i', it will contribute 'i' to the total 
count.
When 'expr' is not a product, then the result will be 1, 
if 'expr' matches 'a' as a whole, else it will be 0.
                                                             "
count/: count[expr_,a_] := 
            Switch[Head[expr], Power, If[MatchQ[expr[[1]],a],expr[[2]],0],
                               Times, Plus @@ (count[#,a]& /@ (List@@expr)),
                               _,     If[MatchQ[expr,a],1,0]]

countlist::usage = "Given a list 'b' of n doublets:
(where the first member of the doublet is a pattern, 
and the second member is a score), 
countlist[a_,b_] provides a total score for product 'a', 
depending on the number of factors which match the patterns in 'b': 
countlist[a_, b_] = 
   count[a,b[[1,1]]]*b[[1,2]] + ... + count[a,b[[n,1]]*b[[n,2]]].
If b is not a list, then countlist[a_,b_] = count[a,b].
                                                               "
countlist[a_,b_]:= If[Head[b]===List,Plus @@((count[a,#[[1]]] #[[2]])& /@ b) ,count[a,b]]
             
