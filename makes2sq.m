(* This command takes a typical integrand: prefactor * (sum of terms)
   and substitutes, wherever legitimate, s2[a_,rho[_]]^2 by s2sq[a],
   s2[2a_,rho[_]]^2 by sisq[a] and s2[a_,rho[_]]^4 by s2qu[a].
   This reduces the number of rho indices, thus moderating the increase
   in the size of the expression once the rho's are made to be different.

   The propagator momenta must be p[1],p[2],p[3],p[1]+p[2],p[1]+p[3],p[3]-p[2]
   in order for this command to make the maximum amount of substitutions.      *)

(* To use it, one simply says (BEFORE rendering rho's different):
   out27 = ...
   makes2sq[out27];
   reducerho[%];
   rorder[%];
   ...NOW one may proceed to render rho's different                    *)


makes2sq[expr_Plus] := makes2sq /@ expr
   
makes2sq[expr_Times]:= 
  Block[{prefactor, rest, lastrho},
        prefactor = Select[expr,(FreeQ[#,rho])&];
(* This previous version leads to WRONG results in certain cases.
       prefactor = Select[expr,(FreeQ[#,r]&&FreeQ[#,s2]&&FreeQ[#,c2]&&
                                FreeQ[#,s2sq]&&FreeQ[#,sisq]&&FreeQ[#,s2qu])&]; *)
        rest = Expand[expr/prefactor];
        lastrho = 1; 
        While[!FreeQ[expr,rho[lastrho+1]], lastrho += 1];
        If[Head[rest] === Plus,
           Do[rest = Sum[If[Head[rest[[i]]] === Times,
                            Select[rest[[i]], FreeQ[#,rho[j]]&] *
                               Switch[Select[rest[[i]], (!FreeQ[#,rho[j]])&],
                                      s2[p[1],rho[j]]^2, s2sq[p[1]],
                                      s2[p[2],rho[j]]^2, s2sq[p[2]],
                                      s2[p[3],rho[j]]^2, s2sq[p[3]],
                                      s2[p[1]+p[2],rho[j]]^2, s2sq[p[1]+p[2]],
                                      s2[p[1]+p[3],rho[j]]^2, s2sq[p[1]+p[3]],
                                      s2[p[3]-p[2],rho[j]]^2, s2sq[p[3]-p[2]],
                                      s2[2p[1],rho[j]]^2, sisq[p[1]],
                                      s2[2p[2],rho[j]]^2, sisq[p[2]],
                                      s2[2p[3],rho[j]]^2, sisq[p[3]],
                                      s2[2p[1]+2p[2],rho[j]]^2, sisq[p[1]+p[2]],
                                      s2[2p[1]+2p[3],rho[j]]^2, sisq[p[1]+p[3]],
                                      s2[2p[3]-2p[2],rho[j]]^2, sisq[p[3]-p[2]],
                                      s2[p[1],rho[j]]^4, s2qu[p[1]],
                                      s2[p[2],rho[j]]^4, s2qu[p[2]],
                                      s2[p[3],rho[j]]^4, s2qu[p[3]],
                                      s2[p[1]+p[2],rho[j]]^4, s2qu[p[1]+p[2]],
                                      s2[p[1]+p[3],rho[j]]^4, s2qu[p[1]+p[3]],
                                      s2[p[3]-p[2],rho[j]]^4, s2qu[p[3]-p[2]],
                                      _, Select[rest[[i]], (!FreeQ[#,rho[j]])&]],
                            Switch[rest[[i]],
                                   s2[p[1],rho[j]]^2, s2sq[p[1]],
                                   s2[p[2],rho[j]]^2, s2sq[p[2]],
                                   s2[p[3],rho[j]]^2, s2sq[p[3]],
                                   s2[p[1]+p[2],rho[j]]^2, s2sq[p[1]+p[2]],
                                   s2[p[1]+p[3],rho[j]]^2, s2sq[p[1]+p[3]],
                                   s2[p[3]-p[2],rho[j]]^2, s2sq[p[3]-p[2]],
                                   s2[2p[1],rho[j]]^2, sisq[p[1]],
                                   s2[2p[2],rho[j]]^2, sisq[p[2]],
                                   s2[2p[3],rho[j]]^2, sisq[p[3]],
                                   s2[2p[1]+2p[2],rho[j]]^2, sisq[p[1]+p[2]],
                                   s2[2p[1]+2p[3],rho[j]]^2, sisq[p[1]+p[3]],
                                   s2[2p[3]-2p[2],rho[j]]^2, sisq[p[3]-p[2]],
                                   s2[p[1],rho[j]]^4, s2qu[p[1]],
                                   s2[p[2],rho[j]]^4, s2qu[p[2]],
                                   s2[p[3],rho[j]]^4, s2qu[p[3]],
                                   s2[p[1]+p[2],rho[j]]^4, s2qu[p[1]+p[2]],
                                   s2[p[1]+p[3],rho[j]]^4, s2qu[p[1]+p[3]],
                                   s2[p[3]-p[2],rho[j]]^4, s2qu[p[3]-p[2]],
                                   _, rest[[i]]]],
                         {i, Length[rest]}],
              {j,lastrho}],
           Do[rest = If[Head[rest] === Times,
                        Select[rest, FreeQ[#,rho[j]]&] *
                           Switch[Select[rest, (!FreeQ[#,rho[j]])&],
                                  s2[p[1],rho[j]]^2, s2sq[p[1]],
                                  s2[p[2],rho[j]]^2, s2sq[p[2]],
                                  s2[p[3],rho[j]]^2, s2sq[p[3]],
                                  s2[p[1]+p[2],rho[j]]^2, s2sq[p[1]+p[2]],
                                  s2[p[1]+p[3],rho[j]]^2, s2sq[p[1]+p[3]],
                                  s2[p[3]-p[2],rho[j]]^2, s2sq[p[3]-p[2]],
                                  s2[2p[1],rho[j]]^2, sisq[p[1]],
                                  s2[2p[2],rho[j]]^2, sisq[p[2]],
                                  s2[2p[3],rho[j]]^2, sisq[p[3]],
                                  s2[2p[1]+2p[2],rho[j]]^2, sisq[p[1]+p[2]],
                                  s2[2p[1]+2p[3],rho[j]]^2, sisq[p[1]+p[3]],
                                  s2[2p[3]-2p[2],rho[j]]^2, sisq[p[3]-p[2]],
                                  s2[p[1],rho[j]]^4, s2qu[p[1]],
                                  s2[p[2],rho[j]]^4, s2qu[p[2]],
                                  s2[p[3],rho[j]]^4, s2qu[p[3]],
                                  s2[p[1]+p[2],rho[j]]^4, s2qu[p[1]+p[2]],
                                  s2[p[1]+p[3],rho[j]]^4, s2qu[p[1]+p[3]],
                                  s2[p[3]-p[2],rho[j]]^4, s2qu[p[3]-p[2]],
                                  _, Select[rest, (!FreeQ[#,rho[j]])&]],
                        Switch[rest,
                               s2[p[1],rho[j]]^2, s2sq[p[1]],
                               s2[p[2],rho[j]]^2, s2sq[p[2]],
                               s2[p[3],rho[j]]^2, s2sq[p[3]],
                               s2[p[1]+p[2],rho[j]]^2, s2sq[p[1]+p[2]],
                               s2[p[1]+p[3],rho[j]]^2, s2sq[p[1]+p[3]],
                               s2[p[3]-p[2],rho[j]]^2, s2sq[p[3]-p[2]],
                               s2[2p[1],rho[j]]^2, sisq[p[1]],
                               s2[2p[2],rho[j]]^2, sisq[p[2]],
                               s2[2p[3],rho[j]]^2, sisq[p[3]],
                               s2[2p[1]+2p[2],rho[j]]^2, sisq[p[1]+p[2]],
                               s2[2p[1]+2p[3],rho[j]]^2, sisq[p[1]+p[3]],
                               s2[2p[3]-2p[2],rho[j]]^2, sisq[p[3]-p[2]],
                               s2[p[1],rho[j]]^4, s2qu[p[1]],
                               s2[p[2],rho[j]]^4, s2qu[p[2]],
                               s2[p[3],rho[j]]^4, s2qu[p[3]],
                               s2[p[1]+p[2],rho[j]]^4, s2qu[p[1]+p[2]],
                               s2[p[1]+p[3],rho[j]]^4, s2qu[p[1]+p[3]],
                               s2[p[3]-p[2],rho[j]]^4, s2qu[p[3]-p[2]],
                               _, rest]],
              {j,lastrho}]];
        prefactor * rest]


makes2sq[expr_] := expr
