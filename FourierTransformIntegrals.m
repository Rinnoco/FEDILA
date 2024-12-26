(* In this program we calculate one-loop integrals of the following form:
   exp[im z p]/(p^2)^a * (p_{mu_1}*....*p_{mu_n}) or
   exp[im z p]/(p^2)^a1/((-p[1]+q[1])^2)^a2 * (p_{mu_1}*....*p_{mu_n}). *)

derivzrules =
{deriv[a_ b_, z,mu_] :> deriv[a,z,mu] b + deriv[b,z,mu] a,
deriv[a_^i_,z,mu_] :> i a^(i-1) deriv[a,z,mu],
deriv[a_ + b_, z,mu_] :> deriv[a,z,mu] + deriv[b,z,mu],
deriv[a_?((FreeQ[#,zsq] && FreeQ[#,z])&),z,mu_] :>0,
deriv[BesselK[nu_,Sqrt[q2 zsq oneminusx x]],z,mu_]:> -1/2*(BesselK[-1+nu,Sqrt[q2 zsq oneminusx x]] + BesselK[1+nu,Sqrt[q2 zsq oneminusx x]])*Sqrt[q2 oneminusx x]/Sqrt[zsq]*s2[2 z,mu],
deriv[exp[im q[1] z x],z,mu_] :> exp[im q[1] z x] im x s2[2 q[1],mu],
deriv[zsq, z, mu_] :> 2 s2[2 z,mu],
deriv[s2[2 z,nu_],z,mu_] :> delm[nu,mu]}

FourierTransformIntegral[expr_Plus]:= FourierTransformIntegral /@ expr

FourierTransformIntegral[expr_Times]:=
Select[expr,FreeQ[#,p[1]]&]*FourierTransformIntegral1[Select[expr,!FreeQ[#,p[1]]&]]

FourierTransformIntegral1[a_. exp[im z1_ p[1]] hat2[p[1]]^i_. hat2[-p[1]+q[1]]^j_.] :=
Fold[(-im*deriv[#1,z,#2])&,
2^(1-i-j-nDim/2) q2^(-i/2-j/2+nDim/4) zsq^(i/2+j/2-nDim/4)/Pi^(nDim/2)/Gamma[i]/Gamma[j]*int[x,0,1]*exp[im q[1] z x] BesselK[-i-j+nDim/2,Sqrt[q2 zsq oneminusx x]] x^(-1-i/2+j/2+nDim/4) oneminusx^(-1+i/2-j/2+nDim/4),
Flatten[(List @@ (a*Nothing)) /. Power -> Table /. Nothing -> {1}] /. s2[2 p[1],b_] :> b /. {1} -> {}] //. derivzrules /. zsq -> sisq[z] /. z -> z1 /. b_.*nDim + c_ :> hold[b*nDim+c] /. b_^hold[c_] :> b^c


FourierTransformIntegral1[a_. exp[im z1_ p[1]] hat2[p[1]]^i_.] :=
(Fold[(-im*deriv[#1,z,#2])&,
Gamma[-i+nDim/2]*zsq^(i - nDim/2)/4^i/Pi^(nDim/2)/Gamma[i],
Flatten[(List @@ (a*Nothing)) /. Power -> Table /. Nothing -> {1}] /. s2[2 p[1],b_] :> b /. {1} -> {}] //. derivzrules /. zsq -> sisq[z] /. z -> z1 /. b_.*nDim + c_ :> hold[b*nDim+c] /. b_^hold[c_] :> b^c /. Gamma[hold[b_]] :> Gamma[b]) /; FreeQ[a,hat2[-p[1]+q[1]]]

FourierTransformIntegral1[a_] := a 
