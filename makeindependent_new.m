makeindependent[x_Plus]:= makeindependent /@ x
makeindependent[x_Times]:=
  Module[{pref,rest,listpref,listrest,l,r1,r2,r3,r4,r5,l1,l2,l3,l4,l5,d,m},
(*    pref = x /. {s2[_?(FreeQ[#,q]&),_]->1, c2[_?(FreeQ[#,q]&),_]->1,dprop[_?(FreeQ[#,q]&),__]->1,prop[_?(FreeQ[#,q]&),__]->1, deriv[_?(FreeQ[#,q]&),_]->1, deriv2[_?(FreeQ[#,q]&),__]->1,propdiffperiodic[_?(FreeQ[#,q]&),__]->1,propinvdiffperiodic[_?(FreeQ[#,q]&),__]->1, dpropdiffperiodic[_?(FreeQ[#,q]&),__]->1};  *)
    pref = x /. {s2[_?(FreeQ[#,q]&),_]->1, c2[_?(FreeQ[#,q]&),_]->1,dprop[_?(FreeQ[#,q]&),__]->1,prop[_?(FreeQ[#,q]&),__]->1, deriv[_?(FreeQ[#,q]&),_]->1, deriv2[_?(FreeQ[#,q]&),__]->1,propdiffperiodic[_?(FreeQ[#,q]&),__]->1,propinvdiffperiodic[_?(FreeQ[#,q]&),__]->1, dpropdiffperiodic[_?(FreeQ[#,q]&),__]->1, effectiveVERTEX[_?(FreeQ[#,q]&),__]->1};
    rest = x / pref;
    listpref = Union[ (pref[[ Sequence @@ # ]]) & /@ Position[pref,rho[_] ], 
                      (pref[[ Sequence @@ # ]]) & /@ Position[pref,nu[_] ]];
    listrest = Union[ (rest[[ Sequence @@ # ]]) & /@ Position[rest,rho[_] ], 
                      (rest[[ Sequence @@ # ]]) & /@ Position[rest,nu[_] ]];
    l = Intersection[listpref,listrest];
    Switch[Length[l],
           0, x,
           1, pref (rest /. l[[1]]-> r1) * d[r1,r1]/4,
           2, pref (rest /. {l[[1]]->r1,l[[2]]->r2})*
              (d[l1,l2]*d[r1,r2]/4 +m[l1,l2]*m[r1,r2]/12),
           3, pref (rest /. {l[[1]]->r1,l[[2]]->r2,l[[3]]->r3})
              *( d[l1,l2,l3]*d[r1,r2,r3]/4
                +d[l1,l2]m[l1,l3]*d[r1,r2]m[r1,r3]/12
                +d[l1,l3]m[l1,l2]*d[r1,r3]m[r1,r2]/12
                +d[l2,l3]m[l1,l2]*d[r2,r3]m[r1,r2]/12
                +m[l1,l2]m[l1,l3]m[l2,l3]*m[r1,r2]m[r1,r3]m[r2,r3]/24),
           4, pref (rest /. {l[[1]]->r1,l[[2]]->r2,l[[3]]->r3,l[[4]]->r4})
	      *( d[l1,l2,l3,l4]*d[r1,r2,r3,r4]/4
	        +d[l2,l3,l4]m[l1,l2]*d[r2,r3,r4]m[r1,r2]/12
	        +d[l1,l3,l4]m[l1,l2]*d[r1,r3,r4]m[r1,r2]/12
                +d[l1,l2,l4]m[l1,l3]*d[r1,r2,r4]m[r1,r3]/12
		+d[l1,l2,l3]m[l1,l4]*d[r1,r2,r3]m[r1,r4]/12
                +d[l1,l2]d[l3,l4]m[l1,l3]*d[r1,r2]d[r3,r4]m[r1,r3]/12
	        +d[l1,l3]d[l2,l4]m[l1,l2]*d[r1,r3]d[r2,r4]m[r1,r2]/12
	        +d[l1,l4]d[l2,l3]m[l1,l2]*d[r1,r4]d[r2,r3]m[r1,r2]/12
	        +d[l1,l2]m[l1,l3]m[l1,l4]m[l3,l4]*d[r1,r2]m[r1,r3]m[r1,r4]m[r3,r4]/24
	        +d[l1,l3]m[l1,l2]m[l1,l4]m[l2,l4]*d[r1,r3]m[r1,r2]m[r1,r4]m[r2,r4]/24
	        +d[l1,l4]m[l1,l2]m[l1,l3]m[l2,l3]*d[r1,r4]m[r1,r2]m[r1,r3]m[r2,r3]/24
	        +d[l2,l3]m[l2,l1]m[l2,l4]m[l1,l4]*d[r2,r3]m[r1,r2]m[r2,r4]m[r1,r4]/24
	        +d[l2,l4]m[l2,l1]m[l2,l3]m[l1,l3]*d[r2,r4]m[r1,r2]m[r2,r3]m[r1,r3]/24
	        +d[l3,l4]m[l3,l1]m[l3,l2]m[l1,l2]*d[r3,r4]m[r1,r3]m[r2,r3]m[r1,r2]/24
                +m[l1,l2]m[l1,l3]m[l1,l4]m[l2,l3]m[l2,l4]m[l3,l4]
                          *m[r1,r2]m[r1,r3]m[r1,r4]m[r2,r3]m[r2,r4]m[r3,r4]/24),
           5, pref (rest /. {l[[1]]->r1,l[[2]]->r2,l[[3]]->r3,l[[4]]->r4,l[[5]]->r5})
	      *( d[l1,l2,l3,l4,l5]*d[r1,r2,r3,r4,r5]/4
	        +d[l2,l3,l4,l5]m[l1,l2]*d[r2,r3,r4,r5]m[r1,r2]/12
	        +d[l1,l3,l4,l5]m[l1,l2]*d[r1,r3,r4,r5]m[r1,r2]/12
	        +d[l1,l2,l4,l5]m[l1,l3]*d[r1,r2,r4,r5]m[r1,r3]/12
	        +d[l1,l2,l3,l5]m[l1,l4]*d[r1,r2,r3,r5]m[r1,r4]/12
	        +d[l1,l2,l3,l4]m[l1,l5]*d[r1,r2,r3,r4]m[r1,r5]/12
                +d[l1,l2,l3]d[l4,l5]m[l1,l4]*d[r1,r2,r3]d[r4,r5]m[r1,r4]/12
                +d[l1,l2,l4]d[l3,l5]m[l1,l3]*d[r1,r2,r4]d[r3,r5]m[r1,r3]/12
                +d[l1,l3,l4]d[l2,l5]m[l1,l2]*d[r1,r3,r4]d[r2,r5]m[r1,r2]/12
                +d[l2,l3,l4]d[l1,l5]m[l1,l2]*d[r2,r3,r4]d[r1,r5]m[r1,r2]/12
                +d[l1,l2,l5]d[l3,l4]m[l1,l3]*d[r1,r2,r5]d[r3,r4]m[r1,r3]/12
                +d[l1,l3,l5]d[l2,l4]m[l1,l2]*d[r1,r3,r5]d[r2,r4]m[r1,r2]/12
                +d[l1,l4,l5]d[l2,l3]m[l1,l2]*d[r1,r4,r5]d[r2,r3]m[r1,r2]/12
                +d[l2,l3,l5]d[l1,l4]m[l1,l2]*d[r2,r3,r5]d[r1,r4]m[r1,r2]/12
                +d[l2,l4,l5]d[l1,l3]m[l1,l2]*d[r2,r4,r5]d[r1,r3]m[r1,r2]/12
                +d[l3,l4,l5]d[l1,l2]m[l1,l3]*d[r3,r4,r5]d[r1,r2]m[r1,r3]/12
	        +d[l1,l2,l3]m[l1,l4]m[l1,l5]m[l4,l5]*d[r1,r2,r3]m[r1,r4]m[r1,r5]m[r4,r5]/24
	        +d[l1,l2,l4]m[l1,l3]m[l1,l5]m[l3,l5]*d[r1,r2,r4]m[r1,r3]m[r1,r5]m[r3,r5]/24
	        +d[l1,l2,l5]m[l1,l3]m[l1,l4]m[l3,l4]*d[r1,r2,r5]m[r1,r3]m[r1,r4]m[r3,r4]/24
	        +d[l1,l3,l4]m[l1,l2]m[l1,l5]m[l2,l5]*d[r1,r3,r4]m[r1,r2]m[r1,r5]m[r2,r5]/24
	        +d[l1,l3,l5]m[l1,l2]m[l1,l4]m[l2,l4]*d[r1,r3,r5]m[r1,r2]m[r1,r4]m[r2,r4]/24
	        +d[l1,l4,l5]m[l1,l2]m[l1,l3]m[l2,l3]*d[r1,r4,r5]m[r1,r2]m[r1,r3]m[r2,r3]/24
	        +d[l2,l3,l4]m[l1,l2]m[l2,l5]m[l1,l5]*d[r2,r3,r4]m[r1,r2]m[r2,r5]m[r1,r5]/24
	        +d[l2,l3,l5]m[l1,l2]m[l2,l4]m[l1,l4]*d[r2,r3,r5]m[r1,r2]m[r2,r4]m[r1,r4]/24
	        +d[l2,l4,l5]m[l1,l2]m[l2,l3]m[l1,l3]*d[r2,r4,r5]m[r1,r2]m[r2,r3]m[r1,r3]/24
	        +d[l3,l4,l5]m[l1,l3]m[l2,l3]m[l1,l2]*d[r3,r4,r5]m[r1,r3]m[r2,r3]m[r1,r2]/24
	        +d[l1,l2]d[l3,l4]m[l1,l3]m[l1,l5]m[l3,l5]*d[r1,r2]d[r3,r4]m[r1,r3]m[r1,r5]m[r3,r5]/24
	        +d[l1,l3]d[l2,l4]m[l1,l2]m[l1,l5]m[l2,l5]*d[r1,r3]d[r2,r4]m[r1,r2]m[r1,r5]m[r2,r5]/24
	        +d[l1,l4]d[l2,l3]m[l1,l2]m[l1,l5]m[l2,l5]*d[r1,r4]d[r2,r3]m[r1,r2]m[r1,r5]m[r2,r5]/24
	        +d[l1,l2]d[l3,l5]m[l1,l3]m[l1,l4]m[l3,l4]*d[r1,r2]d[r3,r5]m[r1,r3]m[r1,r4]m[r3,r4]/24
	        +d[l1,l3]d[l2,l5]m[l1,l2]m[l1,l4]m[l2,l4]*d[r1,r3]d[r2,r5]m[r1,r2]m[r1,r4]m[r2,r4]/24
	        +d[l1,l5]d[l2,l3]m[l1,l2]m[l1,l4]m[l2,l4]*d[r1,r5]d[r2,r3]m[r1,r2]m[r1,r4]m[r2,r4]/24
	        +d[l1,l2]d[l4,l5]m[l1,l4]m[l1,l3]m[l3,l4]*d[r1,r2]d[r4,r5]m[r1,r4]m[r1,r3]m[r3,r4]/24
	        +d[l1,l4]d[l2,l5]m[l1,l2]m[l1,l3]m[l2,l3]*d[r1,r4]d[r2,r5]m[r1,r2]m[r1,r3]m[r2,r3]/24
	        +d[l1,l5]d[l2,l4]m[l1,l2]m[l1,l3]m[l2,l3]*d[r1,r5]d[r2,r4]m[r1,r2]m[r1,r3]m[r2,r3]/24
	        +d[l1,l3]d[l4,l5]m[l1,l4]m[l1,l2]m[l2,l4]*d[r1,r3]d[r4,r5]m[r1,r4]m[r1,r2]m[r2,r4]/24
	        +d[l1,l4]d[l3,l5]m[l1,l3]m[l1,l2]m[l2,l3]*d[r1,r4]d[r3,r5]m[r1,r3]m[r1,r2]m[r2,r3]/24
	        +d[l1,l5]d[l3,l4]m[l1,l3]m[l1,l2]m[l2,l3]*d[r1,r5]d[r3,r4]m[r1,r3]m[r1,r2]m[r2,r3]/24
	        +d[l2,l3]d[l4,l5]m[l2,l4]m[l1,l2]m[l1,l4]*d[r2,r3]d[r4,r5]m[r2,r4]m[r1,r2]m[r1,r4]/24
	        +d[l2,l4]d[l3,l5]m[l2,l3]m[l1,l2]m[l1,l3]*d[r2,r4]d[r3,r5]m[r2,r3]m[r1,r2]m[r1,r3]/24
	        +d[l2,l5]d[l3,l4]m[l2,l3]m[l1,l2]m[l1,l3]*d[r2,r5]d[r3,r4]m[r2,r3]m[r1,r2]m[r1,r3]/24
	        +d[l1,l2]m[l1,l3]m[l1,l4]m[l1,l5]m[l3,l4]m[l3,l5]m[l4,l5]*
	                 d[r1,r2]m[r1,r3]m[r1,r4]m[r1,r5]m[r3,r4]m[r3,r5]m[r4,r5]/24
	        +d[l1,l3]m[l1,l2]m[l1,l4]m[l1,l5]m[l2,l4]m[l2,l5]m[l4,l5]*
	                 d[r1,r3]m[r1,r2]m[r1,r4]m[r1,r5]m[r2,r4]m[r2,r5]m[r4,r5]/24
	        +d[l1,l4]m[l1,l2]m[l1,l3]m[l1,l5]m[l2,l3]m[l2,l5]m[l3,l5]*
	                 d[r1,r4]m[r1,r2]m[r1,r3]m[r1,r5]m[r2,r3]m[r2,r5]m[r3,r5]/24
	        +d[l1,l5]m[l1,l2]m[l1,l3]m[l1,l4]m[l2,l3]m[l2,l4]m[l3,l4]*
	                 d[r1,r5]m[r1,r2]m[r1,r3]m[r1,r4]m[r2,r3]m[r2,r4]m[r3,r4]/24
	        +d[l2,l3]m[l1,l2]m[l1,l4]m[l1,l5]m[l2,l4]m[l2,l5]m[l4,l5]*
	                 d[r2,r3]m[r1,r2]m[r1,r4]m[r1,r5]m[r2,r4]m[r2,r5]m[r4,r5]/24
	        +d[l2,l4]m[l1,l2]m[l1,l3]m[l1,l5]m[l2,l3]m[l2,l5]m[l3,l5]*
	                 d[r2,r4]m[r1,r2]m[r1,r3]m[r1,r5]m[r2,r3]m[r2,r5]m[r3,r5]/24
	        +d[l2,l5]m[l1,l2]m[l1,l3]m[l1,l4]m[l2,l3]m[l2,l4]m[l3,l4]*
	                 d[r2,r5]m[r1,r2]m[r1,r3]m[r1,r4]m[r2,r3]m[r2,r4]m[r3,r4]/24
	        +d[l3,l4]m[l1,l2]m[l1,l3]m[l1,l5]m[l2,l3]m[l2,l5]m[l3,l5]*
	                 d[r3,r4]m[r1,r2]m[r1,r3]m[r1,r5]m[r2,r3]m[r2,r5]m[r3,r5]/24
	        +d[l3,l5]m[l1,l2]m[l1,l3]m[l1,l4]m[l2,l3]m[l2,l4]m[l3,l4]*
	                 d[r3,r5]m[r1,r2]m[r1,r3]m[r1,r4]m[r2,r3]m[r2,r4]m[r3,r4]/24
	        +d[l4,l5]m[l1,l2]m[l1,l3]m[l1,l4]m[l2,l3]m[l2,l4]m[l3,l4]*
	                 d[r4,r5]m[r1,r2]m[r1,r3]m[r1,r4]m[r2,r3]m[r2,r4]m[r3,r4]/24),
           _, Print["Complicated term: ", x]; x]
(*     /. m[a__] :> 1-d[a] /. {l1->l[[1]],l2->l[[2]],l3->l[[3]],l4->l[[4]],l5->l[[5]]}  *)
       /. m[a__] :> 1-d[a] /. Table[{l1,l2,l3,l4,l5}[[i]] -> l[[i]],{i,Length[l]}]
       /. {d->delm,r1->rho[21],r2->rho[22],r3->rho[23],r4->rho[24],r5->rho[25]}]
