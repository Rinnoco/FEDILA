symmetrizeauto[ vertice_, min_, max_] := vertice /; 
                                       !(OddQ[max-min] && max-min > 0)
symmetrizeauto[ vertice_, min_, max_] := vertice /; min+1==max
symmetrizeauto[ vertice_, min_, max_] := 
  symmetrizeauto[vertice + Sum[vertice  /. {k[max-1] -> k[ij], k[ij] -> k[max-1], 
                                            mu[max-1] -> mu[ij], mu[ij] -> mu[max-1],
                                            c[max-1] -> c[ij], c[ij] -> c[max-1]},
                               {ij, min, max-2} ], 
                 min, max-2 ]  / (max-min)


symmetrize[ vertice_, min_, max_] := vertice /; min>=max
symmetrize[ vertice_, min_, max_] := 
  symmetrize[vertice + Sum[vertice  /. {k[max] -> k[ij],  k[ij] -> k[max], 
                                        mu[max]-> mu[ij], mu[ij]-> mu[max],
                                        c[max] -> c[ij],  c[ij] -> c[max],
					cf[max] -> cf[ij],cf[ij]-> cf[max]},
                           {ij, min, max-1} ], 
             min, max-1 ]  / (max-min+1)

symmetrizepartially[ vertice_, listagruppi_ ]:=
     symmetrizepartially[ vertice, listagruppi, 0]
symmetrizepartially[ vertice_, listagruppi_, offset_]:= 
     vertice /;                                        Length[listagruppi] == 1

symmetrizepartially[ vertice_, listagruppi_, offset_] := 
     symmetrizepartially[ vertice, Drop[ listagruppi, -1], offset] /;
                                                        Last[listagruppi ] == 0

symmetrizepartially[ vertice_, listagruppi_, offset_] := 
     symmetrizepartially[ symmetrizepartially1[ vertice, 
                                                Plus@@listagruppi, 
                                                Plus@@listagruppi,
                                                Last[listagruppi], offset],
                          Drop[ listagruppi, -1], offset] /
     Binomial[ Plus@@listagruppi, Last[listagruppi] ]



symmetrizepartially1[ vertice_, maxvalue_, lastindex_, 0 , offset_] := vertice

symmetrizepartially1[ vertice_, maxvalue_, lastindex_, indexnumber_, offset_] :=
  Plus@@Array[
    (symmetrizepartially1[
       vertice /. {k[offset+lastindex] -> k[offset+#+indexnumber-1],
                   k[offset+#+indexnumber-1] -> k[offset+lastindex],
                   c[offset+lastindex] -> c[offset+#+indexnumber-1],
                   c[offset+#+indexnumber-1] -> c[offset+lastindex],
                   mu[offset+lastindex] -> mu[offset+#+indexnumber-1],
                   mu[offset+#+indexnumber-1] -> mu[offset+lastindex]},
                   #+indexnumber-2, 
                   lastindex - 1, 
                   indexnumber - 1,
                   offset]
       )& , maxvalue-indexnumber+1 ]       
 
