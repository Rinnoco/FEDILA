

symmetrizepartially[ vertice_, listagruppi_ ]:= 
     vertice /;                                        Length[listagruppi] == 1

symmetrizepartially[ vertice_, listagruppi_ ] := 
     symmetrizepartially[ vertice, Drop[ listagruppi, -1] ] /;
                                                        Last[listagruppi ] == 0

symmetrizepartially[ vertice_, listagruppi_ ] := 
     symmetrizepartially[ symmetrizepartially1[ vertice, 
                                                Plus@@listagruppi, 
                                                Plus@@listagruppi,
                                                Last[listagruppi] ],
                          Drop[ listagruppi, -1] ] /
     Binomial[ Plus@@listagruppi, Last[listagruppi] ]



symmetrizepartially1[ vertice_, maxvalue_, lastindex_, 0 ] := vertice

symmetrizepartially1[ vertice_, maxvalue_, lastindex_, indexnumber_ ] :=
  Plus@@Array[(symmetrizepartially1 [vertice 
                                        /. k[lastindex] -> dummy 
                                        /. k[#+indexnumber-1] -> k[lastindex] 
                                        /. dummy -> k[#+indexnumber-1]
                                        /. c[lastindex] -> dummy 
                                        /. c[#+indexnumber-1] -> c[lastindex] 
                                        /. dummy -> c[#+indexnumber-1]
                                        /. mu[lastindex] -> dummy 
                                        /. mu[#+indexnumber-1] -> mu[lastindex]
                                        /. dummy -> mu[#+indexnumber-1],
                                     #+indexnumber-2, 
                                     lastindex - 1, 
                                     indexnumber - 1 
                                    ]
              )& , maxvalue-indexnumber+1 ]       
 
