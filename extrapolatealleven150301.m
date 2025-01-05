(* "extrapolateeven" performs extrapolations of numerical data to infinite lattices 
   Input must be in the form of one or more lists of triplets 
       {lattice_size, value_of_r,               result} 
   (or {lattice_size, {value_of_r},             result}
    or {lattice_size, {value_of_r, value_of_m}, result})
   e.g.,
   extrapolateeven[list],   or   extrapolateeven[list, Select[list,EvenQ[#[[1]]]&]].

   A series of extrapolations to different functional forms is performed. To each 
   extrapolation, 3 different criteria are used to assign values of deviation.
   ( (a) discrepancy at L=Lmax-(#of fit parameters),
     (b) discrepancy at L=Lmax,
     (c) discrepancy at L=Lmax-(#of fit parameters)-1     )
   Subsequently, for each of the three criteria, we take an average and standard error 
   over all extrapolations, weighting each extrapolation by a probability proportional 
   to the inverse squared of its deviation.

   The result, for each r (or {r}, or {r,m}), is in the form:
        {r,     {{mean1, error1}, {mean2,error2}, {mean3,error3}}}
   (or  {{r},   {{mean1, error1}, {mean2,error2}, {mean3,error3}}}
    or  {{r,m}, {{mean1, error1}, {mean2,error2}, {mean3,error3}}})    *)

extrapolateeven[list__]:=
 Block[{listr, extrapolations, partiallist, probabilities, norm, result, means, errors},
       result = {};
       extrapolations = Join @@ (extrapolateeven1 /@ (List[list]));
       extrapolations = Table[{extrapolations[[i,1]], extrapolations[[i,2]],
                               (Max[#,1.*^-80])& /@ extrapolations[[i,3]]},
                              {i,Length[extrapolations]}];
               (*   Print[extrapolations];   *)
       listr = Union[(#[[1]])& /@ extrapolations];
       Do[partiallist = Select[extrapolations, (#[[1]] == listr[[ir]])&];
          norm = Sum[partiallist[[i,3,#]]^(-2),{i,Length[partiallist]}]& /@ {1,2,3};
          probabilities = Table[Table[partiallist[[i,3,j]]^(-2)/norm[[j]],
                                      {j,3}],
                                {i,Length[partiallist]}];
          means = Sum[partiallist[[i,2,2]] probabilities[[i,#]], 
                      {i,Length[partiallist]}]& /@ {1,2,3};
          errors = Sqrt[Sum[(partiallist[[i,2,2]] - means[[#]])^2 probabilities[[i,#]], 
                        {i,Length[partiallist]}]]& /@ {1,2,3};
          result = Append[result,{listr[[ir]], {means[[#]],errors[[#]]}& /@ {1,2,3}}],
          {ir,Length[listr]}];
       result]          

extrapolateeven1[list_]:=
 Block[{listr, result, partiallist, exponents,
        coefficients, coefficientsback, intrapolation0, intrapolation1,
        intrapolation2, deviation, a, b, c, d, e},
       result = {};
       exponents = {{{2,4},{2,6},{4,6}},
                    {{2},{4}},
                    {{2,4},{2,6},{4,6}},
                    {{2,4},{2,6},{4,6}},
                    {{2},{4}},
                    {{2,4},{2,6},{4,6}},
                    {{2,4,6}}};
       listr = Union[(#[[2]])& /@ list];
       Do[partiallist = Select[list, (#[[2]] == listr[[ir]])&];
          Do[coefficients = 
               NSolve[(a + b/(#[[1]])^exponents[[1,ifit,1]] 
                        + c/(#[[1]])^exponents[[1,ifit,2]]
                      == #[[3]])& /@ Take[partiallist,-3],{a,b,c},50][[1]];
             coefficientsback = 
               NSolve[(a + b/(#[[1]])^exponents[[1,ifit,1]]
                        + c/(#[[1]])^exponents[[1,ifit,2]]
                      == #[[3]])& /@ Take[Take[partiallist,-4],3],{a,b,c},50][[1]];
             intrapolation0 = 
               ((a + b/(#[[1]])^exponents[[1,ifit,1]]
                   + c/(#[[1]])^exponents[[1,ifit,2]])&
                   [partiallist[[-1]]]) /. coefficientsback;
             intrapolation1 = 
               ((a + b/(#[[1]])^exponents[[1,ifit,1]]
                   + c/(#[[1]])^exponents[[1,ifit,2]])&
                   [partiallist[[-4]]]) /. coefficients;
             intrapolation2 = 
               ((a + b/(#[[1]])^exponents[[1,ifit,1]]
                   + c/(#[[1]])^exponents[[1,ifit,2]])&
                   [partiallist[[-5]]]) /. coefficients;
             deviation = N[{Abs[(intrapolation1/partiallist[[-4,3]]) -1 ],
                            Abs[(intrapolation0/partiallist[[-1,3]]) -1 ],
                            Abs[(intrapolation2/partiallist[[-5,3]]) -1 ]}];
             result = Append[result,{listr[[ir]],coefficients[[1]],deviation}],
             {ifit,Length[exponents[[1]]]}];
          Do[coefficients = 
               NSolve[(a + b/(#[[1]])^exponents[[2,ifit,1]]
                        + c/(#[[1]])^exponents[[2,ifit,1]]*Log[#[[1]]]
                      == #[[3]])& /@ Take[partiallist,-3],{a,b,c},50][[1]];
             coefficientsback = 
               NSolve[(a + b/(#[[1]])^exponents[[2,ifit,1]]
                        + c/(#[[1]])^exponents[[2,ifit,1]]*Log[#[[1]]]
                      == #[[3]])& /@ Take[Take[partiallist,-4],3],{a,b,c},50][[1]];
             intrapolation0 = 
               ((a + b/(#[[1]])^exponents[[2,ifit,1]]
                   + c/(#[[1]])^exponents[[2,ifit,1]]*Log[#[[1]]])&
                   [partiallist[[-1]]]) /. coefficientsback;
             intrapolation1 = 
               ((a + b/(#[[1]])^exponents[[2,ifit,1]]
                   + c/(#[[1]])^exponents[[2,ifit,1]]*Log[#[[1]]])&
                   [partiallist[[-4]]]) /. coefficients;
             intrapolation2 = 
               ((a + b/(#[[1]])^exponents[[2,ifit,1]]
                   + c/(#[[1]])^exponents[[2,ifit,1]]*Log[#[[1]]])&
                   [partiallist[[-5]]]) /. coefficients;
             deviation = N[{Abs[(intrapolation1/partiallist[[-4,3]]) -1 ],
                            Abs[(intrapolation0/partiallist[[-1,3]]) -1 ],
                            Abs[(intrapolation2/partiallist[[-5,3]]) -1 ]}];
             result = Append[result,{listr[[ir]],coefficients[[1]],deviation}],
             {ifit,Length[exponents[[2]]]}];
          Do[coefficients = 
               NSolve[(a + b/(#[[1]])^exponents[[3,ifit,1]]
                        + c/(#[[1]])^exponents[[3,ifit,2]]
                        + d/(#[[1]])^exponents[[3,ifit,2]]*Log[#[[1]]]
                      == #[[3]])& /@ Take[partiallist,-4],{a,b,c,d},50][[1]];
             coefficientsback = 
               NSolve[(a + b/(#[[1]])^exponents[[3,ifit,1]]
                        + c/(#[[1]])^exponents[[3,ifit,2]]
                        + d/(#[[1]])^exponents[[3,ifit,2]]*Log[#[[1]]]
                      == #[[3]])& /@ Take[Take[partiallist,-5],4],{a,b,c,d},50][[1]];
             intrapolation0 = 
               ((a + b/(#[[1]])^exponents[[3,ifit,1]]
                   + c/(#[[1]])^exponents[[3,ifit,2]]
                   + d/(#[[1]])^exponents[[3,ifit,2]]*Log[#[[1]]])&
                   [partiallist[[-1]]]) /. coefficientsback;
             intrapolation1 = 
               ((a + b/(#[[1]])^exponents[[3,ifit,1]]
                   + c/(#[[1]])^exponents[[3,ifit,2]]
                   + d/(#[[1]])^exponents[[3,ifit,2]]*Log[#[[1]]])&
                   [partiallist[[-5]]]) /. coefficients;
             intrapolation2 = 
               ((a + b/(#[[1]])^exponents[[3,ifit,1]]
                   + c/(#[[1]])^exponents[[3,ifit,2]]
                   + d/(#[[1]])^exponents[[3,ifit,2]]*Log[#[[1]]])&
                   [partiallist[[-6]]]) /. coefficients;
             deviation = N[{Abs[(intrapolation1/partiallist[[-5,3]]) -1 ],
                            Abs[(intrapolation0/partiallist[[-1,3]]) -1 ],
                            Abs[(intrapolation2/partiallist[[-6,3]]) -1 ]}];
             result = Append[result,{listr[[ir]],coefficients[[1]],deviation}],
             {ifit,Length[exponents[[3]]]}];
          Do[coefficients = 
               NSolve[(a + b/(#[[1]])^exponents[[4,ifit,1]]
                        + c/(#[[1]])^exponents[[4,ifit,2]]
                        + d/(#[[1]])^exponents[[4,ifit,1]]*Log[#[[1]]]
                      == #[[3]])& /@ Take[partiallist,-4],{a,b,c,d},50][[1]];
             coefficientsback = 
               NSolve[(a + b/(#[[1]])^exponents[[4,ifit,1]]
                        + c/(#[[1]])^exponents[[4,ifit,2]]
                        + d/(#[[1]])^exponents[[4,ifit,1]]*Log[#[[1]]]
                      == #[[3]])& /@ Take[Take[partiallist,-5],4],{a,b,c,d},50][[1]];
             intrapolation0 = 
               ((a + b/(#[[1]])^exponents[[4,ifit,1]]
                   + c/(#[[1]])^exponents[[4,ifit,2]]
                   + d/(#[[1]])^exponents[[4,ifit,1]]*Log[#[[1]]])&
                   [partiallist[[-1]]]) /. coefficientsback;
             intrapolation1 = 
               ((a + b/(#[[1]])^exponents[[4,ifit,1]]
                   + c/(#[[1]])^exponents[[4,ifit,2]]
                   + d/(#[[1]])^exponents[[4,ifit,1]]*Log[#[[1]]])&
                   [partiallist[[-5]]]) /. coefficients;
             intrapolation2 = 
               ((a + b/(#[[1]])^exponents[[4,ifit,1]]
                   + c/(#[[1]])^exponents[[4,ifit,2]]
                   + d/(#[[1]])^exponents[[4,ifit,1]]*Log[#[[1]]])&
                   [partiallist[[-6]]]) /. coefficients;
             deviation = N[{Abs[(intrapolation1/partiallist[[-5,3]]) -1 ],
                            Abs[(intrapolation0/partiallist[[-1,3]]) -1 ],
                            Abs[(intrapolation2/partiallist[[-6,3]]) -1 ]}];
             result = Append[result,{listr[[ir]],coefficients[[1]],deviation}],
             {ifit,Length[exponents[[4]]]}];
          Do[coefficients = 
               NSolve[(a + b/(#[[1]])^exponents[[5,ifit,1]] 
                        + c/(#[[1]])^exponents[[5,ifit,1]]*Log[#[[1]]]
                        + d/(#[[1]])^exponents[[5,ifit,1]]*Log[#[[1]]]^2
                      == #[[3]])& /@ Take[partiallist,-4],{a,b,c,d},50][[1]];
             coefficientsback = 
               NSolve[(a + b/(#[[1]])^exponents[[5,ifit,1]]
                        + c/(#[[1]])^exponents[[5,ifit,1]]*Log[#[[1]]]
                        + d/(#[[1]])^exponents[[5,ifit,1]]*Log[#[[1]]]^2
                      == #[[3]])& /@ Take[Take[partiallist,-5],4],{a,b,c,d},50][[1]];
             intrapolation0 = 
               ((a + b/(#[[1]])^exponents[[5,ifit,1]]
                   + c/(#[[1]])^exponents[[5,ifit,1]]*Log[#[[1]]]
                   + d/(#[[1]])^exponents[[5,ifit,1]]*Log[#[[1]]]^2)&
                   [partiallist[[-1]]]) /. coefficientsback;
             intrapolation1 = 
               ((a + b/(#[[1]])^exponents[[5,ifit,1]]
                   + c/(#[[1]])^exponents[[5,ifit,1]]*Log[#[[1]]]
                   + d/(#[[1]])^exponents[[5,ifit,1]]*Log[#[[1]]]^2)&
                   [partiallist[[-5]]]) /. coefficients;
             intrapolation2 = 
               ((a + b/(#[[1]])^exponents[[5,ifit,1]]
                   + c/(#[[1]])^exponents[[5,ifit,1]]*Log[#[[1]]]
                   + d/(#[[1]])^exponents[[5,ifit,1]]*Log[#[[1]]]^2)&
                   [partiallist[[-6]]]) /. coefficients;
             deviation = N[{Abs[(intrapolation1/partiallist[[-5,3]]) -1 ],
                            Abs[(intrapolation0/partiallist[[-1,3]]) -1 ],
                            Abs[(intrapolation2/partiallist[[-6,3]]) -1 ]}];
             result = Append[result,{listr[[ir]],coefficients[[1]],deviation}],
             {ifit,Length[exponents[[5]]]}];
          Do[coefficients = 
               NSolve[(a + b/(#[[1]])^exponents[[6,ifit,1]]
                        + c/(#[[1]])^exponents[[6,ifit,2]]
                        + d/(#[[1]])^exponents[[6,ifit,2]]*Log[#[[1]]]
                        + e/(#[[1]])^exponents[[6,ifit,2]]*Log[#[[1]]]^2
                      == #[[3]])& /@ Take[partiallist,-5],{a,b,c,d,e},50][[1]];
             coefficientsback = 
               NSolve[(a + b/(#[[1]])^exponents[[6,ifit,1]]
                        + c/(#[[1]])^exponents[[6,ifit,2]]
                        + d/(#[[1]])^exponents[[6,ifit,2]]*Log[#[[1]]]
                        + e/(#[[1]])^exponents[[6,ifit,2]]*Log[#[[1]]]^2
                      == #[[3]])& /@ Take[Take[partiallist,-6],5],{a,b,c,d,e},50][[1]];
             intrapolation0 = 
               ((a + b/(#[[1]])^exponents[[6,ifit,1]]
                   + c/(#[[1]])^exponents[[6,ifit,2]]
                   + d/(#[[1]])^exponents[[6,ifit,2]]*Log[#[[1]]]
                   + e/(#[[1]])^exponents[[6,ifit,2]]*Log[#[[1]]]^2)&
                   [partiallist[[-1]]]) /. coefficientsback;
             intrapolation1 = 
               ((a + b/(#[[1]])^exponents[[6,ifit,1]]
                   + c/(#[[1]])^exponents[[6,ifit,2]]
                   + d/(#[[1]])^exponents[[6,ifit,2]]*Log[#[[1]]]
                   + e/(#[[1]])^exponents[[6,ifit,2]]*Log[#[[1]]]^2)&
                   [partiallist[[-6]]]) /. coefficients;
             intrapolation2 = 
               ((a + b/(#[[1]])^exponents[[6,ifit,1]]
                   + c/(#[[1]])^exponents[[6,ifit,2]]
                   + d/(#[[1]])^exponents[[6,ifit,2]]*Log[#[[1]]]
                   + e/(#[[1]])^exponents[[6,ifit,2]]*Log[#[[1]]]^2)&
                   [partiallist[[-7]]]) /. coefficients;
             deviation = N[{Abs[(intrapolation1/partiallist[[-6,3]]) -1 ],
                            Abs[(intrapolation0/partiallist[[-1,3]]) -1 ],
                            Abs[(intrapolation2/partiallist[[-7,3]]) -1 ]}];
             result = Append[result,{listr[[ir]],coefficients[[1]],deviation}],
	    {ifit,Length[exponents[[6]]]}];
          Do[coefficients = 
               NSolve[(a + b/(#[[1]])^exponents[[6,ifit,1]]
                        + c/(#[[1]])^exponents[[6,ifit,2]]
                        + d/(#[[1]])^exponents[[6,ifit,1]]*Log[#[[1]]]
                        + e/(#[[1]])^exponents[[6,ifit,1]]*Log[#[[1]]]^2
                      == #[[3]])& /@ Take[partiallist,-5],{a,b,c,d,e},50][[1]];
             coefficientsback = 
               NSolve[(a + b/(#[[1]])^exponents[[6,ifit,1]]
                        + c/(#[[1]])^exponents[[6,ifit,2]]
                        + d/(#[[1]])^exponents[[6,ifit,1]]*Log[#[[1]]]
                        + e/(#[[1]])^exponents[[6,ifit,1]]*Log[#[[1]]]^2
                      == #[[3]])& /@ Take[Take[partiallist,-6],5],{a,b,c,d,e},50][[1]];
             intrapolation0 = 
               ((a + b/(#[[1]])^exponents[[6,ifit,1]]
                   + c/(#[[1]])^exponents[[6,ifit,2]]
                   + d/(#[[1]])^exponents[[6,ifit,1]]*Log[#[[1]]]
                   + e/(#[[1]])^exponents[[6,ifit,1]]*Log[#[[1]]]^2)&
                   [partiallist[[-1]]]) /. coefficientsback;
             intrapolation1 = 
               ((a + b/(#[[1]])^exponents[[6,ifit,1]]
                   + c/(#[[1]])^exponents[[6,ifit,2]]
                   + d/(#[[1]])^exponents[[6,ifit,1]]*Log[#[[1]]]
                   + e/(#[[1]])^exponents[[6,ifit,1]]*Log[#[[1]]]^2)&
                   [partiallist[[-6]]]) /. coefficients;
             intrapolation2 = 
               ((a + b/(#[[1]])^exponents[[6,ifit,1]]
                   + c/(#[[1]])^exponents[[6,ifit,2]]
                   + d/(#[[1]])^exponents[[6,ifit,1]]*Log[#[[1]]]
                   + e/(#[[1]])^exponents[[6,ifit,1]]*Log[#[[1]]]^2)&
                   [partiallist[[-7]]]) /. coefficients;
             deviation = N[{Abs[(intrapolation1/partiallist[[-6,3]]) -1 ],
                            Abs[(intrapolation0/partiallist[[-1,3]]) -1 ],
                            Abs[(intrapolation2/partiallist[[-7,3]]) -1 ]}];
             result = Append[result,{listr[[ir]],coefficients[[1]],deviation}],
	    {ifit,Length[exponents[[6]]]}];
          Do[coefficients = 
               NSolve[(a + b/(#[[1]])^exponents[[6,ifit,1]]
                        + c/(#[[1]])^exponents[[6,ifit,2]]
                        + d/(#[[1]])^exponents[[6,ifit,2]]*Log[#[[1]]]
                        + e/(#[[1]])^exponents[[6,ifit,1]]*Log[#[[1]]]
                      == #[[3]])& /@ Take[partiallist,-5],{a,b,c,d,e},50][[1]];
             coefficientsback = 
               NSolve[(a + b/(#[[1]])^exponents[[6,ifit,1]]
                        + c/(#[[1]])^exponents[[6,ifit,2]]
                        + d/(#[[1]])^exponents[[6,ifit,2]]*Log[#[[1]]]
                        + e/(#[[1]])^exponents[[6,ifit,1]]*Log[#[[1]]]
                      == #[[3]])& /@ Take[Take[partiallist,-6],5],{a,b,c,d,e},50][[1]];
             intrapolation0 = 
               ((a + b/(#[[1]])^exponents[[6,ifit,1]]
                   + c/(#[[1]])^exponents[[6,ifit,2]]
                   + d/(#[[1]])^exponents[[6,ifit,2]]*Log[#[[1]]]
                   + e/(#[[1]])^exponents[[6,ifit,1]]*Log[#[[1]]])&
                   [partiallist[[-1]]]) /. coefficientsback;
             intrapolation1 = 
               ((a + b/(#[[1]])^exponents[[6,ifit,1]]
                   + c/(#[[1]])^exponents[[6,ifit,2]]
                   + d/(#[[1]])^exponents[[6,ifit,2]]*Log[#[[1]]]
                   + e/(#[[1]])^exponents[[6,ifit,1]]*Log[#[[1]]])&
                   [partiallist[[-6]]]) /. coefficients;
             intrapolation2 = 
               ((a + b/(#[[1]])^exponents[[6,ifit,1]]
                   + c/(#[[1]])^exponents[[6,ifit,2]]
                   + d/(#[[1]])^exponents[[6,ifit,2]]*Log[#[[1]]]
                   + e/(#[[1]])^exponents[[6,ifit,1]]*Log[#[[1]]])&
                   [partiallist[[-7]]]) /. coefficients;
             deviation = N[{Abs[(intrapolation1/partiallist[[-6,3]]) -1 ],
                            Abs[(intrapolation0/partiallist[[-1,3]]) -1 ],
                            Abs[(intrapolation2/partiallist[[-7,3]]) -1 ]}];
             result = Append[result,{listr[[ir]],coefficients[[1]],deviation}],
	    {ifit,Length[exponents[[6]]]}];
          Do[coefficients = 
               NSolve[(a + b/(#[[1]])^exponents[[7,ifit,1]]
                        + c/(#[[1]])^exponents[[7,ifit,2]]
                        + d/(#[[1]])^exponents[[7,ifit,3]]
                        + e/(#[[1]])^exponents[[7,ifit,1]]*Log[#[[1]]]
                      == #[[3]])& /@ Take[partiallist,-5],{a,b,c,d,e},50][[1]];
             coefficientsback = 
               NSolve[(a + b/(#[[1]])^exponents[[7,ifit,1]]
                        + c/(#[[1]])^exponents[[7,ifit,2]]
                        + d/(#[[1]])^exponents[[7,ifit,3]]
                        + e/(#[[1]])^exponents[[7,ifit,1]]*Log[#[[1]]]
                      == #[[3]])& /@ Take[Take[partiallist,-6],5],{a,b,c,d,e},50][[1]];
             intrapolation0 = 
               ((a + b/(#[[1]])^exponents[[7,ifit,1]]
                   + c/(#[[1]])^exponents[[7,ifit,2]]
                   + d/(#[[1]])^exponents[[7,ifit,3]]
                   + e/(#[[1]])^exponents[[7,ifit,1]]*Log[#[[1]]])&
                   [partiallist[[-1]]]) /. coefficientsback;
             intrapolation1 = 
               ((a + b/(#[[1]])^exponents[[7,ifit,1]]
                   + c/(#[[1]])^exponents[[7,ifit,2]]
                   + d/(#[[1]])^exponents[[7,ifit,3]]
                   + e/(#[[1]])^exponents[[7,ifit,1]]*Log[#[[1]]])&
                   [partiallist[[-6]]]) /. coefficients;
             intrapolation2 = 
               ((a + b/(#[[1]])^exponents[[7,ifit,1]]
                   + c/(#[[1]])^exponents[[7,ifit,2]]
                   + d/(#[[1]])^exponents[[7,ifit,3]]
                   + e/(#[[1]])^exponents[[7,ifit,1]]*Log[#[[1]]])&
                   [partiallist[[-7]]]) /. coefficients;
             deviation = N[{Abs[(intrapolation1/partiallist[[-6,3]]) -1 ],
                            Abs[(intrapolation0/partiallist[[-1,3]]) -1 ],
                            Abs[(intrapolation2/partiallist[[-7,3]]) -1 ]}];
             result = Append[result,{listr[[ir]],coefficients[[1]],deviation}],
             {ifit,Length[exponents[[7]]]}],
          {ir,Length[listr]}];
       result]
