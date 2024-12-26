(* A program to simplify delta functions of loop-momenta. *) 

simplifydelta[exp_,p_] := Module[{x = exp /. delta[-p+b_] :> delta[p-b], y},
                                          y = x /. delta[p+b_] -> 0; 
                                          (Collect[x-y, delta[p+_]] /. delta[p+b_] a_ :> (a /. p -> -b)) + y]
  
