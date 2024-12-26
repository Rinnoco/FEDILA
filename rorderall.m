rhos[expr_] := expr[[Sequence @@ #]]& /@ Position[expr,rho[_]]

rorderall[expr_Plus] := rorderall /@ expr

rorderall[expr_] := Sort[(expr /. Inner[Rule, Union[rhos[expr]], #, List])& /@ Permutations[Union[rhos[expr]]]][[1]]
