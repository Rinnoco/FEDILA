(* Automated extrapolation to infinite volume.
 Dependencies: extrapolatealleven150301.m ; *)

extrapolate[filelist_List,varlist_List] :=
  Module[{templist,l},
	 templist = ReadList[#,Word]& /@ filelist;
	 templist = Map[ToExpression[StringReplace[#, {"E" -> "*^"}]]&,templist,{2}];
	 l = (Do[If[IntegerQ[#[[i]]],index=i-1; Break[]],{i,2,Length[#]}]; index)& /@ templist;
	 templist = Table[Partition[templist[[i]],l[[i]]],{i,Length[templist]}];
	 templist = Map[{tag[Take[#,7]],If[Length[Drop[#,7]]<Length[varlist],Join[Drop[#,7],Table[0.,Length[varlist]-Length[Drop[#,7]]]],Drop[#,7]]}&,templist,{2}];
	 templist = (Plus @@ templist) /. tag[a_]*b_. :> a;
	 templist = Table[{#[[1,1]],Drop[#[[1]],1],#[[2,i]]},{i,Length[#[[2]]]}]& /@ templist;
	 templist = Transpose[templist,{2,1,3}];
	 (* Set data, which are smaller than 10^-8, to zero. *)
	 templist = Map[{#[[1]],#[[2]],If[Abs[#[[3]]]<=10^-8,zero,#[[3]]]}&,templist,{2}];
	 templist = (extrapolateeven /@ templist) /. zero -> 0.;
	 (* We choose the extrapolation with the greatest error *)
	 templist = templist /.{{a_?NumberQ,b_},{c_,d_},{e_,f_}} :> Sort[{{a,b},{c,d},{e,f}},(Abs[#1[[2]]] > Abs[#2[[2]]])&][[1]];
	 (* Let us omit the terms that are zero within the error, according to the following restriction *)
	 templist = templist /.{a_?NumberQ,b_} :> If[a !=0. && Abs[a]/b < 2 && b< 10^(-8),{0.,0.},{a,b}];
	 templist = result /@ templist;
	 Sum[var[i]*templist[[i]],{i,Length[varlist]}] /. varlist]
