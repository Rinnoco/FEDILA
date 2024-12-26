(* Programma per ridurre gli indici a *)


reducea[ expr_Plus] := 
                  reducea /@ expr
 

reducea[expr_Times] := 
       reducea[Select[expr,!FreeQ[#,a]&]] *
                         Select[expr,FreeQ[#,a]&] /;
                              Or @@ (FreeQ[#,a]& /@ List @@ expr)     

reducea[expr_] :=
      Block[ {lista},
            lista = Union[ (expr[[ Sequence @@ # ]]) & /@ Position[expr,a[_] ] ];
            expr /. Inner[Rule,lista,Array[a[#]&,Length[lista]],List]
           ]

(* Programma per ridurre gli indici b *)


reduceb[ expr_Plus] := 
                  reduceb /@ expr
 

reduceb[expr_Times] := 
       reduceb[Select[expr,!FreeQ[#,b]&]] *
                         Select[expr,FreeQ[#,b]&] /;
                              Or @@ (FreeQ[#,b]& /@ List @@ expr)     

reduceb[a_] :=
      Block[ {listb},
            listb = Union[ (a[[ Sequence @@ # ]]) & /@ Position[a,b[_] ] ];
            a /. Inner[Rule,listb,Array[b[#]&,Length[listb]],List]
           ]

(* Programma per ridurre gli indici c *)


reducec[ expr_Plus] := 
                  reducec /@ expr
 

reducec[expr_Times] := 
       reducec[Select[expr,!FreeQ[#,c]&]] *
                         Select[expr,FreeQ[#,c]&] /;
                              Or @@ (FreeQ[#,c]& /@ List @@ expr)     

reducec[a_] :=
      Block[ {listc},
            listc = Union[ (a[[ Sequence @@ # ]]) & /@ Position[a,c[_] ] ];
            a /. Inner[Rule,listc,Array[c[#]&,Length[listc]],List]
           ]

(* Programma per ridurre gli indici k *)


reducek[ expr_Plus] := 
                  reducek /@ expr
 

reducek[expr_Times] := 
       reducek[Select[expr,!FreeQ[#,k]&]] *
                         Select[expr,FreeQ[#,k]&] /;
                              Or @@ (FreeQ[#,k]& /@ List @@ expr)     

reducek[a_] :=
      Block[ {listk},
            listk = Union[ (a[[ Sequence @@ # ]]) & /@ Position[a,k[_] ] ];
            a /. Inner[Rule,listk,Array[k[#]&,Length[listk]],List]
           ]

(* Programma per ridurre gli indici q *)


reduceq[ expr_Plus] := 
                  reduceq /@ expr
 

reduceq[expr_Times] := 
       reduceq[Select[expr,!FreeQ[#,q]&]] *
                         Select[expr,FreeQ[#,q]&] /;
                              Or @@ (FreeQ[#,q]& /@ List @@ expr)     

reduceq[a_] :=
      Block[ {listq},
            listq = Union[ (a[[ Sequence @@ # ]]) & /@ Position[a,q[_] ] ];
            a /. Inner[Rule,listq,Array[q[#]&,Length[listq]],List]
           ]

(* Programma per ridurre gli indici p *)


reducep[ expr_Plus] := 
                  reducep /@ expr
 

reducep[expr_Times] := 
       reducep[Select[expr,!FreeQ[#,p]&]] *
                         Select[expr,FreeQ[#,p]&] /;
                              Or @@ (FreeQ[#,p]& /@ List @@ expr)     

reducep[a_] :=
      Block[ {listq},
            listp = Union[ (a[[ Sequence @@ # ]]) & /@ Position[a,p[_] ] ];
            a /. Inner[Rule,listp,Array[p[#]&,Length[listp]],List]
           ]
				
(* Programma per ridurre gli indici mu *)


reducemu[ expr_Plus] := 
                  reducemu /@ expr
 

reducemu[expr_Times] := 
       reducemu[Select[expr,!FreeQ[#,mu]&]] *
                         Select[expr,FreeQ[#,mu]&] /;
                              Or @@ (FreeQ[#,mu]& /@ List @@ expr)     

reducemu[a_] :=
      Block[ {listmu},
            listmu = Union[ (a[[ Sequence @@ # ]]) & /@ Position[a,mu[_] ] ];
            a /. Inner[Rule,listmu,Array[mu[#]&,Length[listmu]],List]
           ]

(* Programma per ridurre gli indici nu *)


reducenu[ expr_Plus] := 
                  reducenu /@ expr
 

reducenu[expr_Times] := 
       reducenu[Select[expr,!FreeQ[#,nu]&]] *
                         Select[expr,FreeQ[#,nu]&] /;
                              Or @@ (FreeQ[#,nu]& /@ List @@ expr)     

reducenu[a_] :=
      Block[ {listnu},
            listnu = Union[ (a[[ Sequence @@ # ]]) & /@ Position[a,nu[_] ] ];
            a /. Inner[Rule,listnu,Array[nu[#]&,Length[listnu]],List]
           ]

(* Programma per ridurre gli indici rho dopo l`applicazione del
   simplifydelm *)


reducerho[ expr_Plus] := 
                  reducerho /@ expr
 

reducerho[expr_Times] := 
       reducerho[Select[expr,!FreeQ[#,rho]&]] *
                         Select[expr,FreeQ[#,rho]&] /;
                              Or @@ (FreeQ[#,rho]& /@ List @@ expr)     

reducerho[a_] :=
      Block[ {listrho},
            listrho = Union[ (a[[ Sequence @@ # ]]) & /@ Position[a,rho[_] ] ];
            a /. Inner[Rule,listrho,Array[rho[#]&,Length[listrho]],List]
           ]

