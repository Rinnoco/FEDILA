(* This version of integrator contains definitions relevant to overlap
   fermions, and the Iwasaki gluonic propagator                             *)
(* NB: rho indices, assumed distinct, are NOT summed over their range       *)

(* In this version on integrator it is assumed that each summand in the
   integrand is multiplied by a linear combination of var[i]; accordingly,
   the result is also given as a linear combination.                        *)

(* To avoid a plethora of Lorentz indices, we allow also expressions of
   the form s2sq[p[1]] (= \sum_\rho s2[p[1],rho]^2),
            sisq[p[1]] (= \sum_\rho s2[2p[1],rho]^2) and
            s2qu[p[1]] (= \sum_\rho s2[p[1],rho]^4)                         *)

(* To save on CPU time, the program evaluates the integral for up to 300 
   sextuplets of values for (r,m,c0,c1,c2,c3) (the Iwasaki parameters) 
   simultaneously                                                           *)


integrator1::usage = StringJoin[
  "integrator1[integrand_, propagators_, file_] takes as input a 1-loop      \n
   integrand, in the form of a sum of products of: numbers and/or s2 and/or  \n
   c2 and/or m(p) (the fermion mass) and/or r (the Wilson parameter) and/or  \n
   propagators (fhat, hat2, dprop) and/or the Iwasaki parameters cprop0,     \n
   cprop1, cprop2, cprop3; thus, no factors of g, Nc, i0, etc. are allowed.  \n
      In this version, occurences of expressions from the overlap formalism  \n
   are also permitted in the integrand, in particular:                       \n
            s2sqinv[p[1]], mO[p[1]], omegaO[p[1]], omegainvO[p[1]],          \n
            omegaplusinvO[p[1],0], omegabO[p[1]], omegabinvO[p[1]]           \n
      The propagators carry momentum p[1]. They can be bosonic, fermionic,   \n
   and any algebraic expression thereof, e.g.                                \n
          hat2[p[1]]^3*fhat[p[1]]*(hat2[p[1]]-fhat[p[1]])                    \n
      The Lorentz indices can be rho[i], i=1,2,3,4; they are taken in the    \n
   i-th direction.                                                           \n
      The output, written in `file', is a fortran code for the evaluation of \n
   the integral. " ]

integrator1::wrongArgument = "integrator1 called with inappropriate argument"

integrator1[integrand_, propagators_, file_]:= 
  Message[integrator1::wrongArgument] /; 
  !(Complement[Union[If[Head[#]===Symbol,#,Head[#]]& /@ Variables[integrand]],
   {s2,c2,s2sq,s2sqinv,sisq,c2sq,cisq,s2qu,r,m,var,hat2,fhat,prop,dprop,cprop0,cprop1,
    cprop2,cprop3,mO,omegaO,omegabO,omegainvO,omegaplusinvO,omegabinvO}]==={})

integrator1[integrand_, propagators_, file_]:=
  Block[
    {expr, variables, variablelist, varlist, varlength,
     rulelist, factorlist, proplist,
     expr2, expr3, expr4, index1, index2, index3, dummy},

    w[a__] := WriteString[ToString[file], "      ", a, "\n"];
    wc[a__]:= WriteString[ToString[file], "     &", a, "\n"];

    expr = List /@ (If[Head[integrand]===Plus,
                       List@@integrand, List[integrand]]);

    variables = Select[Variables[integrand],!FreeQ[#,p[1]]&];
    variablelist = Table[Cases[variables,_[_,rho[j]]],{j,4}];
    variablelist = 
      Append[Drop[variablelist,-1], 
             Join[variablelist[[-1]],
                  Select[variables,(FreeQ[#,rho] || (!FreeQ[#,dprop]) || (!FreeQ[#,prop]))&]]];

    Do[rulelist = Rule[#,1]& /@ (variablelist[[-j]]);
       expr = (Join[{(#[[1]]) /. rulelist},
                    {(dummy #[[1]]) / ((dummy #[[1]]) /. rulelist)},
                    Drop[#,1]])& /@ expr,
       {j,Length[variablelist]}];

    varlist = Union[integrand[[Sequence @@ #]]& /@ Position[integrand,var[_]]];
    varlength = Max[(#[[1]])& /@ varlist, 1];
    factorlist = ((#[[1]])& /@ expr);
    factorlist = Table[# /. var[j]->1 /. var[_]->0,{j,varlength}]& /@ factorlist;
    factorlist = factorlist /. r -> r[ir] /. m -> m[ir] /. mO -> m[ir] /. 
                               cprop0 -> z0[ir] /. cprop1 -> z1[ir] /.
                               cprop2 -> z2[ir] /. cprop3 -> z3[ir];
    factorlist = Map[FortranForm,factorlist,{2}];

    proplist = {propagators};
    proplist = proplist /. {fhat[p[1]]-> fhat1[ir], hat2[p[1]]->hat1};
    proplist = FortranForm /@ proplist;

    expr = Drop[#,1]& /@ expr;
    expr = expr /. (a_[b_,rho[n_]] :>
                    a[b /. {p[1] :> ToExpression[StringJoin["i",ToString[n]]]}]);
    expr = expr /. {s2sq[p[1]]->s2sq1, sisq[p[1]]->sisq1, 
                    c2sq[p[1]]->c2sq1, cisq[p[1]]->cisq1, 
                    s2qu[p[1]]->s2qu1, s2sqinv[p[1]]->s2sqinv1};
    expr = expr /. {omegaO[p[1]]->omegao1[ir], omegainvO[p[1]]->omegainvo1[ir],
                    omegaplusinvO[p[1],0]->omegaplusinvo1[ir],
                    omegabinvO[p[1]]->omegabinvo1[ir], omegabO[p[1]]->omegabo1[ir],
                    mO[p[1]]->mo1[ir]};
    expr = expr /. m[p[1]] -> m1[ir];
    expr = expr /. {s2[2 a__]^2 :> si2[a],  c2[2 a__]^2 :> ci2[a],
                    s2[a__]^2 :> s22[a], c2[a__]^2 :> c22[a],
                    s2[2 a__] :> si[a],  c2[2 a__] :> ci[a],
                    s2[a__]^4 :> s24[a], c2[a__]^4 :> c24[a],
                    fhat[p[1]]-> fhat1[ir], hat2[p[1]]->hat1,
                    dprop[p[1],rho[m_],rho[n_]]:> dprop1[m,n],
                    prop[p[1],rho[m_],rho[n_]]:> prop1[m,n]};
    expr = Map[FortranForm,expr,{2}];

    expr2 = Union[Take[#,{2,4}]& /@ expr];
    expr3 = Union[Take[#,{3,4}]& /@ expr];
    expr4 = Union[Take[#,{4,4}]& /@ expr];
    index3 = Table[Position[expr4,Drop[expr3[[j]],1]][[1,1]],{j,Length[expr3]}];
    index2 = Table[Position[expr3,Drop[expr2[[j]],1]][[1,1]],{j,Length[expr2]}];
    index1 = Table[Position[expr2,Drop[expr[[j]],1]][[1,1]],{j,Length[expr]}];

    w["program main"];
    w["implicit real*8 (a-h,o-z)"];
    w["real*8 k2p1, k4p1"];
    w["real*8 m, m1, mo1"];
    w["parameter (l = ",Length[expr],")"];
    w["dimension a(l,4,300)"];
    w["dimension s2(-1600:1600), c2(-1600:1600), s22(-1600:1600)"];
    w["dimension c22(-1600:1600), s24(-1600:1600), c24(-1600:1600)"];
    w["dimension si(-1600:1600), ci(-1600:1600), si2(-1600:1600)"];
    w["dimension ci2(-1600:1600)"];
    w["dimension r(300), r24(300), r12(300), m(300)"];
    w["dimension z0(300), z1(300), z2(300), z3(300)"];
    w["dimension cc1(300), cc2(300)"];
    w["dimension fhat1(300), m1(300)"];
    w["dimension dprop1(4,4), prop1(4,4), g(4,4), ginv(4,4)"];
    w["integer indx(4)"];
    w["dimension omegainvo1(300), omegabinvo1(300), omegaplusinvo1(300)"];
    w["dimension omegao1(300), omegabo1(300), mo1(300)"];
    w["dimension result(",varlength,")"];
    w[""];
    w["pi = 4.0*atan(1.d0)"];
    WriteString[ToString[file], "CCCC  ",
                "Enter minimum and maximum length of lattice", "\n"];
    w["read(*,*) nmin, nmax"];
    WriteString[ToString[file], "CCCC  ",
                "Write up to 300 sextuplets of values for r, m, c0, c1, c2, c3, one set per line", "\n"];
    w["ir = 1"];
    WriteString[ToString[file], "  1   read(*,*,end=2) r(ir), m(ir), \n"];
    wc["      z0(ir), z1(ir), z2(ir), z3(ir)"];
    w["cc1(ir) = z2(ir) + z3(ir)"];
    w["cc2(ir) = z1(ir) - z2(ir) - z3(ir)"];
    w["ir = ir + 1"];
    w["goto 1"];
    WriteString[ToString[file], "  2   nr = ir - 1 \n"];
    w["do ir = 1, nr"];
    w[" r24(ir) = 4.d0*r(ir)**2"];
    w[" r12(ir) = 2.d0*r(ir)"];
    w["enddo"];
    w[""];
    w["do 1000 n = nmin, nmax, 2"];
    w["nmod2 = mod(n,2)"];
    w["nhalf = (n+nmod2)/2"];
    w["n4 = n*4"];
    w["do i = -12*n,12*n"];
    w[" s2(i) = sin(i*pi/n)"];
    w[" c2(i) = cos(i*pi/n)"];
    w[" s22(i) = s2(i)**2"];
    w[" c22(i) = c2(i)**2"];
    w[" s24(i) = s2(i)**4"];
    w[" c24(i) = c2(i)**4"];
    w[" si(i) = sin(2*i*pi/n)"];
    w[" ci(i) = cos(2*i*pi/n)"];
    w[" si2(i) = si(i)**2"];
    w[" ci2(i) = ci(i)**2"];
    w["enddo"];
    w[""];
    w["do i = 1,l"];
    w["do ir = 1,nr"];
    w["a(i,1,ir) = 0.d0"];
    w["enddo"];
    w["enddo"];
    w["do i1 = nhalf,n"];
    w[" do i = 1,l"];
    w[" do ir = 1,nr"];
    w[" a(i,2,ir) = 0.d0"];
    w[" enddo"];
    w[" enddo"];
    w[" do i2 = nhalf,n"];
    w["  do i = 1,l"];
    w["  do ir = 1,nr"];
    w["  a(i,3,ir) = 0.d0"];
    w["  enddo"];
    w["  enddo"];
    w["  do i3 = nhalf,n"];
    w["   do i = 1,l"];
    w["   do ir = 1,nr"];
    w["   a(i,4,ir) = 0.d0"];
    w["   enddo"];
    w["   enddo"];
    w["   do i4 = nhalf,n"];
    w["    s2sq1 = (s22(i1)+s22(i2)+s22(i3)+s22(i4))"];
    w["    sisq1 = (si2(i1)+si2(i2)+si2(i3)+si2(i4))"];
    If[!FreeQ[expr,c2sq1],
       w["    c2sq1 = (c22(i1)+c22(i2)+c22(i3)+c22(i4))"]];
    If[!FreeQ[expr,cisq1],
       w["    cisq1 = (ci2(i1)+ci2(i2)+ci2(i3)+ci2(i4))"]];
    If[!FreeQ[expr,s2qu1] || !FreeQ[expr,dprop1] || !FreeQ[expr,prop1],
       w["    s2qu1 = (s24(i1)+s24(i2)+s24(i3)+s24(i4))"]];
    If[!FreeQ[expr,dprop1] || !FreeQ[expr,prop1],
       w["    k2p1  =    4* (s22(i1)+s22(i2)+s22(i3)+s22(i4))"];
       w["    k4p1  =   16* (s24(i1)+s24(i2)+s24(i3)+s24(i4))"]];
    w["    if (s2sq1.gt.1e-9) then"];
    If[!FreeQ[proplist,hat1]   || !FreeQ[expr,hat1] || 
       !FreeQ[proplist,dprop1] || !FreeQ[expr,dprop1] || 
       !FreeQ[proplist,prop1]  || !FreeQ[expr,prop1],
       w["    hat1 = 0.25d0/s2sq1"]];
    w["    do ir = 1,nr"];
    If[!FreeQ[proplist,fhat1] || !FreeQ[expr,fhat1],
       w["     m1(ir) = m(ir) + r12(ir)*s2sq1"];
       w["     fhat1(ir) = 1.d0/(m1(ir)**2 + sisq1)"]];
    If[!FreeQ[expr,dprop1] || !FreeQ[expr,prop1],
       w["     dummy = (1-cc1(ir)*k2p1)"];
       w["     do mu = 1, 4"];
       w["      if (mu.eq.1) imu = i1"];
       w["      if (mu.eq.2) imu = i2"];
       w["      if (mu.eq.3) imu = i3"];
       w["      if (mu.eq.4) imu = i4"];
       w["      do nu = 1, mu"];
       w["       if (nu.eq.1) inu = i1"];
       w["       if (nu.eq.2) inu = i2"];
       w["       if (nu.eq.3) inu = i3"];
       w["       if (nu.eq.4) inu = i4"];
       w["       g(mu,nu) = (1-dummy) * (2*s2(imu))*(2*s2(inu))"];
       wc["       + cc2(ir) *(2*s2(imu))**3*(2*s2(inu))"];
       wc["       + cc2(ir) *(2*s2(imu))*(2*s2(inu))**3"];
       w["       if (mu.eq.nu) g(mu,nu) = g(mu,nu) + dummy * k2p1"];
       wc["       - cc2(ir) * k4p1 - cc2(ir) * k2p1 * (2*s2(imu))**2"];
       w["       if (nu.lt.mu) g(nu,mu) = g(mu,nu)"];
       w["      enddo"];
       w["     enddo"];
       w["     do mu = 1,4"];
       w["      do nu = 1,4"];
       w["       ginv(mu,nu) = 0.d0"];
       w["      enddo"];
       w["      ginv(mu,mu) = 1.d0"];
       w["     enddo"];
       w["     call ludcmp(g,4,4,indx,d)"];
       w["     do nu = 1, 4"];
       w["      call lubksb(g,4,4,indx,ginv(1,nu))"];
       w["     enddo"];
       w["     do mu = 1, 4"];
       w["      do nu = 1, mu"];
       w["       prop1(mu,nu)  = ginv(mu,nu)"];
       w["       dprop1(mu,nu) = ginv(mu,nu)"];
       w["       if (mu.eq.nu) dprop1(mu,nu) = dprop1(mu,nu) - hat1"];
       w["       if (nu.lt.mu) prop1(nu,mu)  = prop1(mu,nu)"];
       w["       if (nu.lt.mu) dprop1(nu,mu) = dprop1(mu,nu)"];
       w["      enddo"];
       w["     enddo"]];
    If[!FreeQ[expr,s2sqinv1],
       w["     s2sqinv1 = 1.d0/s2sq1"]];
    If[(!FreeQ[expr,mo1])||(!FreeQ[expr,omegao1])||(!FreeQ[expr,omegaplusinvo1])||
       (!FreeQ[expr,omegainvo1])||(!FreeQ[expr,omegabo1])||(!FreeQ[expr,omegabinvo1]),
       w["     mo1(ir) = m(ir) - r12(ir)*s2sq1"];
       w["     omegao1(ir) = sqrt(sisq1 + mo1(ir)**2)"];
       w["     omegainvo1(ir) = 1.d0/omegao1(ir)"];
       w["     omegaplusinvo1(ir) = 1.d0/(omegao1(ir)+ m(ir))"];
       w["     omegabo1(ir) = (omegao1(ir)-mo1(ir))"];
       w["     omegabinvo1(ir) = 1.d0/omegabo1(ir)"]];
    w["     prop = ", proplist[[1]]];
    w["    if (i4.eq.n .or. (i4.eq.nhalf .and. nmod2.eq.0))"];
    wc["        prop = 0.5d0 * prop"];
    Do[If[expr4[[j,1]]===FortranForm[1],
          w["a(",j,",4,ir) = a(",j,",4,ir) + prop"],
          w["a(",j,",4,ir) = a(",j,",4,ir) + prop*"];
          wc["  ",expr4[[j,1]]]],
       {j,Length[expr4]}];
    w["    enddo"];
    w["    endif"];
    w["   enddo"];
    w["   if (i3.eq.n .or. (i3.eq.nhalf .and. nmod2.eq.0)) then"];
    w["    do ir = 1,nr"];
    w["    do i = 1,l"];
    w["    a(i,4,ir) = a(i,4,ir) * 0.5d0"];
    w["    enddo"];
    w["    enddo"];
    w["   endif"];
    w["   do ir = 1,nr"];
    Do[If[expr3[[j,1]]===FortranForm[1],
          w["a(",j,",3,ir) = a(",j,",3,ir) + a(",index3[[j]],",4,ir)"],
          w["a(",j,",3,ir) = a(",j,",3,ir) + a(",index3[[j]],",4,ir)*"];
          wc["  ",expr3[[j,1]]]],
       {j,Length[expr3]}];
    w["   enddo"];
    w["  enddo"];
    w["  if (i2.eq.n .or. (i2.eq.nhalf .and. nmod2.eq.0)) then"];
    w["   do ir = 1,nr"];
    w["   do i = 1,l"];
    w["   a(i,3,ir) = a(i,3,ir) * 0.5d0"];
    w["   enddo"];
    w["   enddo"];
    w["  endif"];
    w["  do ir = 1,nr"];
    Do[If[expr2[[j,1]]===FortranForm[1],
          w["a(",j,",2,ir) = a(",j,",2,ir) + a(",index2[[j]],",3,ir)"],
          w["a(",j,",2,ir) = a(",j,",2,ir) + a(",index2[[j]],",3,ir)*"];
          wc["  ",expr2[[j,1]]]],
       {j,Length[expr2]}];
    w["  enddo"];
    w[" enddo"];
    w[" if (i1.eq.n .or. (i1.eq.nhalf .and. nmod2.eq.0)) then"];
    w["  do ir = 1,nr"];
    w["  do i = 1,l"];
    w["  a(i,2,ir) = a(i,2,ir) * 0.5d0"];
    w["  enddo"];
    w["  enddo"];
    w[" endif"];
    w[" do ir = 1,nr"];
    Do[If[expr[[j,1]]===FortranForm[1],
          w["a(",j,",1,ir) = a(",j,",1,ir) + a(",index1[[j]],",2,ir)"],
          w["a(",j,",1,ir) = a(",j,",1,ir) + a(",index1[[j]],",2,ir)*"];
          wc["  ",expr[[j,1]]]],
       {j,Length[expr]}];
    w[" enddo"];
    w["enddo"];
    w["do ir = 1,nr"];
    Do[w["result(",k,") = 0.d0"];
       Do[If[!(factorlist[[j,k]] === FortranForm[0]),
             w["result(",k,") = result(",k,") + a(",j,",1,ir) * "];
             wc["(",N[factorlist[[j,k]],16],")"]],
          {j,Length[expr]}];
       w["result(",k,") = result(",k,") * 2**4 / float(n)**4"],
       {k,varlength}];
    w[" write(*,1001) n,r(ir), m(ir),"];
    wc["    z0(ir), z1(ir), z2(ir), z3(ir), result"];
    w["enddo"];
    w["call flush(6)"];
    WriteString[ToString[file], " 1000 ", "continue", "\n"];
    w["stop"];
    WriteString[ToString[file], " 1001 ", 
     "format(I4,6(1X,F10.7),100(/,1X,E30.18E2,1X,E30.18E2,1X,E30.18E2))", "\n"];
    w["end"];

  ]
