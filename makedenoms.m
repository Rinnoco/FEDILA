(* The function "makedenoms" introduces the object "denoms".
   denoms[a,b,l,m,n] = hat2[p[1]]^a*hat2[-p[1]+q[1]]^b*
                                 hat2[-p[1]+p[2]]^l*hat2[p[2]]^m*
                                 hat2[-p[2]+q[1]]^n .              *)


makedenoms[expr_Plus]:= makedenoms /@ expr
makedenoms[expr_Times]:= makedenoms1[Select[expr,!FreeQ[#,hat2]&]]*Select[expr,FreeQ[#,hat2]&]
makedenoms[expr_]:= makedenoms1[expr] /; !FreeQ[expr,hat2]
makedenoms[expr_]:= expr
makedenoms1[expr_]:= ((expr*denoms[0,0,0,0,0]) /.
  hat2[p[1]]^i_. denoms[a_,b_,l_,m_,n_] :> denoms[a+i,b,l,m,n] /.
  hat2[p[2]]^i_. denoms[a_,b_,l_,m_,n_] :> denoms[a,b,l,m+i,n] /.
  hat2[-p[1]+p[2]]^i_. denoms[a_,b_,l_,m_,n_] :> denoms[a,b,l+i,m,n] /.
  hat2[-p[1]+q[1]]^i_. denoms[a_,b_,l_,m_,n_] :> denoms[a,b+i,l,m,n] /.
  hat2[-p[2]+q[1]]^i_. denoms[a_,b_,l_,m_,n_] :> denoms[a,b,l,m,n+i])

unmakedenoms[expr_]:= expr /. denoms[a1_,a2_,a3_,a4_,a5_] :> hat2[p[1]]^a1 hat2[-p[1]+q[1]]^a2 hat2[-p[1]+p[2]]^a3 hat2[p[2]]^a4 hat2[-p[2]+q[1]]^a5


denomsZerosRules = {denoms[0,0,_,_,_]->0, denoms[0,_,_,0,_]->0,denoms[_,0,_,_,0]->0,denoms[_,_,_,0,0]->0,denoms[0,_,0,_,_]->0,denoms[_,0,0,_,_]->0,denoms[_,_,0,0,_]->0,denoms[_,_,0,_,0]->0};
