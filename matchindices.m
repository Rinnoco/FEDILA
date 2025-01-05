(* This function takes an integrand with propagators INDEPENDENT of external momenta,
   and matches the directions of sines, so as to lead to an even integrand under
   p[i] -> -p[i] 
   Aside from a prefactor, the numerator is a sum of terms, where each term may be 
   a function of p's times a function of external momenta                          *)

matchindices[expr_Plus]:= matchindices /@ expr

matchindices[expr_Times]:= Select[expr,FreeQ[#,s2]&] * 
                                matchindices[Select[expr,!(FreeQ[#,s2])&]] /;
                           Apply[Or, (FreeQ[#1, s2]&) /@ Apply[List, expr]]

matchindices[expr_Times]:= Select[expr,FreeQ[#,p]&] * 
                                matchindices[Select[expr,!(FreeQ[#,p])&]] /;
                           Apply[Or, (FreeQ[#1, p]&) /@ Apply[List, expr]]

matchindices[a_. s2[b_,c_]^i_] := s2[b,c]^2 matchindices[a s2[b,c]^(i-2)]

matchindices[expr_] := expr /; FreeQ[expr,s2] || FreeQ[expr,p]

matchindices[a_. s2[b_,c_] s2[d_,c_]] := s2[b,c] s2[d,c] matchindices[a]

matchindices[s2[a_,b_]] =0

matchindices[s2[a_,b_] s2[c_,d_] s2[e_,f_]] =0
  
matchindices[s2[a_,b_] s2[c_,d_] s2[e_,f_] s2[g_,h_] s2[i_,j_]] =0
  
matchindices[s2[a_,_] s2[c_,_] s2[e_,_] s2[g_,_] s2[i_,_] s2[k_,_] s2[m_,_]] =0
  
matchindices[s2[a_,_] s2[c_,_] s2[e_,_] s2[g_,_] s2[i_,_] s2[k_,_] s2[m_,_] s2[o_,_] s2[q_,_]] =0
  
matchindices[s2[a_,b_] s2[c_,d_]] := s2[a,b] s2[c,b] delm[b,d]

matchindices[s2[a_,b_] s2[c_,d_] s2[e_,f_] s2[g_,h_]] :=
   s2[a,b] s2[c,d] s2[e,f] s2[g,h] * 
   (delm[b,d]*delm[f,h] + delm[b,f]*delm[d,h] + delm[b,h]*delm[d,f] - 2*delm[b,d,f,h])

matchindices[s2[a_,b_] s2[c_,d_] s2[e_,f_] s2[g_,h_] s2[i_,j_] s2[k_,l_]] :=
   s2[a,b] s2[c,d] s2[e,f] s2[g,h] s2[i,j] s2[k,l] * 
   (delm[b,d]*delm[f,h]*delm[j,l] + 
    delm[b,d]*delm[f,j]*delm[h,l] + 
    delm[b,d]*delm[f,l]*delm[j,h] + 
    delm[b,f]*delm[d,h]*delm[j,l] + 
    delm[b,f]*delm[d,j]*delm[h,l] + 
    delm[b,f]*delm[d,l]*delm[j,h] + 
    delm[b,h]*delm[d,f]*delm[j,l] + 
    delm[b,h]*delm[d,j]*delm[f,l] + 
    delm[b,h]*delm[d,l]*delm[j,f] + 
    delm[b,j]*delm[d,f]*delm[h,l] + 
    delm[b,j]*delm[d,h]*delm[f,l] + 
    delm[b,j]*delm[d,l]*delm[f,h] + 
    delm[b,l]*delm[d,f]*delm[h,j] + 
    delm[b,l]*delm[d,h]*delm[f,j] + 
    delm[b,l]*delm[d,j]*delm[f,h] 
    - 2*delm[b,d,f,h]*delm[j,l]
    - 2*delm[b,d,f,j]*delm[h,l]
    - 2*delm[b,d,h,j]*delm[f,l]
    - 2*delm[b,f,h,j]*delm[d,l]
    - 2*delm[d,f,h,j]*delm[b,l]
    - 2*delm[b,d,f,l]*delm[h,j]
    - 2*delm[b,d,h,l]*delm[f,j]
    - 2*delm[b,f,h,l]*delm[d,j]
    - 2*delm[d,f,h,l]*delm[b,j]
    - 2*delm[b,d,j,l]*delm[f,h]
    - 2*delm[b,f,j,l]*delm[d,h]
    - 2*delm[d,f,j,l]*delm[b,h]
    - 2*delm[b,h,j,l]*delm[d,f]
    - 2*delm[d,h,j,l]*delm[b,f]
    - 2*delm[f,h,j,l]*delm[b,d]
    + 16 delm[b,d,f,h,j,l]
   )

matchindices[s2[a_,r1_]s2[b_,r2_]s2[c_,r3_]s2[d_,r4_]s2[e_,r5_]s2[f_,r6_]s2[g_,r7_]s2[h_,r8_]] :=
   s2[a,r1]s2[b,r2]s2[c,r3]s2[d,r4]s2[e,r5]s2[f,r6]s2[g,r7]s2[h,r8] * 
Plus @@ ({delm[r1, r8]*delm[r2, r7]*delm[r3, r6]*delm[r4, r5] + 
  delm[r1, r7]*delm[r2, r8]*delm[r3, r6]*delm[r4, r5] + 
  delm[r1, r8]*delm[r2, r6]*delm[r3, r7]*delm[r4, r5] + 
  delm[r1, r6]*delm[r2, r8]*delm[r3, r7]*delm[r4, r5] + 
  delm[r1, r7]*delm[r2, r6]*delm[r3, r8]*delm[r4, r5] + 
  delm[r1, r6]*delm[r2, r7]*delm[r3, r8]*delm[r4, r5] + 
  delm[r1, r8]*delm[r2, r7]*delm[r3, r5]*delm[r4, r6] + 
  delm[r1, r7]*delm[r2, r8]*delm[r3, r5]*delm[r4, r6] + 
  delm[r1, r8]*delm[r2, r5]*delm[r3, r7]*delm[r4, r6] + 
  delm[r1, r5]*delm[r2, r8]*delm[r3, r7]*delm[r4, r6] + 
  delm[r1, r7]*delm[r2, r5]*delm[r3, r8]*delm[r4, r6] + 
  delm[r1, r5]*delm[r2, r7]*delm[r3, r8]*delm[r4, r6] + 
  delm[r1, r8]*delm[r2, r6]*delm[r3, r5]*delm[r4, r7] + 
  delm[r1, r6]*delm[r2, r8]*delm[r3, r5]*delm[r4, r7] + 
  delm[r1, r8]*delm[r2, r5]*delm[r3, r6]*delm[r4, r7] + 
  delm[r1, r5]*delm[r2, r8]*delm[r3, r6]*delm[r4, r7] + 
  delm[r1, r6]*delm[r2, r5]*delm[r3, r8]*delm[r4, r7] + 
  delm[r1, r5]*delm[r2, r6]*delm[r3, r8]*delm[r4, r7] + 
  delm[r1, r7]*delm[r2, r6]*delm[r3, r5]*delm[r4, r8] + 
  delm[r1, r6]*delm[r2, r7]*delm[r3, r5]*delm[r4, r8] + 
  delm[r1, r7]*delm[r2, r5]*delm[r3, r6]*delm[r4, r8] + 
  delm[r1, r5]*delm[r2, r7]*delm[r3, r6]*delm[r4, r8] + 
  delm[r1, r6]*delm[r2, r5]*delm[r3, r7]*delm[r4, r8] + 
  delm[r1, r5]*delm[r2, r6]*delm[r3, r7]*delm[r4, r8] + 
  delm[r1, r8]*delm[r2, r7]*delm[r3, r4]*delm[r5, r6] + 
  delm[r1, r7]*delm[r2, r8]*delm[r3, r4]*delm[r5, r6] + 
  delm[r1, r8]*delm[r2, r4]*delm[r3, r7]*delm[r5, r6] + 
  delm[r1, r4]*delm[r2, r8]*delm[r3, r7]*delm[r5, r6] + 
  delm[r1, r7]*delm[r2, r4]*delm[r3, r8]*delm[r5, r6] + 
  delm[r1, r4]*delm[r2, r7]*delm[r3, r8]*delm[r5, r6] + 
  delm[r1, r8]*delm[r2, r3]*delm[r4, r7]*delm[r5, r6] + 
  delm[r1, r3]*delm[r2, r8]*delm[r4, r7]*delm[r5, r6] + 
  delm[r1, r2]*delm[r3, r8]*delm[r4, r7]*delm[r5, r6] + 
  delm[r1, r7]*delm[r2, r3]*delm[r4, r8]*delm[r5, r6] + 
  delm[r1, r3]*delm[r2, r7]*delm[r4, r8]*delm[r5, r6] + 
  delm[r1, r2]*delm[r3, r7]*delm[r4, r8]*delm[r5, r6] + 
  delm[r1, r8]*delm[r2, r6]*delm[r3, r4]*delm[r5, r7] + 
  delm[r1, r6]*delm[r2, r8]*delm[r3, r4]*delm[r5, r7] + 
  delm[r1, r8]*delm[r2, r4]*delm[r3, r6]*delm[r5, r7] + 
  delm[r1, r4]*delm[r2, r8]*delm[r3, r6]*delm[r5, r7] + 
  delm[r1, r6]*delm[r2, r4]*delm[r3, r8]*delm[r5, r7] + 
  delm[r1, r4]*delm[r2, r6]*delm[r3, r8]*delm[r5, r7] + 
  delm[r1, r8]*delm[r2, r3]*delm[r4, r6]*delm[r5, r7] + 
  delm[r1, r3]*delm[r2, r8]*delm[r4, r6]*delm[r5, r7] + 
  delm[r1, r2]*delm[r3, r8]*delm[r4, r6]*delm[r5, r7] + 
  delm[r1, r6]*delm[r2, r3]*delm[r4, r8]*delm[r5, r7] + 
  delm[r1, r3]*delm[r2, r6]*delm[r4, r8]*delm[r5, r7] + 
  delm[r1, r2]*delm[r3, r6]*delm[r4, r8]*delm[r5, r7] + 
  delm[r1, r7]*delm[r2, r6]*delm[r3, r4]*delm[r5, r8] + 
  delm[r1, r6]*delm[r2, r7]*delm[r3, r4]*delm[r5, r8] + 
  delm[r1, r7]*delm[r2, r4]*delm[r3, r6]*delm[r5, r8] + 
  delm[r1, r4]*delm[r2, r7]*delm[r3, r6]*delm[r5, r8] + 
  delm[r1, r6]*delm[r2, r4]*delm[r3, r7]*delm[r5, r8] + 
  delm[r1, r4]*delm[r2, r6]*delm[r3, r7]*delm[r5, r8] + 
  delm[r1, r7]*delm[r2, r3]*delm[r4, r6]*delm[r5, r8] + 
  delm[r1, r3]*delm[r2, r7]*delm[r4, r6]*delm[r5, r8] + 
  delm[r1, r2]*delm[r3, r7]*delm[r4, r6]*delm[r5, r8] + 
  delm[r1, r6]*delm[r2, r3]*delm[r4, r7]*delm[r5, r8] + 
  delm[r1, r3]*delm[r2, r6]*delm[r4, r7]*delm[r5, r8] + 
  delm[r1, r2]*delm[r3, r6]*delm[r4, r7]*delm[r5, r8] + 
  delm[r1, r8]*delm[r2, r5]*delm[r3, r4]*delm[r6, r7] + 
  delm[r1, r5]*delm[r2, r8]*delm[r3, r4]*delm[r6, r7] + 
  delm[r1, r8]*delm[r2, r4]*delm[r3, r5]*delm[r6, r7] + 
  delm[r1, r4]*delm[r2, r8]*delm[r3, r5]*delm[r6, r7] + 
  delm[r1, r5]*delm[r2, r4]*delm[r3, r8]*delm[r6, r7] + 
  delm[r1, r4]*delm[r2, r5]*delm[r3, r8]*delm[r6, r7] + 
  delm[r1, r8]*delm[r2, r3]*delm[r4, r5]*delm[r6, r7] + 
  delm[r1, r3]*delm[r2, r8]*delm[r4, r5]*delm[r6, r7] + 
  delm[r1, r2]*delm[r3, r8]*delm[r4, r5]*delm[r6, r7] + 
  delm[r1, r5]*delm[r2, r3]*delm[r4, r8]*delm[r6, r7] + 
  delm[r1, r3]*delm[r2, r5]*delm[r4, r8]*delm[r6, r7] + 
  delm[r1, r2]*delm[r3, r5]*delm[r4, r8]*delm[r6, r7] + 
  delm[r1, r4]*delm[r2, r3]*delm[r5, r8]*delm[r6, r7] + 
  delm[r1, r3]*delm[r2, r4]*delm[r5, r8]*delm[r6, r7] + 
  delm[r1, r2]*delm[r3, r4]*delm[r5, r8]*delm[r6, r7] + 
  delm[r1, r7]*delm[r2, r5]*delm[r3, r4]*delm[r6, r8] + 
  delm[r1, r5]*delm[r2, r7]*delm[r3, r4]*delm[r6, r8] + 
  delm[r1, r7]*delm[r2, r4]*delm[r3, r5]*delm[r6, r8] + 
  delm[r1, r4]*delm[r2, r7]*delm[r3, r5]*delm[r6, r8] + 
  delm[r1, r5]*delm[r2, r4]*delm[r3, r7]*delm[r6, r8] + 
  delm[r1, r4]*delm[r2, r5]*delm[r3, r7]*delm[r6, r8] + 
  delm[r1, r7]*delm[r2, r3]*delm[r4, r5]*delm[r6, r8] + 
  delm[r1, r3]*delm[r2, r7]*delm[r4, r5]*delm[r6, r8] + 
  delm[r1, r2]*delm[r3, r7]*delm[r4, r5]*delm[r6, r8] + 
  delm[r1, r5]*delm[r2, r3]*delm[r4, r7]*delm[r6, r8] + 
  delm[r1, r3]*delm[r2, r5]*delm[r4, r7]*delm[r6, r8] + 
  delm[r1, r2]*delm[r3, r5]*delm[r4, r7]*delm[r6, r8] + 
  delm[r1, r4]*delm[r2, r3]*delm[r5, r7]*delm[r6, r8] + 
  delm[r1, r3]*delm[r2, r4]*delm[r5, r7]*delm[r6, r8] + 
  delm[r1, r2]*delm[r3, r4]*delm[r5, r7]*delm[r6, r8] + 
  delm[r1, r6]*delm[r2, r5]*delm[r3, r4]*delm[r7, r8] + 
  delm[r1, r5]*delm[r2, r6]*delm[r3, r4]*delm[r7, r8] + 
  delm[r1, r6]*delm[r2, r4]*delm[r3, r5]*delm[r7, r8] + 
  delm[r1, r4]*delm[r2, r6]*delm[r3, r5]*delm[r7, r8] + 
  delm[r1, r5]*delm[r2, r4]*delm[r3, r6]*delm[r7, r8] + 
  delm[r1, r4]*delm[r2, r5]*delm[r3, r6]*delm[r7, r8] + 
  delm[r1, r6]*delm[r2, r3]*delm[r4, r5]*delm[r7, r8] + 
  delm[r1, r3]*delm[r2, r6]*delm[r4, r5]*delm[r7, r8] + 
  delm[r1, r2]*delm[r3, r6]*delm[r4, r5]*delm[r7, r8] + 
  delm[r1, r5]*delm[r2, r3]*delm[r4, r6]*delm[r7, r8] + 
  delm[r1, r3]*delm[r2, r5]*delm[r4, r6]*delm[r7, r8] + 
  delm[r1, r2]*delm[r3, r5]*delm[r4, r6]*delm[r7, r8] + 
  delm[r1, r4]*delm[r2, r3]*delm[r5, r6]*delm[r7, r8] + 
  delm[r1, r3]*delm[r2, r4]*delm[r5, r6]*delm[r7, r8] + 
  delm[r1, r2]*delm[r3, r4]*delm[r5, r6]*delm[r7, r8], 
 delm[r5, r8]*delm[r6, r7]*delm[r1, r2, r3, r4] + 
  delm[r5, r7]*delm[r6, r8]*delm[r1, r2, r3, r4] + 
  delm[r5, r6]*delm[r7, r8]*delm[r1, r2, r3, r4] + 
  delm[r4, r8]*delm[r6, r7]*delm[r1, r2, r3, r5] + 
  delm[r4, r7]*delm[r6, r8]*delm[r1, r2, r3, r5] + 
  delm[r4, r6]*delm[r7, r8]*delm[r1, r2, r3, r5] + 
  delm[r4, r8]*delm[r5, r7]*delm[r1, r2, r3, r6] + 
  delm[r4, r7]*delm[r5, r8]*delm[r1, r2, r3, r6] + 
  delm[r4, r5]*delm[r7, r8]*delm[r1, r2, r3, r6] + 
  delm[r4, r8]*delm[r5, r6]*delm[r1, r2, r3, r7] + 
  delm[r4, r6]*delm[r5, r8]*delm[r1, r2, r3, r7] + 
  delm[r4, r5]*delm[r6, r8]*delm[r1, r2, r3, r7] + 
  delm[r4, r7]*delm[r5, r6]*delm[r1, r2, r3, r8] + 
  delm[r4, r6]*delm[r5, r7]*delm[r1, r2, r3, r8] + 
  delm[r4, r5]*delm[r6, r7]*delm[r1, r2, r3, r8] + 
  delm[r3, r8]*delm[r6, r7]*delm[r1, r2, r4, r5] + 
  delm[r3, r7]*delm[r6, r8]*delm[r1, r2, r4, r5] + 
  delm[r3, r6]*delm[r7, r8]*delm[r1, r2, r4, r5] + 
  delm[r3, r8]*delm[r5, r7]*delm[r1, r2, r4, r6] + 
  delm[r3, r7]*delm[r5, r8]*delm[r1, r2, r4, r6] + 
  delm[r3, r5]*delm[r7, r8]*delm[r1, r2, r4, r6] + 
  delm[r3, r8]*delm[r5, r6]*delm[r1, r2, r4, r7] + 
  delm[r3, r6]*delm[r5, r8]*delm[r1, r2, r4, r7] + 
  delm[r3, r5]*delm[r6, r8]*delm[r1, r2, r4, r7] + 
  delm[r3, r7]*delm[r5, r6]*delm[r1, r2, r4, r8] + 
  delm[r3, r6]*delm[r5, r7]*delm[r1, r2, r4, r8] + 
  delm[r3, r5]*delm[r6, r7]*delm[r1, r2, r4, r8] + 
  delm[r3, r8]*delm[r4, r7]*delm[r1, r2, r5, r6] + 
  delm[r3, r7]*delm[r4, r8]*delm[r1, r2, r5, r6] + 
  delm[r3, r4]*delm[r7, r8]*delm[r1, r2, r5, r6] + 
  delm[r3, r8]*delm[r4, r6]*delm[r1, r2, r5, r7] + 
  delm[r3, r6]*delm[r4, r8]*delm[r1, r2, r5, r7] + 
  delm[r3, r4]*delm[r6, r8]*delm[r1, r2, r5, r7] + 
  delm[r3, r7]*delm[r4, r6]*delm[r1, r2, r5, r8] + 
  delm[r3, r6]*delm[r4, r7]*delm[r1, r2, r5, r8] + 
  delm[r3, r4]*delm[r6, r7]*delm[r1, r2, r5, r8] + 
  delm[r3, r8]*delm[r4, r5]*delm[r1, r2, r6, r7] + 
  delm[r3, r5]*delm[r4, r8]*delm[r1, r2, r6, r7] + 
  delm[r3, r4]*delm[r5, r8]*delm[r1, r2, r6, r7] + 
  delm[r3, r7]*delm[r4, r5]*delm[r1, r2, r6, r8] + 
  delm[r3, r5]*delm[r4, r7]*delm[r1, r2, r6, r8] + 
  delm[r3, r4]*delm[r5, r7]*delm[r1, r2, r6, r8] + 
  delm[r3, r6]*delm[r4, r5]*delm[r1, r2, r7, r8] + 
  delm[r3, r5]*delm[r4, r6]*delm[r1, r2, r7, r8] + 
  delm[r3, r4]*delm[r5, r6]*delm[r1, r2, r7, r8] + 
  delm[r2, r8]*delm[r6, r7]*delm[r1, r3, r4, r5] + 
  delm[r2, r7]*delm[r6, r8]*delm[r1, r3, r4, r5] + 
  delm[r2, r6]*delm[r7, r8]*delm[r1, r3, r4, r5] + 
  delm[r2, r8]*delm[r5, r7]*delm[r1, r3, r4, r6] + 
  delm[r2, r7]*delm[r5, r8]*delm[r1, r3, r4, r6] + 
  delm[r2, r5]*delm[r7, r8]*delm[r1, r3, r4, r6] + 
  delm[r2, r8]*delm[r5, r6]*delm[r1, r3, r4, r7] + 
  delm[r2, r6]*delm[r5, r8]*delm[r1, r3, r4, r7] + 
  delm[r2, r5]*delm[r6, r8]*delm[r1, r3, r4, r7] + 
  delm[r2, r7]*delm[r5, r6]*delm[r1, r3, r4, r8] + 
  delm[r2, r6]*delm[r5, r7]*delm[r1, r3, r4, r8] + 
  delm[r2, r5]*delm[r6, r7]*delm[r1, r3, r4, r8] + 
  delm[r2, r8]*delm[r4, r7]*delm[r1, r3, r5, r6] + 
  delm[r2, r7]*delm[r4, r8]*delm[r1, r3, r5, r6] + 
  delm[r2, r4]*delm[r7, r8]*delm[r1, r3, r5, r6] + 
  delm[r2, r8]*delm[r4, r6]*delm[r1, r3, r5, r7] + 
  delm[r2, r6]*delm[r4, r8]*delm[r1, r3, r5, r7] + 
  delm[r2, r4]*delm[r6, r8]*delm[r1, r3, r5, r7] + 
  delm[r2, r7]*delm[r4, r6]*delm[r1, r3, r5, r8] + 
  delm[r2, r6]*delm[r4, r7]*delm[r1, r3, r5, r8] + 
  delm[r2, r4]*delm[r6, r7]*delm[r1, r3, r5, r8] + 
  delm[r2, r8]*delm[r4, r5]*delm[r1, r3, r6, r7] + 
  delm[r2, r5]*delm[r4, r8]*delm[r1, r3, r6, r7] + 
  delm[r2, r4]*delm[r5, r8]*delm[r1, r3, r6, r7] + 
  delm[r2, r7]*delm[r4, r5]*delm[r1, r3, r6, r8] + 
  delm[r2, r5]*delm[r4, r7]*delm[r1, r3, r6, r8] + 
  delm[r2, r4]*delm[r5, r7]*delm[r1, r3, r6, r8] + 
  delm[r2, r6]*delm[r4, r5]*delm[r1, r3, r7, r8] + 
  delm[r2, r5]*delm[r4, r6]*delm[r1, r3, r7, r8] + 
  delm[r2, r4]*delm[r5, r6]*delm[r1, r3, r7, r8] + 
  delm[r2, r8]*delm[r3, r7]*delm[r1, r4, r5, r6] + 
  delm[r2, r7]*delm[r3, r8]*delm[r1, r4, r5, r6] + 
  delm[r2, r3]*delm[r7, r8]*delm[r1, r4, r5, r6] + 
  delm[r2, r8]*delm[r3, r6]*delm[r1, r4, r5, r7] + 
  delm[r2, r6]*delm[r3, r8]*delm[r1, r4, r5, r7] + 
  delm[r2, r3]*delm[r6, r8]*delm[r1, r4, r5, r7] + 
  delm[r2, r7]*delm[r3, r6]*delm[r1, r4, r5, r8] + 
  delm[r2, r6]*delm[r3, r7]*delm[r1, r4, r5, r8] + 
  delm[r2, r3]*delm[r6, r7]*delm[r1, r4, r5, r8] + 
  delm[r2, r8]*delm[r3, r5]*delm[r1, r4, r6, r7] + 
  delm[r2, r5]*delm[r3, r8]*delm[r1, r4, r6, r7] + 
  delm[r2, r3]*delm[r5, r8]*delm[r1, r4, r6, r7] + 
  delm[r2, r7]*delm[r3, r5]*delm[r1, r4, r6, r8] + 
  delm[r2, r5]*delm[r3, r7]*delm[r1, r4, r6, r8] + 
  delm[r2, r3]*delm[r5, r7]*delm[r1, r4, r6, r8] + 
  delm[r2, r6]*delm[r3, r5]*delm[r1, r4, r7, r8] + 
  delm[r2, r5]*delm[r3, r6]*delm[r1, r4, r7, r8] + 
  delm[r2, r3]*delm[r5, r6]*delm[r1, r4, r7, r8] + 
  delm[r2, r8]*delm[r3, r4]*delm[r1, r5, r6, r7] + 
  delm[r2, r4]*delm[r3, r8]*delm[r1, r5, r6, r7] + 
  delm[r2, r3]*delm[r4, r8]*delm[r1, r5, r6, r7] + 
  delm[r2, r7]*delm[r3, r4]*delm[r1, r5, r6, r8] + 
  delm[r2, r4]*delm[r3, r7]*delm[r1, r5, r6, r8] + 
  delm[r2, r3]*delm[r4, r7]*delm[r1, r5, r6, r8] + 
  delm[r2, r6]*delm[r3, r4]*delm[r1, r5, r7, r8] + 
  delm[r2, r4]*delm[r3, r6]*delm[r1, r5, r7, r8] + 
  delm[r2, r3]*delm[r4, r6]*delm[r1, r5, r7, r8] + 
  delm[r2, r5]*delm[r3, r4]*delm[r1, r6, r7, r8] + 
  delm[r2, r4]*delm[r3, r5]*delm[r1, r6, r7, r8] + 
  delm[r2, r3]*delm[r4, r5]*delm[r1, r6, r7, r8] + 
  delm[r1, r8]*delm[r6, r7]*delm[r2, r3, r4, r5] + 
  delm[r1, r7]*delm[r6, r8]*delm[r2, r3, r4, r5] + 
  delm[r1, r6]*delm[r7, r8]*delm[r2, r3, r4, r5] + 
  delm[r1, r8]*delm[r5, r7]*delm[r2, r3, r4, r6] + 
  delm[r1, r7]*delm[r5, r8]*delm[r2, r3, r4, r6] + 
  delm[r1, r5]*delm[r7, r8]*delm[r2, r3, r4, r6] + 
  delm[r1, r8]*delm[r5, r6]*delm[r2, r3, r4, r7] + 
  delm[r1, r6]*delm[r5, r8]*delm[r2, r3, r4, r7] + 
  delm[r1, r5]*delm[r6, r8]*delm[r2, r3, r4, r7] + 
  delm[r1, r7]*delm[r5, r6]*delm[r2, r3, r4, r8] + 
  delm[r1, r6]*delm[r5, r7]*delm[r2, r3, r4, r8] + 
  delm[r1, r5]*delm[r6, r7]*delm[r2, r3, r4, r8] + 
  delm[r1, r8]*delm[r4, r7]*delm[r2, r3, r5, r6] + 
  delm[r1, r7]*delm[r4, r8]*delm[r2, r3, r5, r6] + 
  delm[r1, r4]*delm[r7, r8]*delm[r2, r3, r5, r6] + 
  delm[r1, r8]*delm[r4, r6]*delm[r2, r3, r5, r7] + 
  delm[r1, r6]*delm[r4, r8]*delm[r2, r3, r5, r7] + 
  delm[r1, r4]*delm[r6, r8]*delm[r2, r3, r5, r7] + 
  delm[r1, r7]*delm[r4, r6]*delm[r2, r3, r5, r8] + 
  delm[r1, r6]*delm[r4, r7]*delm[r2, r3, r5, r8] + 
  delm[r1, r4]*delm[r6, r7]*delm[r2, r3, r5, r8] + 
  delm[r1, r8]*delm[r4, r5]*delm[r2, r3, r6, r7] + 
  delm[r1, r5]*delm[r4, r8]*delm[r2, r3, r6, r7] + 
  delm[r1, r4]*delm[r5, r8]*delm[r2, r3, r6, r7] + 
  delm[r1, r7]*delm[r4, r5]*delm[r2, r3, r6, r8] + 
  delm[r1, r5]*delm[r4, r7]*delm[r2, r3, r6, r8] + 
  delm[r1, r4]*delm[r5, r7]*delm[r2, r3, r6, r8] + 
  delm[r1, r6]*delm[r4, r5]*delm[r2, r3, r7, r8] + 
  delm[r1, r5]*delm[r4, r6]*delm[r2, r3, r7, r8] + 
  delm[r1, r4]*delm[r5, r6]*delm[r2, r3, r7, r8] + 
  delm[r1, r8]*delm[r3, r7]*delm[r2, r4, r5, r6] + 
  delm[r1, r7]*delm[r3, r8]*delm[r2, r4, r5, r6] + 
  delm[r1, r3]*delm[r7, r8]*delm[r2, r4, r5, r6] + 
  delm[r1, r8]*delm[r3, r6]*delm[r2, r4, r5, r7] + 
  delm[r1, r6]*delm[r3, r8]*delm[r2, r4, r5, r7] + 
  delm[r1, r3]*delm[r6, r8]*delm[r2, r4, r5, r7] + 
  delm[r1, r7]*delm[r3, r6]*delm[r2, r4, r5, r8] + 
  delm[r1, r6]*delm[r3, r7]*delm[r2, r4, r5, r8] + 
  delm[r1, r3]*delm[r6, r7]*delm[r2, r4, r5, r8] + 
  delm[r1, r8]*delm[r3, r5]*delm[r2, r4, r6, r7] + 
  delm[r1, r5]*delm[r3, r8]*delm[r2, r4, r6, r7] + 
  delm[r1, r3]*delm[r5, r8]*delm[r2, r4, r6, r7] + 
  delm[r1, r7]*delm[r3, r5]*delm[r2, r4, r6, r8] + 
  delm[r1, r5]*delm[r3, r7]*delm[r2, r4, r6, r8] + 
  delm[r1, r3]*delm[r5, r7]*delm[r2, r4, r6, r8] + 
  delm[r1, r6]*delm[r3, r5]*delm[r2, r4, r7, r8] + 
  delm[r1, r5]*delm[r3, r6]*delm[r2, r4, r7, r8] + 
  delm[r1, r3]*delm[r5, r6]*delm[r2, r4, r7, r8] + 
  delm[r1, r8]*delm[r3, r4]*delm[r2, r5, r6, r7] + 
  delm[r1, r4]*delm[r3, r8]*delm[r2, r5, r6, r7] + 
  delm[r1, r3]*delm[r4, r8]*delm[r2, r5, r6, r7] + 
  delm[r1, r7]*delm[r3, r4]*delm[r2, r5, r6, r8] + 
  delm[r1, r4]*delm[r3, r7]*delm[r2, r5, r6, r8] + 
  delm[r1, r3]*delm[r4, r7]*delm[r2, r5, r6, r8] + 
  delm[r1, r6]*delm[r3, r4]*delm[r2, r5, r7, r8] + 
  delm[r1, r4]*delm[r3, r6]*delm[r2, r5, r7, r8] + 
  delm[r1, r3]*delm[r4, r6]*delm[r2, r5, r7, r8] + 
  delm[r1, r5]*delm[r3, r4]*delm[r2, r6, r7, r8] + 
  delm[r1, r4]*delm[r3, r5]*delm[r2, r6, r7, r8] + 
  delm[r1, r3]*delm[r4, r5]*delm[r2, r6, r7, r8] + 
  delm[r1, r8]*delm[r2, r7]*delm[r3, r4, r5, r6] + 
  delm[r1, r7]*delm[r2, r8]*delm[r3, r4, r5, r6] + 
  delm[r1, r2]*delm[r7, r8]*delm[r3, r4, r5, r6] + 
  delm[r1, r8]*delm[r2, r6]*delm[r3, r4, r5, r7] + 
  delm[r1, r6]*delm[r2, r8]*delm[r3, r4, r5, r7] + 
  delm[r1, r2]*delm[r6, r8]*delm[r3, r4, r5, r7] + 
  delm[r1, r7]*delm[r2, r6]*delm[r3, r4, r5, r8] + 
  delm[r1, r6]*delm[r2, r7]*delm[r3, r4, r5, r8] + 
  delm[r1, r2]*delm[r6, r7]*delm[r3, r4, r5, r8] + 
  delm[r1, r8]*delm[r2, r5]*delm[r3, r4, r6, r7] + 
  delm[r1, r5]*delm[r2, r8]*delm[r3, r4, r6, r7] + 
  delm[r1, r2]*delm[r5, r8]*delm[r3, r4, r6, r7] + 
  delm[r1, r7]*delm[r2, r5]*delm[r3, r4, r6, r8] + 
  delm[r1, r5]*delm[r2, r7]*delm[r3, r4, r6, r8] + 
  delm[r1, r2]*delm[r5, r7]*delm[r3, r4, r6, r8] + 
  delm[r1, r6]*delm[r2, r5]*delm[r3, r4, r7, r8] + 
  delm[r1, r5]*delm[r2, r6]*delm[r3, r4, r7, r8] + 
  delm[r1, r2]*delm[r5, r6]*delm[r3, r4, r7, r8] + 
  delm[r1, r8]*delm[r2, r4]*delm[r3, r5, r6, r7] + 
  delm[r1, r4]*delm[r2, r8]*delm[r3, r5, r6, r7] + 
  delm[r1, r2]*delm[r4, r8]*delm[r3, r5, r6, r7] + 
  delm[r1, r7]*delm[r2, r4]*delm[r3, r5, r6, r8] + 
  delm[r1, r4]*delm[r2, r7]*delm[r3, r5, r6, r8] + 
  delm[r1, r2]*delm[r4, r7]*delm[r3, r5, r6, r8] + 
  delm[r1, r6]*delm[r2, r4]*delm[r3, r5, r7, r8] + 
  delm[r1, r4]*delm[r2, r6]*delm[r3, r5, r7, r8] + 
  delm[r1, r2]*delm[r4, r6]*delm[r3, r5, r7, r8] + 
  delm[r1, r5]*delm[r2, r4]*delm[r3, r6, r7, r8] + 
  delm[r1, r4]*delm[r2, r5]*delm[r3, r6, r7, r8] + 
  delm[r1, r2]*delm[r4, r5]*delm[r3, r6, r7, r8] + 
  delm[r1, r8]*delm[r2, r3]*delm[r4, r5, r6, r7] + 
  delm[r1, r3]*delm[r2, r8]*delm[r4, r5, r6, r7] + 
  delm[r1, r2]*delm[r3, r8]*delm[r4, r5, r6, r7] + 
  delm[r1, r7]*delm[r2, r3]*delm[r4, r5, r6, r8] + 
  delm[r1, r3]*delm[r2, r7]*delm[r4, r5, r6, r8] + 
  delm[r1, r2]*delm[r3, r7]*delm[r4, r5, r6, r8] + 
  delm[r1, r6]*delm[r2, r3]*delm[r4, r5, r7, r8] + 
  delm[r1, r3]*delm[r2, r6]*delm[r4, r5, r7, r8] + 
  delm[r1, r2]*delm[r3, r6]*delm[r4, r5, r7, r8] + 
  delm[r1, r5]*delm[r2, r3]*delm[r4, r6, r7, r8] + 
  delm[r1, r3]*delm[r2, r5]*delm[r4, r6, r7, r8] + 
  delm[r1, r2]*delm[r3, r5]*delm[r4, r6, r7, r8] + 
  delm[r1, r4]*delm[r2, r3]*delm[r5, r6, r7, r8] + 
  delm[r1, r3]*delm[r2, r4]*delm[r5, r6, r7, r8] + 
  delm[r1, r2]*delm[r3, r4]*delm[r5, r6, r7, r8], 
 delm[r1, r6, r7, r8]*delm[r2, r3, r4, r5] + delm[r1, r5, r7, r8]*
   delm[r2, r3, r4, r6] + delm[r1, r5, r6, r8]*delm[r2, r3, r4, r7] + 
  delm[r1, r5, r6, r7]*delm[r2, r3, r4, r8] + 
  delm[r1, r4, r7, r8]*delm[r2, r3, r5, r6] + 
  delm[r1, r4, r6, r8]*delm[r2, r3, r5, r7] + 
  delm[r1, r4, r6, r7]*delm[r2, r3, r5, r8] + 
  delm[r1, r4, r5, r8]*delm[r2, r3, r6, r7] + 
  delm[r1, r4, r5, r7]*delm[r2, r3, r6, r8] + 
  delm[r1, r4, r5, r6]*delm[r2, r3, r7, r8] + 
  delm[r1, r3, r7, r8]*delm[r2, r4, r5, r6] + 
  delm[r1, r3, r6, r8]*delm[r2, r4, r5, r7] + 
  delm[r1, r3, r6, r7]*delm[r2, r4, r5, r8] + 
  delm[r1, r3, r5, r8]*delm[r2, r4, r6, r7] + 
  delm[r1, r3, r5, r7]*delm[r2, r4, r6, r8] + 
  delm[r1, r3, r5, r6]*delm[r2, r4, r7, r8] + 
  delm[r1, r3, r4, r8]*delm[r2, r5, r6, r7] + 
  delm[r1, r3, r4, r7]*delm[r2, r5, r6, r8] + 
  delm[r1, r3, r4, r6]*delm[r2, r5, r7, r8] + 
  delm[r1, r3, r4, r5]*delm[r2, r6, r7, r8] + 
  delm[r1, r2, r7, r8]*delm[r3, r4, r5, r6] + 
  delm[r1, r2, r6, r8]*delm[r3, r4, r5, r7] + 
  delm[r1, r2, r6, r7]*delm[r3, r4, r5, r8] + 
  delm[r1, r2, r5, r8]*delm[r3, r4, r6, r7] + 
  delm[r1, r2, r5, r7]*delm[r3, r4, r6, r8] + 
  delm[r1, r2, r5, r6]*delm[r3, r4, r7, r8] + 
  delm[r1, r2, r4, r8]*delm[r3, r5, r6, r7] + 
  delm[r1, r2, r4, r7]*delm[r3, r5, r6, r8] + 
  delm[r1, r2, r4, r6]*delm[r3, r5, r7, r8] + 
  delm[r1, r2, r4, r5]*delm[r3, r6, r7, r8] + 
  delm[r1, r2, r3, r8]*delm[r4, r5, r6, r7] + 
  delm[r1, r2, r3, r7]*delm[r4, r5, r6, r8] + 
  delm[r1, r2, r3, r6]*delm[r4, r5, r7, r8] + 
  delm[r1, r2, r3, r5]*delm[r4, r6, r7, r8] + 
  delm[r1, r2, r3, r4]*delm[r5, r6, r7, r8], 
 delm[r7, r8]*delm[r1, r2, r3, r4, r5, r6] + 
  delm[r6, r8]*delm[r1, r2, r3, r4, r5, r7] + 
  delm[r6, r7]*delm[r1, r2, r3, r4, r5, r8] + 
  delm[r5, r8]*delm[r1, r2, r3, r4, r6, r7] + 
  delm[r5, r7]*delm[r1, r2, r3, r4, r6, r8] + 
  delm[r5, r6]*delm[r1, r2, r3, r4, r7, r8] + 
  delm[r4, r8]*delm[r1, r2, r3, r5, r6, r7] + 
  delm[r4, r7]*delm[r1, r2, r3, r5, r6, r8] + 
  delm[r4, r6]*delm[r1, r2, r3, r5, r7, r8] + 
  delm[r4, r5]*delm[r1, r2, r3, r6, r7, r8] + 
  delm[r3, r8]*delm[r1, r2, r4, r5, r6, r7] + 
  delm[r3, r7]*delm[r1, r2, r4, r5, r6, r8] + 
  delm[r3, r6]*delm[r1, r2, r4, r5, r7, r8] + 
  delm[r3, r5]*delm[r1, r2, r4, r6, r7, r8] + 
  delm[r3, r4]*delm[r1, r2, r5, r6, r7, r8] + 
  delm[r2, r8]*delm[r1, r3, r4, r5, r6, r7] + 
  delm[r2, r7]*delm[r1, r3, r4, r5, r6, r8] + 
  delm[r2, r6]*delm[r1, r3, r4, r5, r7, r8] + 
  delm[r2, r5]*delm[r1, r3, r4, r6, r7, r8] + 
  delm[r2, r4]*delm[r1, r3, r5, r6, r7, r8] + 
  delm[r2, r3]*delm[r1, r4, r5, r6, r7, r8] + 
  delm[r1, r8]*delm[r2, r3, r4, r5, r6, r7] + 
  delm[r1, r7]*delm[r2, r3, r4, r5, r6, r8] + 
  delm[r1, r6]*delm[r2, r3, r4, r5, r7, r8] + 
  delm[r1, r5]*delm[r2, r3, r4, r6, r7, r8] + 
  delm[r1, r4]*delm[r2, r3, r5, r6, r7, r8] + 
  delm[r1, r3]*delm[r2, r4, r5, r6, r7, r8] + 
  delm[r1, r2]*delm[r3, r4, r5, r6, r7, r8], delm[r1, r2, r3, r4, r5, r6, r7, 
  r8]} * {1,-2,4,16,-272})
