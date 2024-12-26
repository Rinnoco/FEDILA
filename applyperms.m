applyperms[expr_,list_]:=
           firstor0[Sort[simplifydelm[canonical[expr /. #]]& /@ list]]

applyperms[expr_Plus,list_]:=
                    applyperms[#,list]& /@ expr


