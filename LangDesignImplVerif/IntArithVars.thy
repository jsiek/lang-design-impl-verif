theory IntArithVars
  imports Main
begin
  
type_synonym name = nat
 
datatype exp = EInt int | ERead | ENeg exp | EAdd exp exp | EVar name | ELet name exp exp
  

  
end
  