section "A Language of Integer Arithmetic and Variables"

theory IntArithVars
  imports Main "~~/src/HOL/Library/Finite_Map"
begin
  
type_synonym name = nat
 
datatype exp = EInt int | ERead | ENeg exp | EAdd exp exp | EVar name | ELet name exp exp

type_synonym input = "int list"

type_synonym env = "name \<rightharpoonup> int"

fun E :: "exp \<Rightarrow> env \<Rightarrow> input \<Rightarrow> int option \<times> input" where
  "E (EInt n) \<rho> stdin = (Some n,stdin)" |
  "E (ERead) \<rho> stdin = (case stdin of [] \<Rightarrow> (None, [])
                        | Cons n stdin' \<Rightarrow> (Some n, stdin'))" |
  "E (ENeg e) \<rho> stdin = (case E e \<rho> stdin of (None,stdin') \<Rightarrow> (None,stdin')
                        | (Some n,stdin') \<Rightarrow> (Some (- n), stdin'))" |
  "E (EAdd e1 e2) \<rho> stdin =
     (case E e1 \<rho> stdin of (None,stdin') \<Rightarrow> (None,stdin')
      | (Some n1,stdin') \<Rightarrow> 
        (case E e2 \<rho> stdin' of
          (None,stdin'') \<Rightarrow> (None,stdin'')
        | (Some n2,stdin'') \<Rightarrow> (Some (n1 + n2), stdin'')))" |
  "E (EVar x) \<rho> stdin = (\<rho> x, stdin)" |
  "E (ELet x e1 e2) \<rho> stdin =
     (case E e1 \<rho> stdin of (None,stdin') \<Rightarrow> (None,stdin')
      | (Some n,stdin') \<Rightarrow> E e2 (\<rho>(x\<mapsto>n)) stdin')"
  
section "Intermediate Language in A-normal form"
  
datatype atom = AInt int | AVar name
datatype fexp = Atom atom | FRead | FNeg atom | FAdd atom atom
datatype stmt = ALet name fexp stmt | Return fexp

section "Compilation Pass: Flattening"

fun atomize :: "fexp \<Rightarrow> nat \<Rightarrow> nat \<times> atom \<times> (stmt \<Rightarrow> stmt)" where
  "atomize (Atom a) k = (k, a, \<lambda>s. s)" |
  "atomize f k = (Suc k, AVar k, \<lambda>s. ALet k f s)"
  
fun flatten :: "exp \<Rightarrow> nat \<Rightarrow> nat \<times> fexp \<times> (stmt \<Rightarrow> stmt)" where
  "flatten (EInt n) k = (k, Atom (AInt n), \<lambda>s. s)" |
  "flatten (ERead) k = (k+1, Atom (AVar k), \<lambda>s. ALet k FRead s)" |
  "flatten (ENeg e) k = 
    (let (k',e',c) = flatten e k in
     let (k'',a,c') = atomize e' k' in
     (k'', FNeg a, \<lambda>s. c (c' s)))" |
  "flatten (EAdd e1 e2) k =
    (let (k1,e1',c1) = flatten e1 k in
     let (k2,e2',c2) = flatten e2 k1 in
     case (e1',e2') of
       (Atom a1, Atom a2) \<Rightarrow> (k2, FAdd a1 a2, \<lambda>s. c1 (c2 s))
    | _ \<Rightarrow> (2+k2, FAdd (AVar k2) (AVar (Suc k2)),
           \<lambda>s. c1 (c2 (ALet k2 e1' (ALet (Suc k2) e2' s)))))" |
  "flatten (EVar x) k = (k, Atom (AVar x), \<lambda>s. s)" |
  "flatten (ELet x e1 e2) k = 
    (let (k1,e1',c1) = flatten e1 k in
     let (k2,e2',c2) = flatten e2 k1 in
     (k2, e2', \<lambda>s. c1 (ALet x e1' (c2 s))))"

fun flatten_program :: "exp \<Rightarrow> stmt" where
  "flatten_program e = (let (k,e',s) = flatten e 0 in s (Return e'))" 
  
value "flatten_program (ENeg (EAdd (EInt 1) (ENeg (EInt 2))))"
  
end
  