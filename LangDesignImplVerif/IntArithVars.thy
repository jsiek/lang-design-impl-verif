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
datatype stmt = SLet name fexp stmt | SReturn fexp
  
fun A :: "atom \<Rightarrow> env \<Rightarrow> int option" where
  "A (AInt n) \<rho> = Some n" |
  "A (AVar x) \<rho> = \<rho> x" 
  
fun F :: "fexp \<Rightarrow> env \<Rightarrow> input \<Rightarrow> int option \<times> input" where
  "F (Atom a) \<rho> stdin = (A a \<rho>, stdin)" |
  "F (FRead) \<rho> stdin = (case stdin of [] \<Rightarrow> (None, [])
                        | Cons n stdin' \<Rightarrow> (Some n, stdin'))" |
  "F (FNeg e) \<rho> stdin = (case A e \<rho>  of None \<Rightarrow> (None,stdin)
                        | Some n \<Rightarrow> (Some (- n),stdin))" |
  "F (FAdd e1 e2) \<rho> stdin =
     (case A e1 \<rho> of (None) \<Rightarrow> (None,stdin)
      | Some n1 \<Rightarrow> 
        (case A e2 \<rho> of
          None \<Rightarrow> (None,stdin)
        | Some n2 \<Rightarrow> (Some (n1 + n2), stdin)))"

fun S :: "stmt \<Rightarrow> env \<Rightarrow> input \<Rightarrow> int option \<times> input" where
  "S (SReturn e) \<rho> stdin = F e \<rho> stdin" |
  "S (SLet x e1 e2) \<rho> stdin =
     (case F e1 \<rho> stdin of (None,stdin') \<Rightarrow> (None,stdin')
      | (Some n,stdin') \<Rightarrow> S e2 (\<rho>(x\<mapsto>n)) stdin')"

section "Compilation Pass: Flattening"

fun atomize :: "fexp \<Rightarrow> nat \<Rightarrow> nat \<times> atom \<times> (stmt \<Rightarrow> stmt)" where
  "atomize (Atom a) k = (k, a, \<lambda>s. s)" |
  "atomize f k = (Suc k, AVar k, \<lambda>s. SLet k f s)"
  
fun flatten :: "exp \<Rightarrow> nat \<Rightarrow> nat \<times> fexp \<times> (stmt \<Rightarrow> stmt)" where
  "flatten (EInt n) k = (k, Atom (AInt n), \<lambda>s. s)" |
  "flatten (ERead) k = (k+1, Atom (AVar k), \<lambda>s. SLet k FRead s)" |
  "flatten (ENeg e) k = 
    (let (k1,e',c) = flatten e k in
     let (k2,a,c') = atomize e' k1 in
     (k2, FNeg a, \<lambda>s. c (c' s)))" |
  "flatten (EAdd e1 e2) k =
    (let (k1,e1',c1) = flatten e1 k in
     let (k2,e2',c2) = flatten e2 k1 in
     let (k3,a1,c3) = atomize e1' k2 in
     let (k4,a2,c4) = atomize e2' k3 in
     (k4, FAdd a1 a2, \<lambda>s. c1 (c2 (c3 (c4 s)))))" |
  "flatten (EVar x) k = (k, Atom (AVar x), \<lambda>s. s)" |
  "flatten (ELet x e1 e2) k = 
    (let (k1,e1',c1) = flatten e1 k in
     let (k2,e2',c2) = flatten e2 k1 in
     (k2, e2', \<lambda>s. c1 (SLet x e1' (c2 s))))"

fun flatten_program :: "exp \<Rightarrow> stmt" where
  "flatten_program e = (let (k,e',s) = flatten e 0 in s (SReturn e'))" 
  
value "flatten_program (ENeg (EAdd (EInt 1) (ENeg (EInt 2))))"
  
section "Correctness of Flattening"
  
lemma atomize_correct: "atomize e k = (k', a, c) \<Longrightarrow> S (SReturn e) = S (c (SReturn (Atom a)))"
  apply (cases e)
  apply force
    apply simp apply clarify apply (rule ext) apply (rule ext) apply simp
    apply (case_tac xa) apply force apply force
  apply simp apply (rule ext) apply (rule ext) apply simp apply clarify apply (case_tac "A x3 x")
    apply force apply force
  apply simp apply (rule ext) apply (rule ext) apply simp apply (case_tac "A x41 x") apply force
  apply simp apply (case_tac "A x42 x") apply auto 
  done
    
lemma flatten_correct: "flatten e k = (k', e', c) \<Longrightarrow> E e = S (c (SReturn e'))"
  apply (rule ext) apply (rule ext)
  apply (induction e arbitrary: k k' e' c)
  apply force
      apply simp apply (case_tac xa) apply force apply force
  prefer 3 apply force 
proof -
  fix e \<rho> stdin k k' e' c
  assume IH: "(\<And>x xa k k' e' c. flatten e k = (k', e', c) \<Longrightarrow> E e x xa = S (c (SReturn e')) x xa)" 
       and fl: "flatten (ENeg e) k = (k', e', c)"
  obtain k1 f c1 where fe: "flatten e k = (k1,f,c1)" apply (case_tac "flatten e k") by auto
  obtain k2 a c2 where aep: "atomize f k1 = (k2,a,c2)" apply (case_tac "atomize f k1") by auto
  from fl fe aep have kp: "k' = k2" by simp
  from fl fe aep have ep: "e' = FNeg a" by auto 
  from fl fe aep have c: "c = (\<lambda>s. c1 (c2 s))" by auto 
  from IH fe have Ee_Sf: "E e \<rho> stdin = S (c1 (SReturn f)) \<rho> stdin" by blast
  from aep have "S (SReturn f) = S (c2 (SReturn (Atom a)))" by (rule atomize_correct)

  show "E (ENeg e) \<rho> stdin = S (c (SReturn e')) \<rho> stdin" 
    sorry
next
  fix e1 e2 x xa k k' e' c
  show " E (EAdd e1 e2) x xa = S (c (SReturn e')) x xa" sorry
next
  fix x1a e1 e2 x xa k k' e' c
  show "E (ELet x1a e1 e2) x xa = S (c (SReturn e')) x xa" sorry
qed
  
end
  