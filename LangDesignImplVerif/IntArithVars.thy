section "A Language of Integer Arithmetic and Variables"

theory IntArithVars
  imports Main
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
datatype stmt = SLet name fexp | SReturn fexp

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
     (case A e1 \<rho> of None \<Rightarrow> (None,stdin)
      | Some n1 \<Rightarrow> 
        (case A e2 \<rho> of
          None \<Rightarrow> (None,stdin)
        | Some n2 \<Rightarrow> (Some (n1 + n2), stdin)))"

fun S :: "stmt \<Rightarrow> env \<Rightarrow> input \<Rightarrow> (int option \<times> input) + (env \<times> input)" where
  "S (SReturn e) \<rho> i = Inl (F e \<rho> i)" |
  "S (SLet x e) \<rho> i =
     (case F e \<rho> i of (None,i') \<Rightarrow> Inl (None,i')
      | (Some n, i') \<Rightarrow> Inr (\<rho>(x\<mapsto>n), i'))"

fun Ss :: "stmt list \<Rightarrow> env \<Rightarrow> input \<Rightarrow> (int option \<times> input) + (env \<times> input)" where
  "Ss [] \<rho> i = Inr (\<rho>,i)" |
  "Ss (s#ss) \<rho> i =
     (case S s \<rho> i of
       Inl r \<Rightarrow> Inl r
     | Inr (\<rho>',i') \<Rightarrow> Ss ss \<rho>' i')"  

fun P :: "stmt list \<Rightarrow> env \<Rightarrow> input \<Rightarrow> int option \<times> input" where
  "P ss \<rho> i = 
     (case Ss ss \<rho> i of
       Inl r \<Rightarrow> r
     | Inr (\<rho>',i') \<Rightarrow> (None, i'))"   
  
section "Compilation Pass: Flattening"

fun atomize :: "fexp \<Rightarrow> nat \<Rightarrow> nat \<times> atom \<times> (stmt list)" where
  "atomize (Atom a) k = (k, a, [])" |
  "atomize f k = (Suc k, AVar k, [SLet k f])"
  
fun flatten :: "exp \<Rightarrow> nat \<Rightarrow> nat \<times> fexp \<times> (stmt list)" where
  "flatten (EInt n) k = (k, Atom (AInt n), [])" |
  "flatten (ERead) k = (k+1, Atom (AVar k), [SLet k FRead])" |
  "flatten (ENeg e) k = 
    (let (k1,e',ss1) = flatten e k in
     let (k2,a,ss2) = atomize e' k1 in
     (k2, FNeg a, ss1@ ss2))" |
  "flatten (EAdd e1 e2) k =
    (let (k1,e1',ss1) = flatten e1 k in
     let (k2,e2',ss2) = flatten e2 k1 in
     let (k3,a1,c3) = atomize e1' k2 in
     let (k4,a2,c4) = atomize e2' k3 in
     (k4, FAdd a1 a2, ss1 @ ss2 @ c3 @ c4))" |
  "flatten (EVar x) k = (k, Atom (AVar x), [])" |
  "flatten (ELet x e1 e2) k = 
    (let (k1,e1',ss1) = flatten e1 k in
     let (k2,e2',ss2) = flatten e2 k1 in
     (k2, e2', ss1 @ (SLet x e1') # ss2))"

fun flatten_program :: "exp \<Rightarrow> stmt list" where
  "flatten_program e = (let (k,e',ss) = flatten e 0 in ss @ [SReturn e'])" 
  
value "flatten_program (ENeg (EAdd (EInt 1) (ENeg (EInt 2))))"
  
section "Correctness of Flattening"
  
lemma atomize_correct: "atomize e k = (k', a, ss) \<Longrightarrow> Ss [SReturn e] = Ss (ss @ [SReturn (Atom a)])"
  apply (cases e)
  apply force
    apply simp apply clarify apply (rule ext) apply (rule ext) apply simp
    apply (case_tac xa) apply force apply force
  apply simp apply (rule ext) apply (rule ext) apply simp apply clarify apply (case_tac "A x3 x")
    apply force apply force
  apply simp apply (rule ext) apply (rule ext) apply simp apply (case_tac "A x41 x") apply force
  apply simp apply (case_tac "A x42 x") apply auto 
  done
  
lemma S_append_cong2[cong]: "\<lbrakk> Ss ss2 = Ss ss2' \<rbrakk> \<Longrightarrow>
    Ss (ss1 @ ss2) \<rho> i = Ss (ss1 @ ss2') \<rho> i"
  apply (induction ss1 arbitrary: \<rho> i)
  apply force
  apply simp apply (case_tac "S a \<rho> i") apply force apply force
  done
    
lemma flatten_correct: "flatten e k = (k', e', ss) \<Longrightarrow> E e \<rho> i = P (ss @ [SReturn e']) \<rho> i"
proof (induction e arbitrary: k k' e' \<rho> i ss)
  case (EInt n)
  have 1: "E (EInt n) \<rho> i = (Some n,i)" by simp
  have 2: "flatten (EInt n) k = (k, Atom (AInt n), [])" by simp
  have 3: "P ([] @ [SReturn (Atom (AInt n))]) \<rho> i = (Some n, i)" by simp
  from EInt 1 2 3 show ?case by simp
next
  case ERead
  have 2: "flatten ERead k = (Suc k, Atom (AVar k), [SLet k FRead])" by simp
  have 3: "E ERead \<rho> i = P ([SLet k FRead] @ [SReturn (Atom (AVar k))]) \<rho> i" by (cases i) auto 
  from ERead 2 3 show ?case by simp
next
  case (ENeg e)
    
  then show ?case sorry
next
  case (EAdd e1 e2)
  then show ?case sorry
next
  case (EVar x)
  then show ?case sorry
next
  case (ELet x1a e1 e2)
  then show ?case sorry
qed
  
  apply force
  apply simp apply clarify apply (case_tac i) apply simp apply clarify apply simp
       apply (subgoal_tac "[SLet k FRead] @ [SReturn (Atom (AVar k))] = [SLet k FRead,SReturn (Atom (AVar k))]")
       prefer 2 apply force apply subst
  prefer 3 apply force 
proof -
  fix e k k' e' \<rho> i ss
  assume IH: "\<And>k k' e' \<rho> i ss. flatten e k = (k', e', ss) \<Longrightarrow> E e \<rho> i = S (ss @ [SReturn e']) \<rho> i"
    and fl: "flatten (ENeg e) k = (k', e', ss)" 
  obtain k1 e'' ss1 where fe: "flatten e k = (k1,e'',ss1)" apply (case_tac "flatten e k") by auto
  obtain k2 a ss2 where aep: "atomize e'' k1 = (k2,a,ss2)" apply (case_tac "atomize e'' k1") by auto    
  from fl fe aep have kp: "k' = k2" by simp
  from fl fe aep have ep: "e' = FNeg a" by auto 
  from fl fe aep have ss: "ss = ss1 @ ss2" by auto 
  from IH fe have Ee_Sf: "E e \<rho> i = S (ss1 @ [SReturn e'']) \<rho> i" by blast    
  from aep have 2: "S [SReturn e''] = S (ss2 @ [SReturn (Atom a)])" by (rule atomize_correct)
  from Ee_Sf 2 have 3: "E e \<rho> i = S (ss1 @ ss2 @ [SReturn (Atom a)]) \<rho> i" apply simp
      
  from ep c show "E (ENeg e) \<rho> stdin = S (c (SReturn e'')) \<rho> stdin"
  proof clarify
    
    show "E (ENeg e) \<rho> stdin = S (c1 (c2 (SReturn (FNeg a)))) \<rho> stdin" sorry
     
  qed
next
  fix e1 e2 x xa k k' e' c
  show " E (EAdd e1 e2) x xa = S (c (SReturn e')) x xa" sorry
next
  fix x1a e1 e2 x xa k k' e' c
  show "E (ELet x1a e1 e2) x xa = S (c (SReturn e')) x xa" sorry
qed
  
end
  