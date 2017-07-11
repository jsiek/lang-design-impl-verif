section "A Language of Integer Arithmetic and Variables"

theory IntArithVars
  imports Main
begin
  
type_synonym name = nat
 
datatype exp = EInt int | ERead | ENeg exp | EAdd exp exp | EVar name | ELet name exp exp

type_synonym input = "int list"

type_synonym env = "name \<rightharpoonup> int"

fun E :: "exp \<Rightarrow> env \<Rightarrow> input \<Rightarrow> (int \<times> input) option" where
  "E (EInt n) \<rho> stdin = Some (n,stdin)" |
  "E (ERead) \<rho> stdin = (case stdin of [] \<Rightarrow> None
                        | Cons n stdin' \<Rightarrow> Some (n, stdin'))" |
  "E (ENeg e) \<rho> stdin = (case E e \<rho> stdin of None \<Rightarrow> None
                        | Some (n,stdin') \<Rightarrow> Some (- n, stdin'))" |
  "E (EAdd e1 e2) \<rho> stdin =
     (case E e1 \<rho> stdin of None \<Rightarrow> None
      | Some (n1,stdin') \<Rightarrow> 
        (case E e2 \<rho> stdin' of
          None \<Rightarrow> None
        | Some (n2, stdin'') \<Rightarrow> Some (n1 + n2, stdin'')))" |
  "E (EVar x) \<rho> stdin = (case \<rho> x of None \<Rightarrow> None | Some n \<Rightarrow> Some (n, stdin))" |
  "E (ELet x e1 e2) \<rho> stdin =
     (case E e1 \<rho> stdin of None \<Rightarrow> None
      | Some (n,stdin') \<Rightarrow> E e2 (\<rho>(x\<mapsto>n)) stdin')"

section "Intermediate Language in A-normal form"
  
datatype atom = AInt int | AVar name
datatype fexp = Atom atom | FNeg atom | FAdd atom atom
datatype stmt = Assign name fexp | Read name 
type_synonym block = "stmt list \<times> fexp"

fun A :: "atom \<Rightarrow> env \<Rightarrow> int option" where
  "A (AInt n) \<rho> = Some n" |
  "A (AVar x) \<rho> = \<rho> x" 
  
fun F :: "fexp \<Rightarrow> env \<Rightarrow> int option" where
  "F (Atom a) \<rho> = A a \<rho>" |
  "F (FNeg e) \<rho> = (case A e \<rho>  of None \<Rightarrow> None
                        | Some n \<Rightarrow> Some (- n))" |
  "F (FAdd e1 e2) \<rho> =
     (case A e1 \<rho> of None \<Rightarrow> None
      | Some n1 \<Rightarrow> 
        (case A e2 \<rho> of
          None \<Rightarrow> None
        | Some n2 \<Rightarrow> Some (n1 + n2)))"

type_synonym state = "env \<times> input"
type_synonym state_xfr = "state \<Rightarrow> state option"

fun S :: "stmt \<Rightarrow> state_xfr" where
  "S (Assign x e) (\<rho>, i) =
     (case F e \<rho> of None \<Rightarrow> None
      | Some n \<Rightarrow> Some (\<rho>(x\<mapsto>n), i))" |
  "S (Read x) (\<rho>, i) = (case i of [] \<Rightarrow> None
                     | Cons n i' \<Rightarrow> Some (\<rho>(x\<mapsto>n), i'))"
  
definition seq :: "('a \<Rightarrow> 'b option) \<Rightarrow> ('b \<Rightarrow> 'c option) \<Rightarrow> 'a \<Rightarrow> 'c option" where
  "seq f1 f2 \<sigma> \<equiv> (case f1 \<sigma> of None \<Rightarrow> None | Some \<sigma>' \<Rightarrow> f2 \<sigma>')"

definition ret :: "state_xfr" where
  "ret \<sigma> = Some \<sigma>"
  
fun Ss :: "stmt list \<Rightarrow> state_xfr" where
  "Ss [] = ret" |
  "Ss (s#ss) = seq (S s) (Ss ss)"

fun B :: "block \<Rightarrow> state \<Rightarrow> (int \<times> input) option" where
  "B (ss,e) = seq (Ss ss) (\<lambda>(\<rho>,i). case F e \<rho> of None \<Rightarrow> None | Some n \<Rightarrow> Some (n,i))"

lemma seq_ret[simp]: "seq ret f = f"
  unfolding seq_def ret_def apply (rule ext) apply auto done

lemma seq_assoc[simp]: "seq (seq f1 f2) f3 = seq f1 (seq f2 f3)" 
  unfolding seq_def apply (rule ext) apply (case_tac "f1 \<sigma>") apply auto done

lemma Ss_append_seq[simp]: "Ss (ss1@ss2) = seq (Ss ss1) (Ss ss2)"
  by (induction ss1) auto
    
lemma seq1_none[simp]: "f1 \<sigma> = None \<Longrightarrow> seq f1 f2 \<sigma> = None"
  by (simp add: seq_def)
    
lemma seq1_some[simp]: "f1 \<sigma> = Some \<sigma>' \<Longrightarrow> seq f1 f2 \<sigma> = f2 \<sigma>'"
  by (simp add: seq_def)  
    
section "Compilation Pass: Flattening"

fun atomize :: "fexp \<Rightarrow> nat \<Rightarrow> nat \<times> (stmt list) \<times> atom" where
  "atomize (Atom a) k = (k, [], a)" |
  "atomize f k = (Suc k, [Assign k f], AVar k)"

fun flatten :: "exp \<Rightarrow> nat \<Rightarrow> nat \<times> block" where
  "flatten (EInt n) k = (k, [], Atom (AInt n))" |
  "flatten (ERead) k = (k+1, [Read k], Atom (AVar k))" |
  "flatten (ENeg e) k = 
    (let (k1,ss1,e') = flatten e k in
     let (k2,ss2,a) = atomize e' k1 in
     (k2, ss1@ ss2, FNeg a))" |
  "flatten (EAdd e1 e2) k =
    (let (k1,ss1,e1') = flatten e1 k in
     let (k2,ss2,e2') = flatten e2 k1 in
     let (k3,ss3,a1) = atomize e1' k2 in
     let (k4,ss4,a2) = atomize e2' k3 in
     (k4, ss1 @ ss2 @ ss3 @ ss4, FAdd a1 a2))" |
  "flatten (EVar x) k = (k, [], Atom (AVar x))" |
  "flatten (ELet x e1 e2) k = 
    (let (k1,ss1,e1') = flatten e1 k in
     let (k2,ss2,e2') = flatten e2 k1 in
     (k2, ss1 @ (Assign x e1') # ss2, e2'))"

fun flatten_program :: "exp \<Rightarrow> block" where
  "flatten_program e = (let (k,ss,e') = flatten e 0 in (ss, e'))" 

value "flatten_program (ENeg (EAdd (EInt 1) (ENeg (EInt 2))))"
  
section "Correctness of Flattening"

lemma atomize_correct: "atomize e k = (k', ss, a) \<Longrightarrow> B ([], e) = B (ss, Atom a)"
  apply (cases e)
  apply force
  apply simp apply clarify apply (rule ext) apply (case_tac x) apply simp
    apply (case_tac "A x2 aa") apply auto
  apply (rule ext) apply (case_tac x) apply (simp add: seq_def) 
    apply (case_tac "A x31 aa") apply (auto simp: seq_def)
    apply (case_tac "A x32 aa") apply (auto simp: seq_def)
  done
  
lemma B_append: assumes 1: "B (ss2, e1) = B (ss2', e2)"
  shows "B (ss1 @ ss2, e1) (\<rho>, i) = B (ss1 @ ss2', e2) (\<rho>, i)"
proof (cases "Ss ss1 (\<rho>,i)")
  case None
  then show ?thesis by simp
next
  case (Some \<sigma>)
  from Some obtain \<rho>' i' where Ss_ss1: "Ss ss1 (\<rho>,i) = Some (\<rho>',i')" by (cases \<sigma>) auto
  from 1 have A: "B (ss2, e1) (\<rho>',i') = B (ss2', e2) (\<rho>',i')" by simp
  from Ss_ss1 A show ?thesis by simp
qed  
    
lemma flatten_correct: "flatten e k = (k', ss, e') \<Longrightarrow> E e \<rho> i = B (ss, e') (\<rho>, i)"
proof (induction e arbitrary: k k' e' \<rho> i ss)
  case (EInt n)
  have 1: "E (EInt n) \<rho> i = Some (n,i)" by simp
  have 2: "flatten (EInt n) k = (k, [], Atom (AInt n))" by simp
  have 3: "B ([], Atom (AInt n)) (\<rho>, i) = Some (n, i)" by simp
  from EInt 1 2 3 show ?case by simp
next
  case ERead
  have 2: "flatten ERead k = (Suc k, [Read k], Atom (AVar k))" by simp
  have 3: "E ERead \<rho> i = B ([Read k], Atom (AVar k)) (\<rho>, i)" by (cases i) (auto simp: seq_def) 
  from ERead 2 3 show ?case by simp
next
  case (ENeg e k k' e' \<rho> i ss)
  obtain k1 e1 ss1 where fe: "flatten e k = (k1,ss1,e1)" by (case_tac "flatten e k") auto
  obtain k2 a ss2 where ae1: "atomize e1 k1 = (k2,ss2,a)" by (case_tac "atomize e1 k1") auto
  from fe ae1 ENeg have fne: "flatten (ENeg e) k = (k2, ss1@ss2, FNeg a)" by simp
  from fe ENeg have IH: "E e \<rho> i = B (ss1, e1) (\<rho>, i)" by blast
  from ae1 have 1: "B ([], e1) = B (ss2, Atom a)" using atomize_correct[of e1 k1] by blast
  from 1 have 2: "B (ss1, e1) (\<rho>, i) = B (ss1 @ ss2, Atom a) (\<rho>, i)"
    using B_append[of "[]" e1 ss2 "Atom a"] by simp
  from IH 2 have 3: "E e \<rho> i = B (ss1 @ ss2, Atom a) (\<rho>, i)" by simp
  have 4: "E (ENeg e) \<rho> i = B (ss1 @ ss2, FNeg a) (\<rho>, i)"
  proof (cases "E e \<rho> i")
    case None
    from this 3 show ?thesis apply (case_tac "seq (Ss ss1) (Ss ss2) (\<rho>,i)") apply force
      apply (case_tac aa) apply (case_tac "A a aaa") apply auto done
  next
    case (Some \<sigma>')
    from this 3 show ?thesis  apply (case_tac "seq (Ss ss1) (Ss ss2) (\<rho>,i)") apply force apply auto
      apply (case_tac "A a aa") apply auto done
  qed
  from 4 fne ENeg show ?case by auto      
next
  case (EAdd e1 e2)
  obtain k1 ss1 e1' where fe1: "flatten e1 k = (k1,ss1,e1')" by (case_tac "flatten e1 k") auto
  obtain k2 ss2 e2' where fe2: "flatten e2 k1 = (k2,ss2,e2')" by (case_tac "flatten e2 k1") auto
  obtain k3 ss3 a1 where ae1: "atomize e1' k2 = (k3,ss3,a1)" by (case_tac "atomize e1' k2") auto
  obtain k4 ss4 a2 where ae2: "atomize e2' k3 = (k4,ss4,a2)" by (case_tac "atomize e2' k3") auto
  from fe1 fe2 ae1 ae2 have fadd: "flatten (EAdd e1 e2) k = (k4, ss1 @ ss2 @ ss3 @ ss4, FAdd a1 a2)"
    by simp
  from fe1 EAdd have IH1: "E e1 \<rho> i = B (ss1, e1') (\<rho>, i)" by blast
  from ae1 have 1: "B ([], e1') = B (ss3, Atom a1)" using atomize_correct by blast
  from 1 have 2: "B (ss1@ss2, e1') (\<rho>, i) = B (ss1@ss2 @ ss3, Atom a1) (\<rho>, i)"
    using B_append[of "[]" e1' ss3 "Atom a1" "ss1@ss2"] by simp
  from IH1 2 have 3: "E e1 \<rho> i = B (ss1 @ ss2, Atom a1) (\<rho>, i)" by simp
      
  then show ?case sorry
next
  case (EVar x)
  then show ?case sorry
next
  case (ELet x1a e1 e2)
  then show ?case sorry
qed

  
end
  