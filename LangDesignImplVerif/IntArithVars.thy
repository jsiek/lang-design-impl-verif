section "A Language of Integer Arithmetic and Variables"

theory IntArithVars
  imports Main "~~/src/HOL/Library/FSet"
begin
  
type_synonym index = nat
 
datatype exp = EInt int | ERead | EPrim "int\<Rightarrow>int\<Rightarrow>int" exp exp | EVar index | ELet exp exp

type_synonym input = "int list"

type_synonym val = int
type_synonym env = "val list"

fun E :: "exp \<Rightarrow> env \<Rightarrow> input \<Rightarrow> (val \<times> input) option" where
  "E (EInt n) \<rho> i = Some (n,i)" |
  "E (ERead) \<rho> i = (case i of [] \<Rightarrow> None
                        | Cons n i' \<Rightarrow> Some (n, i'))" |
  "E (EPrim f e1 e2) \<rho> i =
     (case E e1 \<rho> i of None \<Rightarrow> None
      | Some (n1,i') \<Rightarrow> 
        (case E e2 \<rho> i' of
          None \<Rightarrow> None
        | Some (n2, i'') \<Rightarrow> Some (f n1 n2, i'')))" |
  "E (EVar n) \<rho> i = (if n < length \<rho> then Some (\<rho>!n,i) else None)" |
  "E (ELet e1 e2) \<rho> i =
     (case E e1 \<rho> i of None \<Rightarrow> None
      | Some (n,i') \<Rightarrow> E e2 (n#\<rho>) i')"

fun shifte :: "nat \<Rightarrow> nat \<Rightarrow> exp \<Rightarrow> exp" where
  "shifte k c (EInt n) = (EInt n)" |
  "shifte k c (ERead) = (ERead)" |
  "shifte k c (EPrim f e1 e2) = EPrim f (shifte k c e1) (shifte k c e2)" |
  "shifte k c (EVar n) = (if c \<le> n then EVar (n + k) else EVar n)" |
  "shifte k c (ELet e1 e2) = ELet (shifte k c e1) (shifte k (Suc c) e2)"

section "Intermediate Language in A-normal form"
  
datatype atom = AInt int | AVar index
datatype fexp = Atom atom | FPrim "int\<Rightarrow>int\<Rightarrow>int" atom atom
datatype stmt = Push fexp | Read 
type_synonym block = "stmt list \<times> atom"

fun A :: "atom \<Rightarrow> env \<Rightarrow> int option" where
  "A (AInt n) \<rho> = Some n" |
  "A (AVar k) \<rho> = (if k < length \<rho> then Some (\<rho>!k) else None)" 

fun F :: "fexp \<Rightarrow> env \<Rightarrow> int option" where
  "F (Atom a) \<rho> = A a \<rho>" |
  "F (FPrim f e1 e2) \<rho> =
     (case A e1 \<rho> of None \<Rightarrow> None
      | Some n1 \<Rightarrow> 
        (case A e2 \<rho> of
          None \<Rightarrow> None
        | Some n2 \<Rightarrow> Some (f n1 n2)))"

type_synonym state = "env \<times> input"
type_synonym state_xfr = "state \<Rightarrow> state option"

fun S :: "stmt \<Rightarrow> state_xfr" where
  "S (Push e) (\<rho>, i) =
     (case F e \<rho> of None \<Rightarrow> None
      | Some n \<Rightarrow> Some (n#\<rho>, i))" |
  "S (Read) (\<rho>, i) = (case i of [] \<Rightarrow> None
                     | Cons n i' \<Rightarrow> Some (n#\<rho>, i'))"
  
definition seq :: "('a \<Rightarrow> 'b option) \<Rightarrow> ('b \<Rightarrow> 'c option) \<Rightarrow> 'a \<Rightarrow> 'c option" where
  "seq f1 f2 \<sigma> \<equiv> (case f1 \<sigma> of None \<Rightarrow> None | Some \<sigma>' \<Rightarrow> f2 \<sigma>')"

definition ret :: "state_xfr" where
  "ret \<sigma> = Some \<sigma>"
  
fun Ss :: "stmt list \<Rightarrow> state_xfr" where
  "Ss [] = ret" |
  "Ss (s#ss) = seq (S s) (Ss ss)"

fun As :: "atom \<Rightarrow> state \<Rightarrow> (int \<times> input) option" where
  "As e (\<rho>,i) = (case A e \<rho> of None \<Rightarrow> None | Some n \<Rightarrow> Some (n,i))"

fun B :: "block \<Rightarrow> state \<Rightarrow> (int \<times> input) option" where
  "B (ss,e) = seq (Ss ss) (As e)"

fun shifta :: "nat \<Rightarrow> nat \<Rightarrow> atom \<Rightarrow> atom" where
  "shifta k c (AInt n) = (AInt n)" |
  "shifta k c (AVar n) = (if c \<le> n then AVar (n + k) else AVar n)" 

fun shiftf :: "nat \<Rightarrow> nat \<Rightarrow> fexp \<Rightarrow> fexp" where
  "shiftf k c (Atom a) = Atom (shifta k c a)" |
  "shiftf k c (FPrim f e1 e2) = FPrim f (shifta k c e1) (shifta k c e2)"

fun shifts :: "nat \<Rightarrow> nat \<Rightarrow> stmt \<Rightarrow> stmt" where
  "shifts k c (Read) = Read" |
  "shifts k c (Push e) = Push (shiftf k c e)"

fun shiftb :: "nat \<Rightarrow> nat \<Rightarrow> block \<Rightarrow> block" where
  "shiftb k c ([], e) = ([], shifta k c e)" |
  "shiftb k c (s#ss, e) = (let (ss',e') = shiftb k (Suc c) (ss,e)
                           in ((shifts k c s)#ss', e'))"

lemma seq_ret[simp]: "seq ret f = f"
  unfolding seq_def ret_def apply (rule ext) apply auto done

lemma seq_assoc: "seq (seq f1 f2) f3 = seq f1 (seq f2 f3)" 
  unfolding seq_def apply (rule ext) apply (case_tac "f1 \<sigma>") apply auto done

lemma Ss_append_seq[simp]: "Ss (ss1@ss2) = seq (Ss ss1) (Ss ss2)"
  by (induction ss1) (auto simp: seq_assoc)
    
lemma seq1_none[simp]: "f1 \<sigma> = None \<Longrightarrow> seq f1 f2 \<sigma> = None"
  by (simp add: seq_def)
    
lemma seq1_some[simp]: "f1 \<sigma> = Some \<sigma>' \<Longrightarrow> seq f1 f2 \<sigma> = f2 \<sigma>'"
  by (simp add: seq_def)  

lemma seq_front: "f1 \<sigma> = f1' \<sigma>' \<Longrightarrow> seq f1 f2 \<sigma> = seq f1' f2 \<sigma>'"
  by (simp add: seq_def) 
  
section "Compilation Pass: Flattening"

fun flatten :: "exp \<Rightarrow> block" where
  "flatten (EInt n) = ([], AInt n)" |
  "flatten (ERead) = ([Read], AVar 0)" |
  "flatten (EPrim f e1 e2) =
    (let (ss1,a1) = flatten e1 in
     let (ss2,a2) = flatten e2 in
     let a1' = shifta (length ss2) 0 a1 in
     let (ss2',a2') = shiftb (length ss1) 0 (ss2,a2) in
     (ss1 @ ss2' @ [Push (FPrim f a1' a2')], AVar 0))" |
  "flatten (EVar x) = ([], AVar x)" |
  "flatten (ELet e1 e2) = 
    (let (ss1,a1) = flatten e1 in
     let (ss2,a2) = flatten e2 in
     let (ss2',a2') = shiftb (length ss1) 1 (ss2,a2) in
     (ss1 @ (Push (Atom a1)) # ss2', a2'))"

fun flatten_program :: "exp \<Rightarrow> block" where
  "flatten_program e = (let (ss,e') = flatten e in (ss, e'))" 

fun eadd :: "exp \<Rightarrow> exp \<Rightarrow> exp" where
  "eadd e1 e2 = EPrim (\<lambda>a.\<lambda>b. a+b) e1 e2"
fun esub :: "exp \<Rightarrow> exp \<Rightarrow> exp" where
  "esub e1 e2 = EPrim (\<lambda>a.\<lambda>b. a-b) e1 e2"

section "A Little Testing"
  
(*  (4 + 40) - (7 - 5) = 42*)
definition P0 :: exp where
  "P0 \<equiv> esub (eadd (EInt 4) (EInt 40)) (esub (EInt 7) (EInt 5))"

value "E P0 [] []"
value "flatten_program P0"
value "B (flatten_program P0) ([],[])"

definition P1 :: exp where
  "P1 \<equiv> ELet P0 (eadd (esub (EInt 2) (EInt 2)) (EVar 0))"

value "E P1 [] []" 
value "flatten_program P1"
value "B (flatten_program P1) ([],[])" 

section "Lemmas regarding shift"

lemma nth_append1[simp]: "n < length \<rho>1 \<Longrightarrow> (\<rho>1@\<rho>2)!n = \<rho>1!n"
  apply (induction \<rho>1 arbitrary: \<rho>2 n)
  apply force
  apply (case_tac n) apply simp apply simp done

lemma nth_append2[simp]: "n \<ge> length \<rho>1 \<Longrightarrow> (\<rho>1@\<rho>2)!n = \<rho>2!(n - length \<rho>1)"
  apply (induction \<rho>1 arbitrary: \<rho>2 n)
  apply force
  apply (case_tac n) apply simp apply simp done
 
lemma shifta_append: "A e (\<rho>1@\<rho>3) = A (shifta (length \<rho>2) (length \<rho>1) e) (\<rho>1@\<rho>2@\<rho>3)"
  by (cases e) auto
    
lemma shiftf_append: "F e (\<rho>1@\<rho>3) = F (shiftf (length \<rho>2) (length \<rho>1) e) (\<rho>1@\<rho>2@\<rho>3)"
  apply (cases e)
  using shifta_append apply force
  apply simp apply (case_tac "A x22 (\<rho>1@\<rho>3)") apply auto using shifta_append apply auto
  done

lemma Ss_result: "S s (\<rho>,i) = None \<or> (\<exists> v i'. S s (\<rho>,i) = Some (v#\<rho>,i'))"
  apply (cases s) apply simp apply (case_tac "F x1 \<rho>") apply auto
  apply (case_tac i) apply auto
  done

lemma shifts_append_some: "S s (\<rho>1@\<rho>3,i) = Some (v#(\<rho>1@\<rho>3),i') \<Longrightarrow>
    S (shifts (length \<rho>2) (length \<rho>1) s) (\<rho>1@\<rho>2@\<rho>3,i) = Some (v#(\<rho>1@\<rho>2@\<rho>3),i')"
  apply (cases s)
  -- "Push x1"
  apply simp apply (case_tac "F x1 (\<rho>1@\<rho>3)") 
    using shiftf_append apply force   
    apply simp apply (subgoal_tac "F x1 (\<rho>1@\<rho>3) = F (shiftf (length \<rho>2) (length \<rho>1) x1) (\<rho>1@\<rho>2@\<rho>3)")
    prefer 2 using shiftf_append apply blast 
    apply simp
  -- "Read"
  apply simp apply (case_tac i) apply auto
  done

lemma shifts_append_none: "S s (\<rho>1@\<rho>3,i) = None \<Longrightarrow>
   S (shifts (length \<rho>2) (length \<rho>1) s) (\<rho>1@\<rho>2@\<rho>3,i) = None"
  apply (cases s)
  apply simp apply (case_tac "F x1 (\<rho>1@\<rho>3)") 
    using shiftf_append apply force
    using shiftf_append apply force
  apply simp apply (case_tac i) apply auto
  done   
    
lemma shiftb_append: "B (ss,e) (\<rho>1@\<rho>3,i) = B (shiftb (length \<rho>2) (length \<rho>1) (ss,e)) (\<rho>1@\<rho>2@\<rho>3,i)"
  apply (induction ss arbitrary: \<rho>1 \<rho>2 \<rho>3 i e)
  using shifta_append apply force
proof -
  fix s ss and \<rho>1::env and \<rho>2::env and \<rho>3::env and i e
  assume IH: "\<And>\<rho>1 \<rho>2 \<rho>3 i e. B (ss, e) (\<rho>1@\<rho>3, i) = B (shiftb (length \<rho>2) (length \<rho>1) (ss, e))
            (\<rho>1@\<rho>2@\<rho>3, i)" 
  let ?sp = "shifts (length \<rho>2) (length \<rho>1) s" 
  have "B (s # ss, e) (\<rho>1@\<rho>3, i) = seq (Ss (s#ss)) (As e) (\<rho>1@\<rho>3, i)" by simp
  also have "... = seq (S s) (seq (Ss ss) (As e)) (\<rho>1@\<rho>3, i)" by (simp add: seq_assoc)   
      
  show "B (s # ss, e) (\<rho>1 @ \<rho>3, i) = B (shiftb (length \<rho>2) (length \<rho>1) (s # ss, e)) (\<rho>1@\<rho>2@\<rho>3, i)"
    sorry
qed
  
section "Correctness of Flattening"
  
lemma atomize_correct: "\<lbrakk> atomize e k = (k', ss, a) \<rbrakk> \<Longrightarrow> Fs e = seq (Ss ss) (Fs (Atom a))"
  apply (cases e)
  apply force
  apply simp apply clarify apply (rule ext) apply (case_tac x) apply simp
    apply (case_tac "A x2 aa") apply (auto simp: seq_assoc)
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
  from Ss_ss1 A show ?thesis by (simp add: seq_assoc)
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
  have 3: "E ERead \<rho> i = B ([Read k], Atom (AVar k)) (\<rho>, i)"
    by (cases i) (auto simp: seq_def seq_assoc) 
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
  from 3 have 4: "E (ENeg e) \<rho> i = B (ss1 @ ss2, FNeg a) (\<rho>, i)"
    apply (cases "seq (Ss ss1) (Ss ss2) (\<rho>,i)") apply auto
    apply (case_tac "A a aa") apply auto done
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
  