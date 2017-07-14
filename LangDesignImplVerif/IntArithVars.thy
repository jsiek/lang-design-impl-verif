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
  
fun shiftss :: "nat \<Rightarrow> nat \<Rightarrow> stmt list \<Rightarrow> stmt list" where
  "shiftss k c [] = []" |
  "shiftss k c (s#ss) = (let ss' = shiftss k (Suc c) ss in (shifts k c s)#ss')"

(*
fun shiftb :: "nat \<Rightarrow> nat \<Rightarrow> block \<Rightarrow> block" where
  "shiftb k c ([], e) = ([], shifta k c e)" |
  "shiftb k c (s#ss, e) = (let (ss',e') = shiftb k (Suc c) (ss,e)
                           in ((shifts k c s)#ss', e'))"
*)
fun shiftb :: "nat \<Rightarrow> nat \<Rightarrow> block \<Rightarrow> block" where
  "shiftb k c (ss,e) = (let ss' = shiftss k c ss in (ss', shifta k (c + length ss) e))"  
  
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

lemma shiftas_append: "As a (\<rho>1@\<rho>3,i) = As (shifta (length \<rho>2) (length \<rho>1) a) (\<rho>1@\<rho>2@\<rho>3,i)"
  apply simp apply (case_tac "A a (\<rho>1@\<rho>3)") using shifta_append apply auto done 
    
lemma shiftf_append: "F e (\<rho>1@\<rho>3) = F (shiftf (length \<rho>2) (length \<rho>1) e) (\<rho>1@\<rho>2@\<rho>3)"
  apply (cases e)
  using shifta_append apply force
  apply simp apply (case_tac "A x22 (\<rho>1@\<rho>3)") apply auto using shifta_append apply auto
  done

lemma Ss_result: "S s (\<rho>,i) = None \<or> (\<exists> v i'. S s (\<rho>,i) = Some (v#\<rho>,i'))"
  apply (cases s) apply simp apply (case_tac "F x1 \<rho>") apply auto
  apply (case_tac i) apply auto
  done
    
lemma Sss_result: "Ss ss (\<rho>,i) = None \<or> (\<exists> \<rho>' i'. Ss ss (\<rho>,i) = Some (\<rho>'@\<rho>,i') \<and> length \<rho>' = length ss)"
  apply (induction ss arbitrary: \<rho> i)
  apply (force simp: ret_def)
  apply (subgoal_tac "S a (\<rho>,i) = None \<or> (\<exists> v i'. S a (\<rho>,i) = Some (v#\<rho>,i'))")
    prefer 2 apply (rule Ss_result)
  apply (erule disjE) apply force
  apply (erule exE)+ 
  apply (subgoal_tac " Ss ss (v#\<rho>, i') = None \<or>
             (\<exists>\<rho>' i''. Ss ss (v#\<rho>, i') = Some (\<rho>' @ (v#\<rho>), i'') \<and> length \<rho>' = length ss)")
    prefer 2 apply blast
    apply (erule disjE) apply force    
    apply (rule disjI2) apply force
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

lemma shiftss_append_some: assumes Ss_ss: "Ss ss (\<rho>1@\<rho>3,i) = Some (\<rho>@\<rho>1@\<rho>3, i')"
  shows "Ss (shiftss (length \<rho>2) (length \<rho>1) ss) (\<rho>1@\<rho>2@\<rho>3,i) = Some (\<rho>@\<rho>1@\<rho>2@\<rho>3,i')"
  using Ss_ss
proof (induction ss arbitrary: \<rho> \<rho>1 \<rho>2 \<rho>3 i i')
  case Nil
  then show ?case by (simp add: ret_def)
next
  case (Cons s ss)
  show ?case
  proof (cases "S s (\<rho>1@\<rho>3,i)")
    case None
    from Cons None show ?thesis using shifts_append_none by auto
  next
    case (Some a)
    let ?s0 = "(\<rho>1@\<rho>3,i)"
    from Some obtain v i1 where S_s: "S s (\<rho>1@\<rho>3,i) = Some (v#\<rho>1@\<rho>3, i1)"
      using Ss_result[of s "\<rho>1@\<rho>3" i] by auto
    let ?s1 = "(v#\<rho>1@\<rho>3, i1)"
    let ?s2 = "(\<rho>@\<rho>1@\<rho>3,i')"
    from Cons(2) S_s obtain \<rho>0 where S_ss: "Ss ss ?s1 = Some ?s2"
      and r: "\<rho>=\<rho>0@[v]" using Sss_result[of ss "v#\<rho>1@\<rho>3" i1] by auto 
    
    let ?sp = "shifts (length \<rho>2) (length \<rho>1) s" and ?ssp = "(shiftss (length \<rho>2)(length(v#\<rho>1)) ss)"
    let ?s0p = "(\<rho>1@\<rho>2@\<rho>3, i)" and ?s1p = "(v#\<rho>1@\<rho>2@\<rho>3,i1)" and ?s2p = "(\<rho>@\<rho>1@\<rho>2@\<rho>3,i')"

    from S_s have S_sp: "S ?sp ?s0p = Some ?s1p" using shifts_append_some by auto
    from S_ss r have "Ss ss ((v # \<rho>1) @ \<rho>3, i1) = Some (\<rho>0 @ (v # \<rho>1) @ \<rho>3, i')" by simp
    from this r Cons(1)[of "v#\<rho>1" \<rho>3 i1 \<rho>0 i' \<rho>2] have S_ssp: "Ss ?ssp ?s1p = Some ?s2p" by simp
    from S_sp S_ssp r show ?thesis by simp
  qed
qed

(*
lemma shiftb_append: "B (ss,e) (\<rho>1@\<rho>3,i) = B (shiftb (length \<rho>2) (length \<rho>1) (ss,e)) (\<rho>1@\<rho>2@\<rho>3,i)"
  apply (induction ss arbitrary: \<rho>1 \<rho>2 \<rho>3 i e)
  using shifta_append apply force
proof -
  fix s ss and \<rho>1::env and \<rho>2::env and \<rho>3::env and i e
  assume IH: "\<And>\<rho>1 \<rho>2 \<rho>3 i e. B (ss, e) (\<rho>1@\<rho>3, i) = B (shiftb (length \<rho>2) (length \<rho>1) (ss, e))
            (\<rho>1@\<rho>2@\<rho>3, i)" 
  let ?sp = "shifts (length \<rho>2) (length \<rho>1) s" 
  show "B (s # ss, e) (\<rho>1 @ \<rho>3, i) = B (shiftb (length \<rho>2) (length \<rho>1) (s # ss, e)) (\<rho>1@\<rho>2@\<rho>3, i)"
  proof (cases "S s (\<rho>1@\<rho>3,i)")
    case None
    from None have s_sp: "S ?sp (\<rho>1@\<rho>2@\<rho>3,i) = None" using shifts_append_none by blast
    from None s_sp
    show ?thesis apply simp apply (case_tac "shiftb (length \<rho>2) (Suc (length \<rho>1)) (ss, e)") by auto
  next
    case (Some \<sigma>)
    from Some obtain v i' where s: "\<sigma> = (v#(\<rho>1@\<rho>3), i')" using Ss_result[of s "\<rho>1@\<rho>3" i] by auto
    from Some s have s_sp: "S ?sp (\<rho>1@\<rho>2@\<rho>3,i) = Some (v#(\<rho>1@\<rho>2@\<rho>3),i')"
      using shifts_append_some[of s \<rho>1 \<rho>3] by auto
    from IH[of e "v#\<rho>1" \<rho>3 i' \<rho>2] s have
      1: "B (ss,e) \<sigma> = B (shiftb(length \<rho>2)(length (v#\<rho>1))(ss,e)) ((v#\<rho>1)@\<rho>2@\<rho>3,i')" by simp
    from s_sp 1 s Some 
    show ?thesis apply simp apply (case_tac "shiftb (length \<rho>2) (Suc (length \<rho>1)) (ss, e)")
        by (auto simp: seq_assoc) 
  qed
qed
*)

section "Correctness of Flattening"
  
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
    
lemma flatten_correct: "flatten e = (ss, e') \<Longrightarrow> E e \<rho> i = B (ss, e') (\<rho>, i)"
proof (induction e arbitrary: e' \<rho> i ss)
  case (EInt n)
  have "E (EInt n) \<rho> i = Some (n,i)" by simp
  also have "... = B ([], AInt n) (\<rho>, i)" by simp
  also have "... = B (flatten (EInt n)) (\<rho>,i)" by simp
  also from EInt have "... = B (ss,e') (\<rho>,i)" by simp
  finally show ?case .
next
  case ERead
  have "E ERead \<rho> i = B ([Read], AVar 0) (\<rho>, i)"
    by (cases i) (auto simp: seq_def seq_assoc) 
  also have "... = B (flatten ERead) (\<rho>,i)" by simp
  also from ERead have "... = B (ss,e') (\<rho>,i)" by simp 
  finally show ?case .
next
  case (EPrim f e1 e2 e' \<rho> i ss) 
  obtain ss1 a1 where fe1: "flatten e1 = (ss1,a1)" by (case_tac "flatten e1") simp
  obtain ss2 a2 where fe2: "flatten e2 = (ss2,a2)" by (case_tac "flatten e2") simp
  obtain a1' where a1p: "a1' = shifta (length ss2) 0 a1" by auto
  obtain ss2' where ss2p: "shiftss (length ss1) 0 ss2 = ss2'" by auto
  obtain a2' where a2p: "shifta (length ss1) (length ss2) a2 = a2'" by auto
   
  from fe1 fe2 a1p ss2p a2p
  have fp: "flatten (EPrim f e1 e2) = (ss1@ss2'@[Push (FPrim f a1' a2')], AVar 0)" by simp 

  from EPrim fe1 have IH1: "E e1 \<rho> i = B (ss1,a1) (\<rho>,i)" by simp
  show ?case
  proof (cases "E e1 \<rho> i")
    case None
    from Sss_result[of ss1 \<rho> i] have "Ss ss1 (\<rho>,i) = None \<or> (\<exists> \<rho>' i'. Ss ss1 (\<rho>,i) = Some (\<rho>'@\<rho>,i')
        \<and> length \<rho>' = length ss1)" by simp
    from this show ?thesis
    proof
      assume "Ss ss1 (\<rho>,i) = None"
      from this EPrim(3) None fp show ?thesis apply auto done
    next
      assume "\<exists> \<rho>' i'. Ss ss1 (\<rho>,i) = Some (\<rho>'@\<rho>,i') \<and> length \<rho>' = length ss1"
      from this obtain \<rho>' i' where Ss_ss1: "Ss ss1 (\<rho>,i) = Some (\<rho>'@\<rho>,i')" by blast
      from IH1 Ss_ss1 None have "A a1 (\<rho>'@\<rho>) = None" apply (case_tac "A a1 (\<rho>'@\<rho>)") by auto
      from this Ss_ss1 fp EPrim(3) None fe1 fe2 show ?thesis sorry 
    qed   
  next
    case (Some r1)
    from Some obtain n1 i' where Ee1: "E e1 \<rho> i = Some (n1,i')" by (cases r1) simp
    let ?s0 = "(\<rho>,i)"
    from IH1 Ee1 Sss_result[of ss1 \<rho> i] obtain \<rho>1 where Ss_ss1: "Ss ss1 (\<rho>,i) = Some (\<rho>1@\<rho>,i')" and 
      Aa1: "As a1 (\<rho>1@\<rho>,i') = Some (n1,i')" and lr1_ss1: "length \<rho>1 = length ss1"
      apply (case_tac "Ss ss1 (\<rho>,i)") 
      apply (auto simp: seq_def) apply (case_tac "A a1 (\<rho>''@\<rho>)") apply auto done  
    let ?s1 = "(\<rho>1@\<rho>,i')"
    from fe2 EPrim have IH2: "E e2 \<rho> i' = B (ss2,a2) (\<rho>,i')" by simp
    show ?thesis
    proof (cases "E e2 \<rho> i'")
      case None
      then show ?thesis sorry
    next
      case (Some r2)
      from Some obtain n2 i'' where Ee2: "E e2 \<rho> i' = Some (n2,i'')" by (cases r2) simp
      from Ee2 IH2 Sss_result[of ss2 \<rho> i'] obtain \<rho>2 where Sss2: "Ss ss2 (\<rho>,i') = Some (\<rho>2@\<rho>,i'')"
        and Aa2: "As a2 (\<rho>2@\<rho>,i'') = Some (n2,i'')" and lr2_ss2:"length \<rho>2 = length ss2" 
        apply (case_tac "Ss ss2 (\<rho>,i')") apply (auto simp: seq_def)
        apply (case_tac "A a2 (\<rho>''@\<rho>)") apply auto done
      let ?s2 = "(\<rho>2@\<rho>1@\<rho>, i'')"
      
      from Sss2 ss2p lr1_ss1 lr2_ss2 shiftss_append_some[of ss2 "[]" \<rho> i' \<rho>2 i'' \<rho>1]
      have Ss_ss2p: "Ss ss2' ?s1 = Some ?s2" by simp

      from a1p lr1_ss1 lr2_ss2 have "A a1 (\<rho>1@\<rho>) = A a1' (\<rho>2@\<rho>1@\<rho>)" 
        using shifta_append[of a1 "[]" "\<rho>1@\<rho>" \<rho>2]  by simp
      from this Aa1 have As_a1p: "As a1' ?s2 = Some (n1,i'')" apply simp
          apply (case_tac "A a1 (\<rho>1@\<rho>)") apply auto apply (case_tac "A a1' (\<rho>2 @ \<rho>1 @ \<rho>)") by auto
      
      from a2p lr1_ss1 lr2_ss2 have "A a2 (\<rho>2@\<rho>) = A a2' (\<rho>2@\<rho>1@\<rho>)"
        using shifta_append[of a2 \<rho>2 \<rho> \<rho>1] by simp
      from this Aa2 have As_a2p: "As a2' ?s2 = Some (n2,i'')" by simp
          
      from Ee1 Ee2 have Ep: "E (EPrim f e1 e2) \<rho> i = Some (f n1 n2, i'')" by simp

      from fp have "B (flatten (EPrim f e1 e2)) (\<rho>, i) 
            = seq (Ss ss1) (seq (Ss ss2') (seq (Ss [Push (FPrim f a1' a2')]) (As (AVar 0)))) ?s0"
        by (simp add: seq_assoc)
      also from Ss_ss1 have "... = seq (Ss ss2') (seq (Ss [Push (FPrim f a1' a2')]) (As (AVar 0))) ?s1"
        by simp
      also from Ss_ss2p have "... = seq (Ss [Push (FPrim f a1' a2')]) (As (AVar 0)) ?s2" by simp
      also from As_a1p As_a2p have "... = Some (f n1 n2, i'')" apply (simp add: seq_def)
        apply (case_tac "A a1' (\<rho>2 @ \<rho>1 @ \<rho>)") apply auto 
        apply (case_tac "A a2' (\<rho>2 @ \<rho>1 @ \<rho>)") apply (auto simp: ret_def) done
      finally have "B (flatten (EPrim f e1 e2)) (\<rho>, i) = Some (f n1 n2, i'')" .
      
      from this Ep EPrim show ?thesis by simp
    qed
  qed
next
  case (EVar x)
  then show ?case sorry
next
  case (ELet e1 e2)
  then show ?case sorry
qed

  
end
  