(* term-project.v *)
(* YSC3236 2019-2020, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 07 Nov 2019 *)

(* ********** *)

(*
   name: Jianglong Liao
   student ID number: A0152453L
   e-mail address: jlliao@u.yale-nus.edu.sg
*)

(* ********** *)

(* Task 11:

   a. Write a Magritte interpreter for the source language
      that does not operate on natural numbers
      but on syntactic representations of natural numbers.

   b. Write a Magritte interpreter for the target language
      that does not operate on natural numbers
      but on syntactic representations of natural numbers.

   c. Prove that interpreting an arithmetic expression with the Magritte source interpreter
      gives the same result as first compiling it and then executing the compiled program
      with the Magritte target interpreter over an empty data stack.

   d. Prove that the Magritte target interpreter is (essentially)
      a left inverse of the compiler, i.e., it is a decompiler.
*)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.
  
Require Import Arith Bool List String Ascii.

(* caution: only use natural numbers up to 5000 *)
Definition string_of_nat (q0 : nat) : string :=
  let s0 := String (ascii_of_nat (48 + (q0 mod 10))) EmptyString
  in if q0 <? 10
     then s0
     else let q1 := q0 / 10
          in let s1 := String (ascii_of_nat (48 + (q1 mod 10))) s0
             in if q1 <? 10
                then s1
                else let q2 := q1 / 10
                     in let s2 := String (ascii_of_nat (48 + (q2 mod 10))) s1
                        in if q2 <? 10
                           then s2
                           else let q3 := q2 / 10
                                in let s2 := String (ascii_of_nat (48 + (q3 mod 10))) s2
                        in if q3 <? 10
                           then s2
                           else "00000".

Notation "A =n= B" := (beq_nat A B) (at level 70, right associativity).

(* ********** *)

(* Arithmetic expressions: *)

Inductive arithmetic_expression : Type :=
| Literal : nat -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

(* Source programs: *)

Inductive source_program : Type :=
| Source_program : arithmetic_expression -> source_program.

(* ********** *)

(* Semantics: *)

Inductive expressible_value : Type :=
| Expressible_nat : arithmetic_expression -> expressible_value
| Expressible_msg : string -> expressible_value.

(* ********** *)

Definition evaluate (ae : arithmetic_expression) : arithmetic_expression :=
  ae.

Lemma fold_unfold_evaluate :
  forall (ae : arithmetic_expression),
    evaluate ae = ae.
Proof.
  fold_unfold_tactic evaluate.
Qed.  

(*
   a. Write a Magritte interpreter for the source language
      that does not operate on natural numbers
      but on syntactic representations of natural numbers.
 *)

Definition interpret (sp : source_program) : expressible_value :=
  match sp with
  | Source_program ae => Expressible_nat (evaluate ae)
  end. 
  
(* ********** *)

(* Byte-code instructions: *)

Inductive byte_code_instruction : Type :=
| PUSH : nat -> byte_code_instruction
| ADD : byte_code_instruction
| SUB : byte_code_instruction.

(* Target programs: *)

Inductive target_program : Type :=
| Target_program : list byte_code_instruction -> target_program.

(* Data stack: *)

Definition data_stack := list arithmetic_expression.

(* ********** *)

Inductive result_of_decoding_and_execution : Type :=
| OK : data_stack -> result_of_decoding_and_execution
| KO : string -> result_of_decoding_and_execution.  

Definition decode_execute (bcis : byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bcis with
    | PUSH n =>
       OK (Literal n :: ds)
    | ADD =>
        match ds with
        | nil =>
           KO "ADD: stack underflow"
        | ae :: nil =>
           KO "ADD: stack underflow"
        | ae2 :: ae1 :: ds'' =>
           OK ((Plus ae1 ae2) :: ds'') 
        end   
    | SUB =>
        match ds with
        | nil =>
           KO "SUB: stack underflow"
        | ae :: nil =>
           KO "SUB: stack underflow"
        | ae2 :: ae1 :: ds'' =>
           OK ((Minus ae1 ae2) :: ds'')
        end
  end.

Lemma fold_unfold_decode_execute_push :
  forall (n : nat)
         (ds : data_stack),
    decode_execute (PUSH n) ds = OK (Literal n :: ds).
Proof.
  fold_unfold_tactic decode_execute.
Qed.  

Lemma fold_unfold_decode_execute_add :  
  forall (ds : data_stack),
  decode_execute ADD ds = 
    match ds with
        | nil =>
           KO "ADD: stack underflow"
        | ae :: nil =>
           KO "ADD: stack underflow"
        | ae2 :: ae1 :: ds'' =>
           OK ((Plus ae1 ae2) :: ds'') 
    end.  
Proof. 
  fold_unfold_tactic decode_execute.
Qed.    

Lemma fold_unfold_decode_execute_sub :  
  forall (ds : data_stack),
  decode_execute SUB ds = 
    match ds with
        | nil =>
           KO "SUB: stack underflow"
        | ae :: nil =>
           KO "SUB: stack underflow"
        | ae2 :: ae1 :: ds'' =>
           OK ((Minus ae1 ae2) :: ds'')
    end.
Proof. 
  fold_unfold_tactic decode_execute.
Qed.    
      
(* ********** *)

Fixpoint fetch_decode_execute_loop (bcis : list byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bcis with
    | nil =>
       OK ds
    | bci :: bcis' =>
       match decode_execute bci ds with
         | OK ds' =>
           fetch_decode_execute_loop bcis' ds'
         | KO s =>
           KO s
      end
  end.

Lemma fold_unfold_fetch_decode_execute_loop_nil :
  forall (ds : data_stack),
    fetch_decode_execute_loop nil ds = OK ds.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop.
Qed.

Lemma fold_unfold_fetch_decode_execute_loop_cons :
  forall (bci : byte_code_instruction)
         (bcis' : list byte_code_instruction)
         (ds : data_stack),
    fetch_decode_execute_loop (bci :: bcis') ds =
      match decode_execute bci ds with
         | OK ds' =>
           fetch_decode_execute_loop bcis' ds'
         | KO s =>
           KO s
      end.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop.
Qed.

(* ********** *)

Lemma fold_unfold_append_nil :
  forall bci2s : list byte_code_instruction,
    nil ++ bci2s = bci2s.
Proof.
  fold_unfold_tactic List.app.
Qed.

Lemma fold_unfold_append_cons :
  forall (bci1 : byte_code_instruction)
         (bci1s bci2s : list byte_code_instruction),
    (bci1 :: bci1s) ++ bci2s =
    bci1 :: (bci1s ++ bci2s).
Proof.
  fold_unfold_tactic List.app.
Qed.

Theorem about_fetch_decode_execute_loop :
  forall (bci1s bci2s : list byte_code_instruction)
         (ds : data_stack),
   fetch_decode_execute_loop (bci1s ++ bci2s) ds =
   match fetch_decode_execute_loop bci1s ds with
   | OK ds' => fetch_decode_execute_loop bci2s ds'
   | KO s => KO s
  end.
Proof.
  intros bci1s.
  induction bci1s as [ | bci' bcis' IHbcis']; intros bci2s ds.
  - rewrite -> fold_unfold_append_nil.
    rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
    reflexivity.
  - rewrite -> fold_unfold_append_cons.
    rewrite ->2 fold_unfold_fetch_decode_execute_loop_cons.
    destruct (decode_execute bci' ds) as [ds'| s].
    * Check (IHbcis' bci2s ds').
      exact (IHbcis' bci2s ds').
    * reflexivity.
Qed.

(* ********** *)

(*
   b. Write a Magritte interpreter for the target language
      that does not operate on natural numbers
      but on syntactic representations of natural numbers.
*)

Definition run (tp : target_program) : expressible_value :=
  match tp with
  | Target_program bcis =>
    match fetch_decode_execute_loop bcis nil with
         | OK nil => Expressible_msg "no result on the data stack"
         | OK (ae :: nil) => Expressible_nat ae
         | OK (n :: n' :: ds'') => Expressible_msg "too many results on the data stack"
         | KO s => Expressible_msg s
    end
  end.

(* ********** *)

Fixpoint compile_aux (ae : arithmetic_expression) :=
  match ae with
    | Literal n => PUSH n :: nil
    | Plus ae1 ae2 => (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil)
    | Minus ae1 ae2 => (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil)
  end.

Lemma fold_unfold_compile_aux_literal :
  forall n : nat,
    compile_aux (Literal n) = PUSH n :: nil.
Proof.
  fold_unfold_tactic compile_aux.
Qed.

Lemma fold_unfold_compile_aux_plus :
  forall ae1 ae2 : arithmetic_expression,
    compile_aux (Plus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil).
Proof.
  fold_unfold_tactic compile_aux.
Qed.

Lemma fold_unfold_compile_aux_minus :
  forall ae1 ae2 : arithmetic_expression,
    compile_aux (Minus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil).
Proof.
  fold_unfold_tactic compile_aux.
Qed.
        
Definition compile (sp : source_program) :=
  match sp with
  | Source_program ae =>  Target_program (compile_aux ae)
  end.

(* ********** *)

(* the capstone :
   Prove that interpreting an arithmetic expression gives the same result
   as first compiling it and then executing the compiled program.
*)

Lemma capstone_aux:
  forall (ae : arithmetic_expression)
         (ds : data_stack),
    fetch_decode_execute_loop (compile_aux ae) ds = OK (ae :: ds).
Proof.
  intro ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ]; intro ds.
  - rewrite -> fold_unfold_compile_aux_literal.
    rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
    rewrite -> fold_unfold_decode_execute_push.
    rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
    reflexivity.

  - rewrite -> fold_unfold_compile_aux_plus.
    rewrite -> about_fetch_decode_execute_loop.
    rewrite -> (IHae1 ds).
    rewrite -> about_fetch_decode_execute_loop.
    rewrite -> (IHae2 (ae1 :: ds)).
    rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
    rewrite -> fold_unfold_decode_execute_add.
    rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
    reflexivity.

  - rewrite -> fold_unfold_compile_aux_minus.
    rewrite -> about_fetch_decode_execute_loop.
    rewrite -> (IHae1 ds).
    rewrite -> about_fetch_decode_execute_loop.
    rewrite -> (IHae2 (ae1 :: ds)).
    rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
    rewrite -> fold_unfold_decode_execute_sub.
    rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
    reflexivity.
Qed.

(*
   c. Prove that interpreting an arithmetic expression with the Magritte source interpreter
      gives the same result as first compiling it and then executing the compiled program
      with the Magritte target interpreter over an empty data stack.
*)

Theorem capstone :
  forall sp : source_program,
    interpret sp =  run (compile sp).
Proof.
  intros [ae].
  unfold interpret.
  unfold compile.
  unfold run.
  rewrite -> (capstone_aux ae nil).
  rewrite -> fold_unfold_evaluate.
  reflexivity.
Qed.

(*
   d. Prove that the Magritte target interpreter is (essentially)
      a left inverse of the compiler, i.e., it is a decompiler.
*)

Theorem Magritte_interpreter_is_a_left_inverse_of_the_compiler :
  forall (ae : arithmetic_expression),
    run (compile (Source_program ae)) = Expressible_nat ae.
Proof.
  intro ae.
  unfold compile.
  unfold run.
  rewrite -> (capstone_aux ae nil).
  reflexivity.
Qed.

(* ********** *)

(* end of term-project.v *)
