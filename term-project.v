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

(*

The primary goal of this term project is to prove the following theorem:

  Theorem the_commutative_diagram :
    forall sp : source_program,
      interpret sp = run (compile sp).

for

* a source language of arithmetic expressions:

    Inductive arithmetic_expression : Type :=
    | Literal : nat -> arithmetic_expression
    | Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
    | Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.
    
    Inductive source_program : Type :=
    | Source_program : arithmetic_expression -> source_program.

* a target language of byte-code instructions:

    Inductive byte_code_instruction : Type :=
    | PUSH : nat -> byte_code_instruction
    | ADD : byte_code_instruction
    | SUB : byte_code_instruction.
    
    Inductive target_program : Type :=
    | Target_program : list byte_code_instruction -> target_program.

* a semantics of expressible values:

    Inductive expressible_value : Type :=
    | Expressible_nat : nat -> expressible_value
    | Expressible_msg : string -> expressible_value.

* a source interpreter

    interpret : source_program -> expressible_value

* a compiler

    compile : source_program -> target_program

* a target interpreter

    run : target_program -> expressible_value

The source for errors is subtraction,
since subtracting two natural numbers does not always yield a natural number:
for example, 3 - 2 is defined but not 2 - 3.

You are expected, at the very least:

* to prove that the specification of the interpreter specifies at most one function

* to implement a source interpreter
  and to verify that it satisfies its specification

* to implement a target interpreter (i.e., a virtual machine)
  and to verify that it satisfies its specification

* to implement a compiler
  and to verify that it satisfies its specification

* to prove that the diagram commutes, i.e., to show that
  interpreting any given expression
  gives the same result as
  compiling this expression and then running the resulting compiled program

Beyond this absolute minimum, in decreasing importance, it would be good:

* to write an accumulator-based compiler and to prove that it satisfies the specification,

* to investigate byte-code verification,

* to investigate decompilation,

* to write a continuation-based interpreter and to prove that it satisfies the specification, and

* if there is any time left, to prove that each of the specifications specifies a unique function.

Also, feel free:

* to expand the source language and the target language with multiplication, quotient, and modulo, and/or

* to implement right-to-left language processors and to verify that the corresponding diagram commutes,
  as in the term project of Intro to CS.

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
| Expressible_nat : nat -> expressible_value
| Expressible_msg : string -> expressible_value.

(* ********** *)

Definition specification_of_evaluate (evaluate : arithmetic_expression -> expressible_value) :=
  (forall n : nat,
     evaluate (Literal n) = Expressible_nat n)
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 ->
       evaluate (Plus ae1 ae2) = Expressible_msg s1)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Plus ae1 ae2) = Expressible_msg s2)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       evaluate (Plus ae1 ae2) = Expressible_nat (n1 + n2)))
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 ->
       evaluate (Minus ae1 ae2) = Expressible_msg s1)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Minus ae1 ae2) = Expressible_msg s2)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       n1 <? n2 = true ->
       evaluate (Minus ae1 ae2) = Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1))))
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       n1 <? n2 = false ->
       evaluate (Minus ae1 ae2) = Expressible_nat (n1 - n2))).

Definition specification_of_interpret (interpret : source_program -> expressible_value) :=
  forall evaluate : arithmetic_expression -> expressible_value,
    specification_of_evaluate evaluate ->
    forall ae : arithmetic_expression,
      interpret (Source_program ae) = evaluate ae.

(* Task 1: 
   a. prove that each of the definitions above specifies at most one function;
   b. implement these two functions; and
   c. verify that each of your functions satisfies its specification.
*)

Theorem there_is_at_most_one_evaluate_function :
  forall (evaluate_1 evaluate_2 : arithmetic_expression -> expressible_value),
    specification_of_evaluate evaluate_1 ->
    specification_of_evaluate evaluate_2 ->
    forall (ae : arithmetic_expression),
      evaluate_1 ae = evaluate_2 ae.
Proof.
  intros evaluate_1 evaluate_2 S_evaluate_1 S_evaluate_2 ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2].

  - unfold specification_of_evaluate in S_evaluate_1.
    destruct S_evaluate_1 as [H_evaluate_1_Literal _].
    unfold specification_of_evaluate in S_evaluate_2.
    destruct S_evaluate_2 as [H_evaluate_2_Literal _].
    rewrite -> H_evaluate_2_Literal.
    exact (H_evaluate_1_Literal n).

  - destruct (evaluate_1 ae1) as [n11 | s11] eqn:H1_ae1;
    destruct (evaluate_1 ae2) as [n12 | s12] eqn:H1_ae2;
    destruct (evaluate_2 ae1) as [n21 | s21] eqn:H2_ae1;
    destruct (evaluate_2 ae2) as [n22 | s22] eqn:H2_ae2.
    * destruct S_evaluate_1 as [_ [[_ [_ H1_nat_nat]] _]].
      destruct S_evaluate_2 as [_ [[_ [_ H2_nat_nat]] _]].
      rewrite -> (H1_nat_nat ae1 ae2 n11 n12 H1_ae1 H1_ae2).
      rewrite -> (H2_nat_nat ae1 ae2 n21 n22 H2_ae1 H2_ae2).
      injection IHae1 as IHae1.
      injection IHae2 as IHae2.
      rewrite -> IHae1.
      rewrite -> IHae2.
      reflexivity.            
    * discriminate IHae2.
    * discriminate IHae1.
    * discriminate IHae1.
    * discriminate IHae2.
    * destruct S_evaluate_1 as [_ [[_ [H1_nat_msg _]] _]].
      destruct S_evaluate_2 as [_ [[_ [H2_nat_msg _]] _]].
      rewrite -> (H1_nat_msg ae1 ae2 n11 s12 H1_ae1 H1_ae2).
      rewrite -> (H2_nat_msg ae1 ae2 n21 s22 H2_ae1 H2_ae2).
      exact IHae2.        
    * discriminate IHae1.
    * discriminate IHae1.
    * discriminate IHae1.
    * discriminate IHae1.
    * destruct S_evaluate_1 as [_ [[H1_msg _] _]].
      destruct S_evaluate_2 as [_ [[H2_msg _] _]].
      rewrite -> (H1_msg ae1 ae2 s11 H1_ae1).
      rewrite -> (H2_msg ae1 ae2 s21 H2_ae1).
      exact IHae1.
    * discriminate IHae2.
    * discriminate IHae1.
    * discriminate IHae1.
    * discriminate IHae2.
    * destruct S_evaluate_1 as [_ [[H1_msg _] _]].
      destruct S_evaluate_2 as [_ [[H2_msg _] _]].
      rewrite -> (H1_msg ae1 ae2 s11 H1_ae1).
      rewrite -> (H2_msg ae1 ae2 s21 H2_ae1).
      exact IHae1.
  
  - destruct (evaluate_1 ae1) as [n11 | s11] eqn:H1_ae1;
    destruct (evaluate_1 ae2) as [n12 | s12] eqn:H1_ae2;
    destruct (evaluate_2 ae1) as [n21 | s21] eqn:H2_ae1;
    destruct (evaluate_2 ae2) as [n22 | s22] eqn:H2_ae2.
    * destruct (n11 <? n12) eqn:H_n11_n12;
      destruct (n21 <? n22) eqn:H_n21_n22;
      injection IHae1 as IHae1;
      injection IHae2 as IHae2.
      + destruct S_evaluate_1 as [_ [_ [_ [_ [H1_nat_nat_lt _]]]]].
        destruct S_evaluate_2 as [_ [_ [_ [_ [H2_nat_nat_lt _]]]]].
        rewrite -> (H1_nat_nat_lt ae1 ae2 n11 n12 H1_ae1 H1_ae2 H_n11_n12).
        rewrite -> (H2_nat_nat_lt ae1 ae2 n21 n22 H2_ae1 H2_ae2 H_n21_n22).
        rewrite -> IHae1.
        rewrite -> IHae2.
        reflexivity.
      + rewrite -> IHae1 in H_n11_n12.
        rewrite -> IHae2 in H_n11_n12.
        rewrite -> H_n11_n12 in H_n21_n22.
        discriminate H_n21_n22.
      + rewrite -> IHae1 in H_n11_n12.
        rewrite -> IHae2 in H_n11_n12.
        rewrite -> H_n11_n12 in H_n21_n22.
        discriminate H_n21_n22.
      + destruct S_evaluate_1 as [_ [_ [_ [_ [_ H1_nat_nat_nmt]]]]].
        destruct S_evaluate_2 as [_ [_ [_ [_ [_ H2_nat_nat_nmt]]]]].
        rewrite -> (H1_nat_nat_nmt ae1 ae2 n11 n12 H1_ae1 H1_ae2 H_n11_n12).
        rewrite -> (H2_nat_nat_nmt ae1 ae2 n21 n22 H2_ae1 H2_ae2 H_n21_n22).
        rewrite -> IHae1.
        rewrite -> IHae2.
        reflexivity.
    * discriminate IHae2.
    * discriminate IHae1.
    * discriminate IHae1.
    * discriminate IHae2.
    * destruct S_evaluate_1 as [_ [_ [_ [H1_nat_msg _]]]].
      destruct S_evaluate_2 as [_ [_ [_ [H2_nat_msg _]]]].
      rewrite -> (H1_nat_msg ae1 ae2 n11 s12 H1_ae1 H1_ae2).
      rewrite -> (H2_nat_msg ae1 ae2 n21 s22 H2_ae1 H2_ae2).
      exact IHae2.      
    * discriminate IHae1.
    * discriminate IHae1.
    * discriminate IHae1.
    * discriminate IHae1.
    * destruct S_evaluate_1 as [_ [_ [H1_msg _]]].
      destruct S_evaluate_2 as [_ [_ [H2_msg _]]].    
      rewrite -> (H1_msg ae1 ae2 s11 H1_ae1).
      rewrite -> (H2_msg ae1 ae2 s21 H2_ae1).
      exact IHae1.
    * discriminate IHae2.
    * discriminate IHae2.
    * discriminate IHae1.
    * discriminate IHae2.
    * destruct S_evaluate_1 as [_ [_ [H1_msg _]]].
      destruct S_evaluate_2 as [_ [_ [H2_msg _]]].    
      rewrite -> (H1_msg ae1 ae2 s11 H1_ae1).
      rewrite -> (H2_msg ae1 ae2 s21 H2_ae1).
      exact IHae1.
Qed.

Theorem there_is_at_most_one_interpret_function :
  forall (interpret_1 interpret_2 : source_program -> expressible_value),
    specification_of_interpret interpret_1 ->
    specification_of_interpret interpret_2 ->  
    forall (evaluate : arithmetic_expression -> expressible_value),
    specification_of_evaluate evaluate ->
    forall (ae : arithmetic_expression),
    interpret_1 (Source_program ae) = evaluate ae ->
    interpret_2 (Source_program ae) = evaluate ae.
Proof.
  intros interpret_1 interpret_2.
  unfold specification_of_interpret.
  intros H_int1 H_int2 evaluate H_ev ae.
  rewrite -> (H_int1 evaluate H_ev).
  rewrite -> (H_int2 evaluate H_ev).
  intro H_true.
  exact H_true.  
Qed.

Fixpoint evaluate (ae : arithmetic_expression) : expressible_value :=
  match ae with
  | Literal n => Expressible_nat n
  | Plus ae1 ae2 => 
      match (evaluate ae1) with
      | Expressible_nat n1 => 
        match (evaluate ae2) with
        | Expressible_nat n2 => Expressible_nat (n1 + n2)
        | Expressible_msg s2 => Expressible_msg s2
        end
      | Expressible_msg s1 => Expressible_msg s1
      end
  | Minus ae1 ae2 => 
      match (evaluate ae1) with
        | Expressible_nat n1 => 
          match (evaluate ae2) with
          | Expressible_nat n2 => 
            match (n1 <? n2) with
            | true => Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
            | false => Expressible_nat (n1 - n2)
            end
          | Expressible_msg s2 => Expressible_msg s2
          end
        | Expressible_msg s1 => Expressible_msg s1
        end
  end.

Lemma fold_unfold_evaluate_literal :
  forall (n : nat),
  evaluate (Literal n) = Expressible_nat n.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_plus :
  forall (ae1 ae2: arithmetic_expression),
    evaluate (Plus ae1 ae2) = 
      match (evaluate ae1) with
      | Expressible_nat n1 => 
        match (evaluate ae2) with
        | Expressible_nat n2 => Expressible_nat (n1 + n2)
        | Expressible_msg s2 => Expressible_msg s2
        end
      | Expressible_msg s1 => Expressible_msg s1
      end.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_minus :
  forall (ae1 ae2: arithmetic_expression),
    evaluate (Minus ae1 ae2) = 
      match (evaluate ae1) with
        | Expressible_nat n1 => 
          match (evaluate ae2) with
          | Expressible_nat n2 => 
            match (n1 <? n2) with
            | true => Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
            | false => Expressible_nat (n1 - n2)
            end
          | Expressible_msg s2 => Expressible_msg s2
          end
        | Expressible_msg s1 => Expressible_msg s1
        end.
Proof.
  fold_unfold_tactic evaluate.
Qed.
   

Theorem evaluate_satisfies_the_specification_of_evaluate :
  specification_of_evaluate evaluate.
Proof.
  unfold specification_of_evaluate.
  split; [ | split].
  - exact (fold_unfold_evaluate_literal).
  - split; [ | split].
    * intros ae1 ae2 s1 H_ev1.
      rewrite -> fold_unfold_evaluate_plus. 
      rewrite -> H_ev1.
      reflexivity.
    * intros ae1 ae2 n1 s2 H_ev1 H_ev2.
      rewrite -> fold_unfold_evaluate_plus.
      rewrite -> H_ev1.
      rewrite -> H_ev2.
      reflexivity.
    * intros ae1 ae2 n1 n2 H_ev1 H_ev2.
      rewrite -> fold_unfold_evaluate_plus.
      rewrite -> H_ev1.
      rewrite -> H_ev2.
      reflexivity.
  - split; [ | split].
    * intros ae1 ae2 s1 H_ev1.
      rewrite -> fold_unfold_evaluate_minus.
      rewrite -> H_ev1.
      reflexivity.
    * intros ae1 ae2 n1 s2 H_ev1 H_ev2.
      rewrite -> fold_unfold_evaluate_minus.
      rewrite -> H_ev1.
      rewrite -> H_ev2.
      reflexivity.
    * split; intros ae1 ae2 n1 n2 H_ev1 H_ev2 H_n1_n2;
      rewrite -> fold_unfold_evaluate_minus;
      rewrite -> H_ev1;
      rewrite -> H_ev2;
      rewrite -> H_n1_n2;
      reflexivity.
Qed.

Definition interpret (sp : source_program) : expressible_value :=
  match sp with
  | Source_program ae => evaluate ae
  end.

Theorem interpret_satisfies_the_specification_of_interpret :
  specification_of_interpret interpret.
Proof.
  unfold specification_of_interpret, interpret.
  intros eval H_eval ae.
  Check (there_is_at_most_one_evaluate_function evaluate eval
         evaluate_satisfies_the_specification_of_evaluate H_eval ae).
  exact (there_is_at_most_one_evaluate_function evaluate eval
         evaluate_satisfies_the_specification_of_evaluate H_eval ae).
Qed.
  
  
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

Definition data_stack := list nat.

(* ********** *)

Inductive result_of_decoding_and_execution : Type :=
| OK : data_stack -> result_of_decoding_and_execution
| KO : string -> result_of_decoding_and_execution.

Definition specification_of_decode_execute (decode_execute : byte_code_instruction -> data_stack -> result_of_decoding_and_execution) :=
  (forall (n : nat)
          (ds : data_stack),
     decode_execute (PUSH n) ds = OK (n :: ds))
  /\
  ((decode_execute ADD nil = KO "ADD: stack underflow")
   /\
   (forall (n2 : nat),
       decode_execute ADD (n2 :: nil) = KO "ADD: stack underflow")
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       decode_execute ADD (n2 :: n1 :: ds) = OK ((n1 + n2) :: ds)))
  /\
  ((decode_execute SUB nil = KO "SUB: stack underflow")
   /\
   (forall (n2 : nat),
       decode_execute SUB (n2 :: nil) = KO "SUB: stack underflow")
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       n1 <? n2 = true ->
       decode_execute SUB (n2 :: n1 :: ds) = KO (String.append "numerical underflow: -" (string_of_nat (n2 - n1))))
   /\
   (forall (n1 n2 : nat)
           (ds : data_stack),
       n1 <? n2 = false ->
       decode_execute SUB (n2 :: n1 :: ds) = OK ((n1 - n2) :: ds))).

(* Task 2:
   a. if there is time, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
*)

Theorem there_is_at_most_one_decode_execute_function :
  forall (decode_execute_1 decode_execute_2 : byte_code_instruction -> data_stack -> result_of_decoding_and_execution),
    specification_of_decode_execute decode_execute_1 ->
    specification_of_decode_execute decode_execute_2 ->
    forall (bci : byte_code_instruction)
           (ds : data_stack),
    decode_execute_1 bci ds = decode_execute_2 bci ds.
Proof.
  intros decode_execute_1 decode_execute_2 S_decode_execute_1 S_decode_execute_2 bci.
  destruct bci as [ n | | ]; intro ds.

  - unfold specification_of_decode_execute in S_decode_execute_1.
    destruct S_decode_execute_1 as [H_decode_execute_1_n _].
    unfold specification_of_decode_execute in S_decode_execute_2.
    destruct S_decode_execute_2 as [H_decode_execute_2_n _].
    rewrite -> H_decode_execute_2_n.
    exact (H_decode_execute_1_n n ds).

  - destruct (decode_execute_1 ADD ds) as [ d1 | s1 ] eqn:H_d1_s1;
    destruct (decode_execute_2 ADD ds) as [ d2 | s2 ] eqn:H_d2_s2;
    destruct S_decode_execute_1 as [_ [H1 _]];
    destruct S_decode_execute_2 as [_ [H2 _]];
    destruct ds as [ | n ds' ].
    + destruct H1 as [H1_nil _].
      rewrite -> H1_nil in H_d1_s1.
      destruct H2 as [H2_nil _].
      rewrite -> H2_nil in H_d2_s2.
      rewrite <- H_d1_s1.
      exact H_d2_s2.
    + destruct ds' as [ | n' ds''].
      ++ destruct H1 as [_ [H1_d_nil _]].
         rewrite -> H1_d_nil in H_d1_s1.
         destruct H2 as [_ [H2_d_nil _]].
         rewrite -> H2_d_nil in H_d2_s2.
         rewrite <- H_d1_s1.
         exact H_d2_s2.
      ++ destruct H1 as [_ [_ H1_ds]].
         rewrite -> H1_ds in H_d1_s1.
         destruct H2 as [_ [_ H2_ds]].
         rewrite -> H2_ds in H_d2_s2.
         rewrite <- H_d1_s1.
         exact H_d2_s2.
    + destruct H1 as [H1_nil _].
      rewrite -> H1_nil in H_d1_s1.
      discriminate H_d1_s1.
    + destruct ds' as [ | n' ds''].
      ++ destruct H1 as [_ [H1_d_nil _]].
         rewrite -> H1_d_nil in H_d1_s1.
         discriminate H_d1_s1.
      ++ destruct H1 as [_ [_ H1_ds]].
         rewrite -> H1_ds in H_d1_s1.
         destruct H2 as [_ [_ H2_ds]].
         rewrite -> H2_ds in H_d2_s2.
         rewrite <- H_d1_s1.
         exact H_d2_s2.
    + destruct H2 as [H2_nil _].
      rewrite -> H2_nil in H_d2_s2.
      discriminate H_d2_s2.
    + destruct ds' as [ | n' ds''].
      ++ destruct H2 as [_ [H2_d_nil _]].
         rewrite -> H2_d_nil in H_d2_s2.
         discriminate H_d2_s2.
      ++ destruct H1 as [_ [_ H1_ds]].
         rewrite -> H1_ds in H_d1_s1.
         destruct H2 as [_ [_ H2_ds]].
         rewrite -> H2_ds in H_d2_s2.
         rewrite <- H_d1_s1.
         exact H_d2_s2.
    + destruct H1 as [H1_nil _].
      rewrite -> H1_nil in H_d1_s1.
      destruct H2 as [H2_nil _].
      rewrite -> H2_nil in H_d2_s2.
      rewrite <- H_d1_s1.
      exact H_d2_s2.
    + destruct ds' as [ | n' ds''].
      ++ destruct H1 as [_ [H1_d_nil _]].
         rewrite -> H1_d_nil in H_d1_s1.
         destruct H2 as [_ [H2_d_nil _]].
         rewrite -> H2_d_nil in H_d2_s2.
         rewrite <- H_d1_s1.
         exact H_d2_s2.
      ++ destruct H1 as [_ [_ H1_ds]].
         rewrite -> H1_ds in H_d1_s1.
         destruct H2 as [_ [_ H2_ds]].
         rewrite -> H2_ds in H_d2_s2.
         rewrite <- H_d1_s1.
         exact H_d2_s2.
         
  - destruct (decode_execute_1 SUB ds) as [ d1 | s1 ] eqn:H_d1_s1;
    destruct (decode_execute_2 SUB ds) as [ d2 | s2 ] eqn:H_d2_s2;
    destruct S_decode_execute_1 as [_ [_ H1]];
    destruct S_decode_execute_2 as [_ [_ H2]];
    destruct ds as [ | n ds'].
    + destruct H1 as [H1_nil _].
      rewrite -> H1_nil in H_d1_s1.
      destruct H2 as [H2_nil _].
      rewrite -> H2_nil in H_d2_s2.
      rewrite <- H_d1_s1.
      exact H_d2_s2.
    + destruct ds' as [ | n' ds''].
      ++ destruct H1 as [_ [H1_d_nil _]].
         rewrite -> H1_d_nil in H_d1_s1.
         discriminate H_d1_s1.
      ++ destruct (n' <? n) eqn:H_n'_n.
         * destruct H1 as [_ [_ [H1_n_n_lt _]]].
           Check (H1_n_n_lt n' n ds'' H_n'_n).
           rewrite -> (H1_n_n_lt n' n ds'' H_n'_n) in H_d1_s1.
           discriminate H_d1_s1.
         * destruct H1 as [_ [_ [_ H1_n_n_lt]]].
           Check (H1_n_n_lt n' n ds'' H_n'_n).
           rewrite -> (H1_n_n_lt n' n ds'' H_n'_n) in H_d1_s1.
           destruct H2 as [_ [_ [_ H2_n_n_lt]]].
           Check (H2_n_n_lt n' n ds'' H_n'_n).
           rewrite -> (H2_n_n_lt n' n ds'' H_n'_n) in H_d2_s2.
           rewrite <- H_d1_s1.
           exact H_d2_s2.
    + destruct H1 as [H1_nil _].
      rewrite -> H1_nil in H_d1_s1.
      discriminate H_d1_s1.
    + destruct ds' as [ | n' ds''].
      ++ destruct H1 as [_ [H1_d_nil _]].
         rewrite -> H1_d_nil in H_d1_s1.
         discriminate H_d1_s1.
      ++ destruct (n' <? n) eqn:H_n'_n.
         * destruct H1 as [_ [_ [H1_n_n_lt _]]].
           Check (H1_n_n_lt n' n ds'' H_n'_n).
           rewrite -> (H1_n_n_lt n' n ds'' H_n'_n) in H_d1_s1.
           discriminate H_d1_s1.
         * destruct H2 as [_ [_ [_ H2_n_n_lt]]].
           Check (H2_n_n_lt n' n ds'' H_n'_n).
           rewrite -> (H2_n_n_lt n' n ds'' H_n'_n) in H_d2_s2.
           discriminate H_d2_s2.
    + destruct H1 as [H1_nil _].
      rewrite -> H1_nil in H_d1_s1.
      destruct H2 as [H2_nil _].
      rewrite -> H2_nil in H_d2_s2.
      rewrite <- H_d1_s1.
      exact H_d2_s2.
    + destruct ds' as [ | n' ds''].
      ++ destruct H2 as [_ [H2_d_nil _]].
         rewrite -> H2_d_nil in H_d2_s2.
         discriminate H_d2_s2.
      ++ destruct (n' <? n) eqn:H_n'_n.
         * destruct H2 as [_ [_ [H2_n_n_lt _]]].
           Check (H2_n_n_lt n' n ds'' H_n'_n).
           rewrite -> (H2_n_n_lt n' n ds'' H_n'_n) in H_d2_s2.
           discriminate H_d2_s2.
         * destruct H1 as [_ [_ [_ H1_n_n_lt]]].
           Check (H1_n_n_lt n' n ds'' H_n'_n).
           rewrite -> (H1_n_n_lt n' n ds'' H_n'_n) in H_d1_s1.
           destruct H2 as [_ [_ [_ H2_n_n_lt]]].
           Check (H2_n_n_lt n' n ds'' H_n'_n).
           rewrite -> (H2_n_n_lt n' n ds'' H_n'_n) in H_d2_s2.
           rewrite <- H_d1_s1.
           exact H_d2_s2.
    + destruct H1 as [H1_nil _].
      rewrite -> H1_nil in H_d1_s1.
      destruct H2 as [H2_nil _].
      rewrite -> H2_nil in H_d2_s2.
      rewrite <- H_d1_s1.
      exact H_d2_s2.
    + destruct ds' as [ | n' ds''].
      ++ destruct H1 as [_ [H1_d_nil _]].
         destruct H2 as [_ [H2_d_nil _]].
         rewrite -> H1_d_nil in H_d1_s1.
         rewrite -> H2_d_nil in H_d2_s2.
         rewrite <- H_d1_s1.
         exact H_d2_s2.
      ++ destruct (n' <? n) eqn:H_n'_n.
         * destruct H1 as [_ [_ [H1_n_n_lt _]]].
           Check (H1_n_n_lt n' n ds'' H_n'_n).
           rewrite -> (H1_n_n_lt n' n ds'' H_n'_n) in H_d1_s1.
           destruct H2 as [_ [_ [H2_n_n_lt _]]].
           Check (H2_n_n_lt n' n ds'' H_n'_n).
           rewrite -> (H2_n_n_lt n' n ds'' H_n'_n) in H_d2_s2.
           rewrite <- H_d1_s1.
           exact H_d2_s2.
         * destruct H1 as [_ [_ [_ H1_n_n_lt]]].
           Check (H1_n_n_lt n' n ds'' H_n'_n).
           rewrite -> (H1_n_n_lt n' n ds'' H_n'_n) in H_d1_s1.
           destruct H2 as [_ [_ [_ H2_n_n_lt]]].
           Check (H2_n_n_lt n' n ds'' H_n'_n).
           rewrite -> (H2_n_n_lt n' n ds'' H_n'_n) in H_d2_s2.
           rewrite <- H_d1_s1.
           exact H_d2_s2.
Qed.
    
Definition decode_execute (bci : byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bci with
    | PUSH n =>
       OK (n :: ds)
    | ADD =>
        match ds with
        | nil =>
           KO "ADD: stack underflow"
        | n :: nil =>
           KO "ADD: stack underflow"
        | n2 :: n1 :: ds'' =>
           OK ((n1 + n2) :: ds'') 
        end   
    | SUB =>
        match ds with
        | nil =>
           KO "SUB: stack underflow"
        | n :: nil =>
           KO "SUB: stack underflow"
        | n2 :: n1 :: ds'' =>
            match (n1 <? n2) with
            | true => KO (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
            | false => OK ((n1 - n2) :: ds'')
            end
        end
  end.

Lemma fold_unfold_decode_execute_push :
  forall (n : nat)
         (ds : data_stack),
    decode_execute (PUSH n) ds = OK (n :: ds).
Proof.
  fold_unfold_tactic decode_execute.
Qed.  

Lemma fold_unfold_decode_execute_add :  
  forall (ds : data_stack),
  decode_execute ADD ds = 
    match ds with
    | nil =>
       KO "ADD: stack underflow"
    | n :: nil =>
       KO "ADD: stack underflow"
    | n2 :: n1 :: ds'' =>
       OK ((n1 + n2) :: ds'') 
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
      | n :: nil =>
         KO "SUB: stack underflow"
      | n2 :: n1 :: ds'' =>
          match (n1 <? n2) with
          | true => KO (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
          | false => OK ((n1 - n2) :: ds'')
          end
      end.
Proof. 
  fold_unfold_tactic decode_execute.
Qed.    
   
Theorem decode_execute_satisfies_the_specification_of_decode_execute :
  specification_of_decode_execute decode_execute.
Proof.
  unfold specification_of_decode_execute.
  split; [ | split].
  - exact (fold_unfold_decode_execute_push).
  - split; [ | split].
    * exact (fold_unfold_decode_execute_add nil).
    * intro n.
      exact (fold_unfold_decode_execute_add (n :: nil)).
    * intros n1 n2 ds.
      exact (fold_unfold_decode_execute_add (n2 :: n1 :: ds)).
  - split; [ | split].
    * exact (fold_unfold_decode_execute_sub nil).
    * intro n.
      exact (fold_unfold_decode_execute_sub (n :: nil)).
    * split; intros n1 n2 ds H_n1_n2;
      rewrite -> fold_unfold_decode_execute_sub;
      rewrite -> H_n1_n2;
      reflexivity.
Qed. 
      
(* ********** *)

(* Specification of the virtual machine: *)

Definition specification_of_fetch_decode_execute_loop (fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution) :=
  forall decode_execute : byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_decode_execute decode_execute ->
    (forall ds : data_stack,
        fetch_decode_execute_loop nil ds = OK ds)
    /\
    (forall (bci : byte_code_instruction)
            (bcis' : list byte_code_instruction)
            (ds ds' : data_stack),
        decode_execute bci ds = OK ds' ->
        fetch_decode_execute_loop (bci :: bcis') ds =
        fetch_decode_execute_loop bcis' ds')
    /\
    (forall (bci : byte_code_instruction)
            (bcis' : list byte_code_instruction)
            (ds : data_stack)
            (s : string),
        decode_execute bci ds = KO s ->
        fetch_decode_execute_loop (bci :: bcis') ds =
        KO s).

(* Task 3:
   a. if there is time, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
*)

Theorem there_is_at_most_one_fetch_decode_execute_loop_function :
  forall (fetch_decode_execute_loop_1 fetch_decode_execute_loop_2 : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution),
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop_1 ->
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop_2 ->
    forall (bcis : list byte_code_instruction)
           (ds : data_stack),
   fetch_decode_execute_loop_1 bcis ds = fetch_decode_execute_loop_2 bcis ds.
Proof.
  intros fetch_decode_execute_loop_1 fetch_decode_execute_loop_2 S_fetch_decode_execute_loop_1 S_fetch_decode_execute_loop_2 bcis.
  unfold specification_of_fetch_decode_execute_loop in S_fetch_decode_execute_loop_1.
  unfold specification_of_fetch_decode_execute_loop in S_fetch_decode_execute_loop_2.
  assert (H_fdel1 := S_fetch_decode_execute_loop_1 decode_execute decode_execute_satisfies_the_specification_of_decode_execute).
  assert (H_fdel2 := S_fetch_decode_execute_loop_2 decode_execute decode_execute_satisfies_the_specification_of_decode_execute).
  clear S_fetch_decode_execute_loop_1.
  clear S_fetch_decode_execute_loop_2.
  
  induction bcis as [ | bci bcis' IHbcis'];
  intro ds.

  - destruct H_fdel1 as [S1_nil_ds _].
    destruct H_fdel2 as [S2_nil_ds _].
    rewrite -> S2_nil_ds.
    exact (S1_nil_ds ds).

  - destruct (decode_execute bci ds) as [ ds' | ds' ] eqn:H_OK_KO.
    + destruct H_fdel1 as [_ [S1_bcis_ds _]].
      Check (S1_bcis_ds bci bcis' ds ds' H_OK_KO).
      rewrite -> (S1_bcis_ds bci bcis' ds ds' H_OK_KO).
      destruct H_fdel2 as [_ [S2_bcis_ds _]].
      Check (S2_bcis_ds bci bcis' ds ds' H_OK_KO).
      rewrite -> (S2_bcis_ds bci bcis' ds ds' H_OK_KO).
      exact (IHbcis' ds').

    + destruct H_fdel1 as [_ [_ S1_bcis_ds]].
      Check (S1_bcis_ds bci bcis' ds ds' H_OK_KO).
      rewrite -> (S1_bcis_ds bci bcis' ds ds' H_OK_KO).
      destruct H_fdel2 as [_ [_ S2_bcis_ds]].
      Check (S2_bcis_ds bci bcis' ds ds' H_OK_KO).
      rewrite -> (S2_bcis_ds bci bcis' ds ds' H_OK_KO).
      reflexivity.
Qed.

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

Theorem fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop :
  specification_of_fetch_decode_execute_loop fetch_decode_execute_loop.
Proof.
  unfold specification_of_fetch_decode_execute_loop.
  intros decode_execute' S_decode_execute.
  assert (one_decode_execute :=
            there_is_at_most_one_decode_execute_function
            decode_execute decode_execute'
            decode_execute_satisfies_the_specification_of_decode_execute
            S_decode_execute).
  split; [ | split].
  - exact fold_unfold_fetch_decode_execute_loop_nil.
  - intros bci bcis' ds ds' H_decode_execute.
    rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
    Check (one_decode_execute bci ds).
    rewrite -> (one_decode_execute bci ds).
    rewrite -> H_decode_execute.
    reflexivity.
  - intros bci bcis' ds s H_decode_execute.
    rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
    rewrite -> (one_decode_execute bci ds).
    rewrite -> H_decode_execute.
    reflexivity. (* The proof of the second and the third sub-case are very similar *)
Qed.

(* ********** *)

(* Task 4:
   Prove that for any lists of byte-code instructions bci1s and bci2s,
   and for any data stack ds,
   executing the concatenation of bci1s and bci2s (i.e., bci1s ++ bci2s) with ds
   gives the same result as
   (1) executing bci1s with ds, and then
   (2) executing bci2s with the resulting data stack, if there exists one.
*)

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

Theorem about_fetch_decode_execute_loop' :
  forall (bci1s bci2s : list byte_code_instruction)
         (ds ds': data_stack)
         (s: string),
    ((fetch_decode_execute_loop bci1s ds = OK ds') ->
     (fetch_decode_execute_loop (bci1s ++ bci2s) ds = fetch_decode_execute_loop bci2s ds'))
    /\
    ((fetch_decode_execute_loop bci1s ds = KO s) ->
     (fetch_decode_execute_loop (bci1s ++ bci2s) ds = KO s)).
Proof.
  intro bci1s.
  induction bci1s as [ | bci1' bci1s' IHbci1s']; intros bci2s ds ds' s.

  - split;
    intro H_fetch_decode_execute_loop;
    rewrite -> fold_unfold_append_nil;
    rewrite -> fold_unfold_fetch_decode_execute_loop_nil in H_fetch_decode_execute_loop.
    * injection H_fetch_decode_execute_loop as H_fetch_decode_execute_loop.
      rewrite -> H_fetch_decode_execute_loop.
      reflexivity.  
    * discriminate H_fetch_decode_execute_loop.
  - split; intro H_fetch_decode_execute_loop;
    rewrite -> fold_unfold_fetch_decode_execute_loop_cons in H_fetch_decode_execute_loop;
    rewrite -> fold_unfold_append_cons;
    rewrite -> fold_unfold_fetch_decode_execute_loop_cons;
    destruct (decode_execute bci1' ds) as [ds''| s'] eqn:H1_de.
     * destruct (IHbci1s' bci2s ds'' ds' s) as [H1_ok _].
       exact (H1_ok H_fetch_decode_execute_loop).
     * discriminate H_fetch_decode_execute_loop.
     * destruct (IHbci1s' bci2s ds'' ds' s) as [_ H1_ko].
       exact (H1_ko H_fetch_decode_execute_loop).
     * exact H_fetch_decode_execute_loop.
Qed.
      
Theorem equivalence_of_two_about_fetch_decode_execute_loop_theorems :
  (forall (bci1s bci2s : list byte_code_instruction)
         (ds : data_stack),
   fetch_decode_execute_loop (bci1s ++ bci2s) ds =
   match fetch_decode_execute_loop bci1s ds with
   | OK ds' => fetch_decode_execute_loop bci2s ds'
   | KO s => KO s
  end) <->
  forall (bci1s bci2s : list byte_code_instruction)
         (ds ds': data_stack)
         (s: string),
    ((fetch_decode_execute_loop bci1s ds = OK ds') ->
     (fetch_decode_execute_loop (bci1s ++ bci2s) ds = fetch_decode_execute_loop bci2s ds'))
    /\
    ((fetch_decode_execute_loop bci1s ds = KO s) ->
     (fetch_decode_execute_loop (bci1s ++ bci2s) ds = KO s)).
Proof.
  split.
  - intros H_theorem1 bci1s bci2s ds ds' s.
    split; intro H_fetch_decode_execute_loop;
    assert (H_tmp := H_theorem1 bci1s bci2s ds);
    rewrite -> H_fetch_decode_execute_loop in H_tmp;
    exact H_tmp.
  - intros H_theorem2 bci1s bci2s ds.
    destruct (fetch_decode_execute_loop bci1s ds) as [ds'| s] eqn:H_fetch_decode_execute_loop.
    * Check (H_theorem2 bci1s bci2s ds ds' ""%string).
      destruct (H_theorem2 bci1s bci2s ds ds' ""%string) as [H1_ok _].
      exact (H1_ok H_fetch_decode_execute_loop).
    * Check (H_theorem2 bci1s bci2s ds nil s).
      destruct (H_theorem2 bci1s bci2s ds nil s) as [_ H1_ko].
      exact (H1_ko H_fetch_decode_execute_loop).
Qed.


(* ********** *)

Definition specification_of_run (run : target_program -> expressible_value) :=
  forall fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop ->
    (forall (bcis : list byte_code_instruction),
       fetch_decode_execute_loop bcis nil = OK nil ->
       run (Target_program bcis) = Expressible_msg "no result on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (n : nat),
       fetch_decode_execute_loop bcis nil = OK (n :: nil) ->
       run (Target_program bcis) = Expressible_nat n)
    /\
    (forall (bcis : list byte_code_instruction)
            (n n' : nat)
            (ds'' : data_stack),
       fetch_decode_execute_loop bcis nil = OK (n :: n' :: ds'') ->
       run (Target_program bcis) = Expressible_msg "too many results on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (s : string),
       fetch_decode_execute_loop bcis nil = KO s ->
       run (Target_program bcis) = Expressible_msg s).

(* Task 5:
   a. if there is time, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
 *)

Theorem there_is_at_most_one_run_function :
  forall (run_1 run_2 : target_program -> expressible_value),
    specification_of_run run_1 ->
    specification_of_run run_2 ->
      forall tp : target_program,
      run_1 tp = run_2 tp.
Proof.
  intros run_1 run_2 S_run_1 S_run_2 tp.
  destruct tp as [bcis].
  Check (S_run_1 fetch_decode_execute_loop 
         fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop).
  destruct (S_run_1 fetch_decode_execute_loop 
            fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop)
    as [ H1_ok_nil [H1_ok_n_nil [H1_ok_cons H1_ko]]].
  destruct (S_run_2 fetch_decode_execute_loop 
            fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop)
    as [ H2_ok_nil [H2_ok_n_nil [H2_ok_cons H2_ko]]].
  destruct (fetch_decode_execute_loop bcis nil) as [ds | s] eqn:H_fetch_decode_execute_loop.
  - destruct ds as [ | n ds']. 
    * rewrite -> (H2_ok_nil bcis H_fetch_decode_execute_loop).
      exact (H1_ok_nil bcis H_fetch_decode_execute_loop).
    * destruct ds' as [ | n' ds''].
      + rewrite -> (H2_ok_n_nil bcis n H_fetch_decode_execute_loop).
        exact (H1_ok_n_nil bcis n H_fetch_decode_execute_loop).
      + rewrite -> (H2_ok_cons bcis n n' ds'' H_fetch_decode_execute_loop).
        exact (H1_ok_cons bcis n n' ds'' H_fetch_decode_execute_loop).
  - rewrite -> (H2_ko bcis s H_fetch_decode_execute_loop).
    exact (H1_ko bcis s H_fetch_decode_execute_loop).
Qed.

Definition run (tp : target_program) :=
  match tp with
  | Target_program bcis =>
    match fetch_decode_execute_loop bcis nil with
         | OK nil => Expressible_msg "no result on the data stack"
         | OK (n :: nil) => Expressible_nat n
         | OK (n :: n' :: ds'') => Expressible_msg "too many results on the data stack"
         | KO s => Expressible_msg s
    end
  end.

Theorem run_satisfies_the_specification_of_run :
  specification_of_run run.
Proof.
  unfold specification_of_run.
  intros fetch_decode_execute_loop' S_fetch_decode_execute_loop.
  assert (H_fetch_decode_execute_loop := there_is_at_most_one_fetch_decode_execute_loop_function
         fetch_decode_execute_loop fetch_decode_execute_loop'
         fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop
         S_fetch_decode_execute_loop).
  split; [ | split; [ | split]].
  - intros bcis H_fetch_decode_execute_loop'.
    unfold run.
    rewrite -> H_fetch_decode_execute_loop.
    rewrite -> H_fetch_decode_execute_loop'.
    reflexivity.
  - intros bcis n H_fetch_decode_execute_loop'.
    unfold run.
    rewrite -> H_fetch_decode_execute_loop.
    rewrite -> H_fetch_decode_execute_loop'.
    reflexivity.
  - intros bcis n n' ds'' H_fetch_decode_execute_loop'.
    unfold run.
    rewrite -> H_fetch_decode_execute_loop.
    rewrite -> H_fetch_decode_execute_loop'.
    reflexivity.
  - intros bcis s H_fetch_decode_execute_loop'.
    unfold run.
    rewrite -> H_fetch_decode_execute_loop.
    rewrite -> H_fetch_decode_execute_loop'.
    reflexivity.
Qed.

(* ********** *)

Definition specification_of_compile_aux (compile_aux : arithmetic_expression -> list byte_code_instruction) :=
  (forall n : nat,
     compile_aux (Literal n) = PUSH n :: nil)
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile_aux (Plus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil))
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile_aux (Minus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil)).

(* Task 6:
   a. if there is time, prove that the definition above specifies at most one function;
   b. implement this function using list concatenation, i.e., ++; and
   c. verify that your function satisfies the specification.
*)

Theorem there_is_at_most_one_compile_aux_function :
  forall (compile_aux_1 compile_aux_2 : arithmetic_expression -> list byte_code_instruction),
    specification_of_compile_aux compile_aux_1 ->
    specification_of_compile_aux compile_aux_2 ->
    forall ae : arithmetic_expression,
   compile_aux_1 ae = compile_aux_2 ae.
Proof.
  intros compile_aux_1 compile_aux_2 S_compile_aux_1 S_compile_aux_2 ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2].

  - destruct S_compile_aux_1 as [S_compile_aux_1_Literal _].
    destruct S_compile_aux_2 as [S_compile_aux_2_Literal _].
    rewrite -> S_compile_aux_1_Literal.
    rewrite -> S_compile_aux_2_Literal.
    reflexivity.

  - destruct S_compile_aux_1 as [_  [H1_plus _] ].
    destruct S_compile_aux_2 as [_  [H2_plus _] ].
    rewrite -> H1_plus.
    rewrite -> H2_plus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.

  - destruct S_compile_aux_1 as [_  [_ H1_minus] ].
    destruct S_compile_aux_2 as [_  [_ H2_minus] ].
    rewrite -> H1_minus.
    rewrite -> H2_minus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
Qed. 

Fixpoint compile_aux (ae : arithmetic_expression) : list byte_code_instruction :=
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

Theorem compile_aux_satisfies_the_specification_of_compile_aux :
  specification_of_compile_aux compile_aux.
Proof.
  unfold specification_of_compile_aux.
  exact (conj fold_unfold_compile_aux_literal
        (conj fold_unfold_compile_aux_plus
              fold_unfold_compile_aux_minus)).
Qed.

Definition specification_of_compile (compile : source_program -> target_program) :=
  forall compile_aux : arithmetic_expression -> list byte_code_instruction,
    specification_of_compile_aux compile_aux ->
    forall ae : arithmetic_expression,
      compile (Source_program ae) = Target_program (compile_aux ae).

(* Task 7:
   a. if there is time, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
*)

Theorem there_is_at_most_one_compile_function :
  forall (compile_1 compile_2 : source_program -> target_program),
    specification_of_compile compile_1 ->
    specification_of_compile compile_2 ->
      forall sp : source_program,
      compile_1 sp = compile_2 sp.
Proof.
  intros compile_1 compile_2.
  unfold specification_of_compile.
  intros S_compile_1 S_compile_2 [ae].
  rewrite -> (S_compile_1 compile_aux compile_aux_satisfies_the_specification_of_compile_aux ae).
  rewrite -> (S_compile_2 compile_aux compile_aux_satisfies_the_specification_of_compile_aux ae).
  reflexivity.
Qed.
        
Definition compile (sp : source_program) : target_program :=
  match sp with
  | Source_program ae =>  Target_program (compile_aux ae)
  end.

Theorem compile_satisfies_the_specification_of_compile :
  specification_of_compile compile.
Proof.
  unfold specification_of_compile.
  intros compile_aux' S_compile_aux' ae.
  unfold compile.
  Check (there_is_at_most_one_compile_aux_function compile_aux compile_aux'
         compile_aux_satisfies_the_specification_of_compile_aux S_compile_aux' ae).
  rewrite -> (there_is_at_most_one_compile_aux_function compile_aux compile_aux'
              compile_aux_satisfies_the_specification_of_compile_aux S_compile_aux' ae).
  reflexivity.
Qed.

(* Task 8:
   implement an alternative compiler
   using an auxiliary function with an accumulator
   and that does not use ++ but :: instead,
   and prove that it satisfies the specification.

   Subsidiary question:
   Are your compiler and your alternative compiler equivalent?
   How can you tell?
*)

Fixpoint compile_alt_aux (ae : arithmetic_expression) (a : list byte_code_instruction) :=
  match ae with
  | Literal n =>
     (PUSH n) :: a
  | Plus ae1 ae2 =>
     compile_alt_aux ae1 (compile_alt_aux ae2 (ADD :: a))
  | Minus ae1 ae2 =>
     compile_alt_aux ae1 (compile_alt_aux ae2 (SUB :: a))
  end.

Lemma fold_unfold_compile_alt_aux_literal :
  forall (n : nat) (a : list byte_code_instruction),
     compile_alt_aux (Literal n) a = (PUSH n) :: a.
Proof.
  fold_unfold_tactic compile_alt_aux.
Qed.

Lemma fold_unfold_compile_alt_aux_plus :
  forall (ae1 ae2 : arithmetic_expression) (a : list byte_code_instruction),
    compile_alt_aux (Plus ae1 ae2) a = 
    compile_alt_aux ae1 (compile_alt_aux ae2 (ADD :: a)).
Proof.
  fold_unfold_tactic compile_alt_aux.
Qed.

Lemma fold_unfold_compile_alt_aux_minus :
  forall (ae1 ae2 : arithmetic_expression) (a : list byte_code_instruction),
    compile_alt_aux (Minus ae1 ae2) a = 
    compile_alt_aux ae1 (compile_alt_aux ae2 (SUB :: a)).
Proof.
  fold_unfold_tactic compile_alt_aux.
Qed. 

Definition compile_alt (sp : source_program) :=
  match sp with
  | Source_program ae => Target_program (compile_alt_aux ae nil)
  end.

(*
Compute (compile_alt_aux (Plus (Literal 3) (Literal 4))(PUSH 1 :: PUSH 2 :: SUB :: nil)).
Compute (compile_alt_aux (Plus (Literal 3) (Literal 4))(PUSH 1 :: SUB :: nil)).
 *)

Lemma about_compile_alt_aux :
  forall (ae : arithmetic_expression)
         (bcis : list byte_code_instruction),
    compile_alt_aux ae bcis = (compile_alt_aux ae nil) ++ bcis.
Proof.
  intro ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2]; intro bcis. 
  - rewrite ->2 fold_unfold_compile_alt_aux_literal.
    rewrite -> fold_unfold_append_cons.
    rewrite -> fold_unfold_append_nil.
    reflexivity.
  - rewrite ->2 fold_unfold_compile_alt_aux_plus.
    rewrite -> (IHae2 (ADD :: bcis)).
    rewrite -> (IHae2 (ADD :: nil)).
    rewrite -> (IHae1 (compile_alt_aux ae2 nil ++ ADD :: bcis)).
    rewrite -> (IHae1 (compile_alt_aux ae2 nil ++ ADD :: nil)).
    Check (List.app_assoc). (* De ja vu *)
    rewrite <-2 List.app_assoc.
    rewrite -> fold_unfold_append_cons.
    rewrite -> fold_unfold_append_nil.
    reflexivity.
  - rewrite ->2 fold_unfold_compile_alt_aux_minus.
    rewrite -> (IHae2 (SUB :: bcis)).
    rewrite -> (IHae2 (SUB :: nil)).
    rewrite -> (IHae1 (compile_alt_aux ae2 nil ++ SUB :: bcis)).
    rewrite -> (IHae1 (compile_alt_aux ae2 nil ++ SUB :: nil)).
    Check (List.app_assoc).
    rewrite <-2 List.app_assoc.
    rewrite -> fold_unfold_append_cons.
    rewrite -> fold_unfold_append_nil.
    reflexivity.
Qed.

Theorem compile_alt_satisfies_the_specification_of_compile :
  specification_of_compile compile_alt.
Proof.
  unfold specification_of_compile, compile_alt.
  intros compile_aux' S_compile_aux' ae.
  rewrite ->(there_is_at_most_one_compile_aux_function compile_aux' compile_aux
         S_compile_aux' compile_aux_satisfies_the_specification_of_compile_aux ae). 
  induction ae.

  - rewrite -> fold_unfold_compile_alt_aux_literal.
    rewrite -> fold_unfold_compile_aux_literal.
    reflexivity.

  - injection IHae1 as IHae1.
    injection IHae2 as IHae2.
    rewrite -> fold_unfold_compile_alt_aux_plus.
    rewrite -> fold_unfold_compile_aux_plus.
    rewrite <- IHae2.
    rewrite <- IHae1.
    rewrite -> about_compile_alt_aux.
    rewrite -> (about_compile_alt_aux ae2 (ADD :: nil)).
    reflexivity.

  - injection IHae1 as IHae1.
    injection IHae2 as IHae2.
    rewrite -> fold_unfold_compile_alt_aux_minus.
    rewrite -> fold_unfold_compile_aux_minus.
    rewrite <- IHae2.
    rewrite <- IHae1.
    rewrite -> about_compile_alt_aux.
    rewrite -> (about_compile_alt_aux ae2 (SUB :: nil)).
    reflexivity.
Qed.


Corollary equivalence_of_compile_and_compile_alt :
  forall sp : source_program,
    compile sp = compile_alt sp.
Proof.
  exact (there_is_at_most_one_compile_function compile compile_alt
         compile_satisfies_the_specification_of_compile
         compile_alt_satisfies_the_specification_of_compile).
Qed.

(* ********** *)

(* Task 9 (the capstone):
   Prove that interpreting an arithmetic expression gives the same result
   as first compiling it and then executing the compiled program.
*)

Lemma capstone_aux :
  forall (ae : arithmetic_expression)
         (ds : data_stack),
    (exists n,
      evaluate ae = Expressible_nat n /\
      fetch_decode_execute_loop (compile_aux ae) ds = OK (n :: ds)) \/
    (exists s,
      evaluate ae = Expressible_msg s /\
      fetch_decode_execute_loop (compile_aux ae) ds = KO s).
Proof.
  intro ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ]; intro ds.
  - left.
    exists n.
    split.
    * rewrite -> fold_unfold_evaluate_literal.
      reflexivity.
    * rewrite -> fold_unfold_compile_aux_literal.
      rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
      rewrite -> fold_unfold_decode_execute_push.
      rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
      reflexivity.
  - destruct (evaluate (Plus ae1 ae2)) as [n | s] eqn:H_eval.
    * left.
      exists n.
      split.
      ** reflexivity.
      ** rewrite -> fold_unfold_compile_aux_plus.
         rewrite -> about_fetch_decode_execute_loop.
         destruct (IHae1 ds) as [[n1 [H1_eval H1_fdel]] | [s1 [H1_eval H1_fdel]]].
         + rewrite -> H1_fdel.
           rewrite -> about_fetch_decode_execute_loop.
           destruct (IHae2 (n1 :: ds)) as [[n2 [H2_eval H2_fdel]] | [s2 [H2_eval H2_fdel]]];
           rewrite -> fold_unfold_evaluate_plus in H_eval;
           rewrite -> H1_eval in H_eval;
           rewrite -> H2_eval in H_eval.
           ++ rewrite -> H2_fdel.
              rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
              rewrite -> fold_unfold_decode_execute_add.
              rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
              injection H_eval as H_eval.
              rewrite -> H_eval.
              reflexivity.
           ++ discriminate H_eval.
         + rewrite -> fold_unfold_evaluate_plus in H_eval.
           rewrite -> H1_eval in H_eval.
           discriminate H_eval.
    * right.
      exists s. 
      split.
      ** reflexivity.
      ** rewrite -> fold_unfold_compile_aux_plus.
         rewrite -> about_fetch_decode_execute_loop.
         destruct (IHae1 ds) as [[n1 [H1_eval H1_fdel]] | [s1 [H1_eval H1_fdel]]].
         + rewrite -> H1_fdel.
           rewrite -> about_fetch_decode_execute_loop.
           destruct (IHae2 (n1 :: ds)) as [[n2 [H2_eval H2_fdel]] | [s2 [H2_eval H2_fdel]]];
           rewrite -> fold_unfold_evaluate_plus in H_eval;
           rewrite -> H1_eval in H_eval;
           rewrite -> H2_eval in H_eval.
           ++ discriminate H_eval.
           ++ rewrite -> H2_fdel.
              injection H_eval as H_eval.
              rewrite -> H_eval.
              reflexivity.
         + rewrite -> H1_fdel.
           rewrite -> fold_unfold_evaluate_plus in H_eval.
           rewrite -> H1_eval in H_eval.
           injection H_eval as H_eval.
           rewrite -> H_eval.
           reflexivity.
  - destruct (evaluate (Minus ae1 ae2)) as [n | s] eqn:H_eval.
    * left.
      exists n.
      split.
      ** reflexivity.
      ** rewrite -> fold_unfold_compile_aux_minus.
         rewrite -> about_fetch_decode_execute_loop.
         destruct (IHae1 ds) as [[n1 [H1_eval H1_fdel]] | [s1 [H1_eval H1_fdel]]].
         + rewrite -> H1_fdel.
           rewrite -> about_fetch_decode_execute_loop.
           destruct (IHae2 (n1 :: ds)) as [[n2 [H2_eval H2_fdel]] | [s2 [H2_eval H2_fdel]]];
           rewrite -> fold_unfold_evaluate_minus in H_eval;
           rewrite -> H1_eval in H_eval;
           rewrite -> H2_eval in H_eval.
           ++ rewrite -> H2_fdel.
              rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
              rewrite -> fold_unfold_decode_execute_sub.
              destruct (n1 <? n2) as [ | ].
              +++ discriminate H_eval.
              +++ rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
                  injection H_eval as H_eval.
                  rewrite -> H_eval.
                  reflexivity.
           ++ discriminate H_eval.
         + rewrite -> fold_unfold_evaluate_minus in H_eval.
           rewrite -> H1_eval in H_eval.
           discriminate H_eval.
    * right.
      exists s. 
      split.
      ** reflexivity.
      ** rewrite -> fold_unfold_compile_aux_minus.
         rewrite -> about_fetch_decode_execute_loop.
         destruct (IHae1 ds) as [[n1 [H1_eval H1_fdel]] | [s1 [H1_eval H1_fdel]]];
         rewrite -> H1_fdel.
         + rewrite -> about_fetch_decode_execute_loop.
           destruct (IHae2 (n1 :: ds)) as [[n2 [H2_eval H2_fdel]] | [s2 [H2_eval H2_fdel]]];
           rewrite -> fold_unfold_evaluate_minus in H_eval;
           rewrite -> H1_eval in H_eval;
           rewrite -> H2_eval in H_eval;
           rewrite -> H2_fdel.
           ++ rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
              rewrite -> fold_unfold_decode_execute_sub.
              destruct (n1 <? n2) as [ | ].
              +++ injection H_eval as H_eval.
                  rewrite <- H_eval.
                  reflexivity.
              +++ discriminate H_eval.
           ++ injection H_eval as H_eval.
              rewrite -> H_eval.
              reflexivity.
         + rewrite -> fold_unfold_evaluate_minus in H_eval.
           rewrite -> H1_eval in H_eval.
           injection H_eval as H_eval.
           rewrite -> H_eval.
           reflexivity.
Qed.

Lemma capstone_aux' :
  forall (ae : arithmetic_expression)
         (ds : data_stack),
    (forall (n : nat),
        evaluate ae = Expressible_nat n ->
        fetch_decode_execute_loop (compile_aux ae) ds = OK (n :: ds)) /\
    (forall (s : string),
        evaluate ae = Expressible_msg s ->
        fetch_decode_execute_loop (compile_aux ae) ds = KO s).
Proof.
  intro ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ]; intro ds. 

  - split.
    -- rewrite -> fold_unfold_evaluate_literal.
       rewrite -> fold_unfold_compile_aux_literal.
       rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
       rewrite -> fold_unfold_decode_execute_push.
       rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
       intros n' H_n_n.
       injection H_n_n as H_n_n.
       rewrite -> H_n_n.
       reflexivity.
    -- rewrite -> fold_unfold_evaluate_literal.
       intros s H_n_s.
       discriminate H_n_s.

  - split.
    -- rewrite -> fold_unfold_evaluate_plus.
       rewrite -> fold_unfold_compile_aux_plus.
       rewrite -> about_fetch_decode_execute_loop.
       destruct (evaluate ae1) as [n1 | s1] eqn:H1_eval.
       + rewrite <- H1_eval in IHae1.
         destruct (IHae1 ds) as [H1_n H1_s].
         rewrite -> (H1_n n1 H1_eval).
         destruct (evaluate ae2) as [n2 | s2] eqn:H2_eval.
          * rewrite <- H2_eval in IHae2.
            rewrite -> about_fetch_decode_execute_loop.
            destruct (IHae2 (n1 :: ds)) as [H2_n H2_s].
            rewrite -> (H2_n n2 H2_eval).
            rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
            rewrite -> fold_unfold_decode_execute_add.
            rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
            intros n H_n1_n2.
            injection H_n1_n2 as H_n1_n2.
            rewrite -> H_n1_n2.
            reflexivity.
          * intros n H_s2_n.
            discriminate H_s2_n.
       + intros n H_s1_n.
         discriminate H_s1_n.
    -- rewrite -> fold_unfold_evaluate_plus.
       rewrite -> fold_unfold_compile_aux_plus.
       rewrite -> about_fetch_decode_execute_loop.     
       destruct (evaluate ae1) as [n1 | s1] eqn:H1_eval.
       + destruct (evaluate ae2) as [n2 | s2] eqn:H2_eval.
         * intros s H_n_s.
           discriminate H_n_s.
         * rewrite <- H1_eval in IHae1.
           destruct (IHae1 ds) as [H1_n H1_s].
           rewrite -> (H1_n n1 H1_eval).
           rewrite <- H2_eval in IHae2.
           rewrite -> about_fetch_decode_execute_loop.
           destruct (IHae2 (n1 :: ds)) as [H2_n H2_s].
           rewrite -> (H2_s s2 H2_eval).
           intros s H_s2_s.
           injection H_s2_s as H_s2_s.
           rewrite -> H_s2_s.
           reflexivity.
       + rewrite <- H1_eval in IHae1.
         destruct (IHae1 ds) as [H1_n H1_s].
         rewrite -> (H1_s s1 H1_eval).
         intros s H_s1_s.
         injection H_s1_s as H_s1_s.
         rewrite -> H_s1_s.
         reflexivity.

  - split.
    -- rewrite -> fold_unfold_evaluate_minus.
       rewrite -> fold_unfold_compile_aux_minus.
       rewrite -> about_fetch_decode_execute_loop.
       destruct (evaluate ae1) as [n1 | s1] eqn:H1_eval.
       + rewrite <- H1_eval in IHae1.
         destruct (IHae1 ds) as [H1_n H1_s].
         rewrite -> (H1_n n1 H1_eval).
         destruct (evaluate ae2) as [n2 | s2] eqn:H2_eval.
         ++ destruct (n1 <? n2) as [ | ] eqn: H_n1_lt_n2. 
            * intros n H_s_n.
              discriminate H_s_n.
            * rewrite <- H2_eval in IHae2.
              rewrite -> about_fetch_decode_execute_loop.
              destruct (IHae2 (n1 :: ds)) as [H2_n H2_s].
              rewrite -> (H2_n n2 H2_eval).
              rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
              rewrite -> fold_unfold_decode_execute_sub.
              rewrite -> H_n1_lt_n2.
              rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
              intros n H_n_n.
              injection H_n_n as H_n_n.
              rewrite -> H_n_n.
              reflexivity.
         ++ intros n H_s2_n.
            discriminate H_s2_n.
       + intros n H_s1_n.
         discriminate H_s1_n.
    -- rewrite -> fold_unfold_evaluate_minus.
       rewrite -> fold_unfold_compile_aux_minus.
       rewrite -> about_fetch_decode_execute_loop.
       destruct (evaluate ae1) as [n1 | s1] eqn:H1_eval.
       + rewrite <- H1_eval in IHae1.
         destruct (IHae1 ds) as [H1_n H1_s].
         rewrite -> (H1_n n1 H1_eval).
         destruct (evaluate ae2) as [n2 | s2] eqn:H2_eval.
         ++ destruct (n1 <? n2) as [ | ] eqn: H_n1_lt_n2.
            * rewrite <- H2_eval in IHae2.
              rewrite -> about_fetch_decode_execute_loop.
              destruct (IHae2 (n1 :: ds)) as [H2_n H2_s].
              rewrite -> (H2_n n2 H2_eval).
              rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
              rewrite -> fold_unfold_decode_execute_sub.
              rewrite -> H_n1_lt_n2.
              intros s H_s_s.
              injection H_s_s as H_s_s.
              rewrite <- H_s_s.
              reflexivity.
            * intros s H_n_s.
              discriminate H_n_s.
         ++ rewrite -> about_fetch_decode_execute_loop.
            rewrite <- H2_eval in IHae2.     
            destruct (IHae2 (n1 :: ds)) as [H2_n H2_s].
            rewrite -> (H2_s s2 H2_eval).
            intros s H_s2_s.
            injection H_s2_s as H_s2_s.
            rewrite -> H_s2_s.
            reflexivity.
       + rewrite <- H1_eval in IHae1.
         destruct (IHae1 ds) as [H1_n H1_s].
         rewrite -> (H1_s s1 H1_eval).
         intros s H_s1_s.
         injection H_s1_s as H_s1_s.
         rewrite -> H_s1_s.
         reflexivity.
Qed.

Theorem capstone :
  forall sp : source_program,
    interpret sp = run (compile sp).
Proof.
  intros [ae].
  unfold interpret.
  unfold compile.
  unfold run.
  Check (capstone_aux ae nil).
  destruct (capstone_aux ae nil) as [[n [H_eval H_fdel]] | [s [H_eval H_fdel]]];
  rewrite -> H_eval;
  rewrite -> H_fdel;
  reflexivity.

  Restart.
  intros [ae].
  unfold interpret.
  unfold compile.
  unfold run.
  destruct (evaluate ae) as [n | s] eqn:H_eval;
  destruct (capstone_aux' ae nil) as [H_n  H_s].
  - rewrite -> (H_n n H_eval).
    reflexivity.
  - rewrite -> (H_s s H_eval).
    reflexivity.
Qed.  

(* ********** *)

(* Byte-code verification:
   the following verifier symbolically executes a byte-code program
   to check whether no underflow occurs during execution
   and whether when the program completes,
   there is one and one only natural number on top of the stack.
   The second argument of verify_aux is a natural number
   that represents the size of the stack.
*)

Fixpoint verify_aux (bcis : list byte_code_instruction) (n : nat) : option nat :=
  match bcis with
    | nil =>
      Some n
    | bci :: bcis' =>
      match bci with
        | PUSH _ =>
          verify_aux bcis' (S n)
        | _ =>
          match n with
            | S (S n') =>
              verify_aux bcis' (S n')
            | _ =>
              None
          end
      end
  end.

Lemma fold_unfold_verify_aux_nil :
  forall (n : nat),
    verify_aux nil n = Some n.
Proof.
  fold_unfold_tactic verify_aux.
Qed.

Lemma fold_unfold_verify_aux_cons :
  forall (bci : byte_code_instruction) (bcis' : list byte_code_instruction) (n : nat),
    verify_aux (bci :: bcis') n = 
      match bci with
        | PUSH _ =>
          verify_aux bcis' (S n)
        | _ =>
          match n with
            | S (S n') =>
              verify_aux bcis' (S n')
            | _ =>
              None
          end
      end.
Proof.
  fold_unfold_tactic verify_aux.
Qed.

Definition verify (p : target_program) : bool :=
  match p with
  | Target_program bcis =>
    match verify_aux bcis 0 with
    | Some n =>
      match n with
      | 1 =>
        true
      | _ =>
        false
      end
    | _ =>
      false
    end
  end.

(* Task 10 (if there is time):
   Prove that the compiler emits code
   that is accepted by the verifier.
*)

Lemma about_verify_aux :
  forall (bci1s bci2s : list byte_code_instruction)
         (n : nat),
    (forall n1 : nat,
        verify_aux bci1s n = Some n1 ->
        verify_aux (bci1s ++ bci2s) n = verify_aux bci2s n1) /\
    (verify_aux bci1s n = None ->
     verify_aux (bci1s ++ bci2s) n = None).
Proof.
  intro bci1s.
  induction bci1s as [ | bci bcis' IHbcis']; intros bci2s n.

  - split.
    * intros n1 H_nil_Some.
      rewrite -> fold_unfold_verify_aux_nil in H_nil_Some.
      injection H_nil_Some as H_nil_Some.
      rewrite -> H_nil_Some.
      rewrite -> fold_unfold_append_nil.
      reflexivity.
    * intro H_nil_None.
      rewrite -> fold_unfold_verify_aux_nil in H_nil_None.
      discriminate H_nil_None.
      
  - split.
    * intros n1 H_cons_Some.
      rewrite -> fold_unfold_verify_aux_cons in H_cons_Some.
      destruct bci as [n' | | ];
      rewrite -> fold_unfold_append_cons;
      rewrite -> fold_unfold_verify_aux_cons.
      + destruct (IHbcis' bci2s (S n)) as [IHbcis'_Some _].
        exact (IHbcis'_Some n1 H_cons_Some).
      + destruct n as [ | n'].
        ++ discriminate H_cons_Some.
        ++ destruct n' as [ | n''].
           +++ discriminate H_cons_Some.
           +++ destruct (IHbcis' bci2s (S n'')) as [IHbcis'_Some _].
               exact (IHbcis'_Some n1 H_cons_Some).
      + destruct n as [ | n'].
        ++ discriminate H_cons_Some.
        ++ destruct n' as [ | n''].
           +++ discriminate H_cons_Some.
           +++ destruct (IHbcis' bci2s (S n'')) as [IHbcis'_Some _].
               exact (IHbcis'_Some n1 H_cons_Some).
    * intro H_cons_None.
      rewrite -> fold_unfold_verify_aux_cons in H_cons_None.
      destruct bci as [n' | | ];
        rewrite -> fold_unfold_append_cons;
        rewrite -> fold_unfold_verify_aux_cons.
      + destruct (IHbcis' bci2s (S n)) as [_ IHbcis'_None].
        exact (IHbcis'_None H_cons_None).
      + destruct n as [ | n'].
        ++ reflexivity.
        ++ destruct n' as [ | n''].
           +++ reflexivity.
           +++ destruct (IHbcis' bci2s (S n'')) as [_ IHbcis'_None].
               exact (IHbcis'_None H_cons_None).
      + destruct n as [ | n'].
        ++ reflexivity.
        ++ destruct n' as [ | n''].
           +++ reflexivity.
           +++ destruct (IHbcis' bci2s (S n'')) as [_ IHbcis'_None].
               exact (IHbcis'_None H_cons_None).
Qed.

Lemma the_compiler_emits_well_behaved_code_aux :
  forall (ae : arithmetic_expression)
         (n : nat),
    verify_aux (compile_aux ae) n = Some (S n).
Proof.
  intro ae.
  induction ae as [ n' | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ]; intro n.
  - rewrite -> fold_unfold_compile_aux_literal.
    rewrite -> fold_unfold_verify_aux_cons.
    rewrite -> fold_unfold_verify_aux_nil.
    reflexivity.
  - rewrite -> fold_unfold_compile_aux_plus.
    Check (about_verify_aux (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) n).
    destruct (about_verify_aux (compile_aux ae1) (compile_aux ae2 ++ ADD :: nil) n) as [H_ae1_Some _].
    Check (H_ae1_Some (S n) (IHae1 n)).
    rewrite -> (H_ae1_Some (S n) (IHae1 n)).
    Check (about_verify_aux (compile_aux ae2) (ADD :: nil) (S n)).
    destruct (about_verify_aux (compile_aux ae2) (ADD :: nil) (S n)) as [H_ae2_Some _].
    Check (H_ae2_Some (S (S n)) (IHae2 (S n))).
    rewrite -> (H_ae2_Some (S (S n)) (IHae2 (S n))).
    rewrite -> fold_unfold_verify_aux_cons.
    rewrite -> fold_unfold_verify_aux_nil.
    reflexivity.
  - rewrite -> fold_unfold_compile_aux_minus.
    Check (about_verify_aux (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) n).
    destruct (about_verify_aux (compile_aux ae1) (compile_aux ae2 ++ SUB :: nil) n) as [H_ae1_Some _].
    Check (H_ae1_Some (S n) (IHae1 n)).
    rewrite -> (H_ae1_Some (S n) (IHae1 n)).
    Check (about_verify_aux (compile_aux ae2) (SUB :: nil) (S n)).
    destruct (about_verify_aux (compile_aux ae2) (SUB :: nil) (S n)) as [H_ae2_Some _].
    Check (H_ae2_Some (S (S n)) (IHae2 (S n))).
    rewrite -> (H_ae2_Some (S (S n)) (IHae2 (S n))).
    rewrite -> fold_unfold_verify_aux_cons.
    rewrite -> fold_unfold_verify_aux_nil.
    reflexivity.
Qed.
   
Theorem the_compiler_emits_well_behaved_code :
  forall sp : source_program,
    verify (compile sp) = true.
Proof.
  intros [ae].
  unfold compile, verify.
  rewrite -> the_compiler_emits_well_behaved_code_aux.
  reflexivity.
Qed.

(* Wrong ways we have tried to think about verify *)

(*
Lemma verify_S :
  forall (bcis : list byte_code_instruction)
         (x n : nat),
  verify_aux bcis x = Some n ->
  verify_aux bcis (S x) = Some (S n).
Proof.
  intro bcis.
  induction bcis as [ | bci bcis' IHbcis']; intros x n H_v.
  - rewrite -> fold_unfold_verify_aux_nil in H_v.
    rewrite -> fold_unfold_verify_aux_nil.
    injection H_v as H_v.
    rewrite -> H_v.
    reflexivity.
  - destruct bci as [ n' | | ]; 
    rewrite -> fold_unfold_verify_aux_cons in H_v;
    rewrite -> fold_unfold_verify_aux_cons.
    * exact (IHbcis' (S x) n H_v).
    * destruct x as [ | x'].
      + discriminate H_v.
      + destruct x' as [ | x''].
        ++ discriminate H_v.
        ++ exact (IHbcis' (S x'') n H_v).
    * destruct x as [ | x'].
      + discriminate H_v.
      + destruct x' as [ | x''].
        ++ discriminate H_v.
        ++ exact (IHbcis' (S x'') n H_v).
Qed.

Lemma verifying_the_concatenation :
  forall (bci1s bci2s : list byte_code_instruction)
         (n1 n2 : nat),
  verify_aux bci1s n1 = Some 1 -> 
  verify_aux bci2s n2 = Some 1 -> 
  verify_aux (bci1s ++ bci2s)
  (n1 + n2) = Some 2.
Proof.
  intro bci1s.
  induction bci1s as [ | bci1 bci1s' IHbci1s']; intros bci2s n1 n2 H_v1 H_v2.

  - rewrite -> fold_unfold_verify_aux_nil in H_v1.
    rewrite -> fold_unfold_append_nil.
    injection H_v1 as H_v1.
    rewrite -> H_v1.
    rewrite -> Nat.add_1_l.
    exact (verify_S bci2s n2 1 H_v2).
  
  - destruct bci1 as [ n1' | | ];
    rewrite -> fold_unfold_verify_aux_cons in H_v1;
    rewrite -> fold_unfold_append_cons;
    rewrite -> fold_unfold_verify_aux_cons.
    * rewrite <- plus_Sn_m.
      exact (IHbci1s' bci2s (S n1) n2 H_v1 H_v2).
    * destruct n1 as [ | n1'].
      + discriminate H_v1.
      + destruct n1' as [ | n1''].
        ++ discriminate H_v1.
        ++ rewrite -> plus_Sn_m.
           destruct (S n1'' + n2) as [ | n] eqn: H_n.
            +++ rewrite -> plus_Sn_m in H_n.
                discriminate H_n.
            +++ rewrite <- H_n.
                exact (IHbci1s' bci2s (S n1'') n2 H_v1 H_v2).
    * destruct n1 as [ | n1'].
      + discriminate H_v1.
      + destruct n1' as [ | n1''].
        ++ discriminate H_v1.
        ++ rewrite -> plus_Sn_m.
           destruct (S n1'' + n2) as [ | n] eqn: H_n.
            +++ rewrite -> plus_Sn_m in H_n.
                discriminate H_n.
            +++ rewrite <- H_n.
                exact (IHbci1s' bci2s (S n1'') n2 H_v1 H_v2).
Qed.
      

Lemma verify_add :
  forall (bcis : list byte_code_instruction)
         (n : nat),
    verify_aux bcis n = Some 2 ->
    verify_aux (bcis ++ ADD :: nil) n = Some 1.
Proof.
  intro bcis.
  induction bcis as [ | bci bcis' IHbcis']; intros n H_v.
    
  - rewrite -> fold_unfold_verify_aux_nil in H_v.
    rewrite -> fold_unfold_append_nil.
    rewrite -> fold_unfold_verify_aux_cons.
    injection H_v as H_v.
    rewrite -> H_v.
    rewrite -> fold_unfold_verify_aux_nil.
    reflexivity.
  - destruct bci as [n' | | ];
    rewrite -> fold_unfold_verify_aux_cons in H_v;
    rewrite -> fold_unfold_append_cons;
    rewrite -> fold_unfold_verify_aux_cons.
    * exact (IHbcis' (S n) H_v).
    * destruct n as [ | n'].
      + discriminate H_v.
      + destruct n' as [ | n''].
        ++ discriminate H_v.
        ++ exact (IHbcis' (S n'') H_v).
    * destruct n as [ | n'].
      + discriminate H_v.
      + destruct n' as [ | n''].
        ++ discriminate H_v.
        ++ exact (IHbcis' (S n'') H_v).
Qed.

Lemma verify_sub :
  forall (bcis : list byte_code_instruction)
         (n : nat),
    verify_aux bcis n = Some 2 ->
    verify_aux (bcis ++ SUB :: nil) n = Some 1.
Proof.
  intro bcis.
  induction bcis as [ | bci bcis' IHbcis']; intros n H_v.
    
  - rewrite -> fold_unfold_verify_aux_nil in H_v.
    rewrite -> fold_unfold_append_nil.
    rewrite -> fold_unfold_verify_aux_cons.
    injection H_v as H_v.
    rewrite -> H_v.
    rewrite -> fold_unfold_verify_aux_nil.
    reflexivity.
  - destruct bci as [n' | | ];
    rewrite -> fold_unfold_verify_aux_cons in H_v;
    rewrite -> fold_unfold_append_cons;
    rewrite -> fold_unfold_verify_aux_cons.
    * exact (IHbcis' (S n) H_v).
    * destruct n as [ | n'].
      + discriminate H_v.
      + destruct n' as [ | n''].
        ++ discriminate H_v.
        ++ exact (IHbcis' (S n'') H_v).
    * destruct n as [ | n'].
      + discriminate H_v.
      + destruct n' as [ | n''].
        ++ discriminate H_v.
        ++ exact (IHbcis' (S n'') H_v).
Qed.     
 

Lemma the_compiler_emits_well_behaved_code_aux :
  forall (ae : arithmetic_expression),
         (*(n : nat),*)
    verify_aux (compile_aux ae) 0 = Some 1.
Proof.
  intro ae.
  induction ae.

  - rewrite -> fold_unfold_compile_aux_literal.
    rewrite -> fold_unfold_verify_aux_cons.
    rewrite -> fold_unfold_verify_aux_nil.
    reflexivity.

  - rewrite -> fold_unfold_compile_aux_plus.
    Check (verifying_the_concatenation).
    assert (H_tmp := verifying_the_concatenation
           (compile_aux ae1) (compile_aux ae2) 0 0
           IHae1 IHae2).
    rewrite -> Nat.add_0_l in H_tmp.
    rewrite -> List.app_assoc.
    exact (verify_add (compile_aux ae1 ++ compile_aux ae2) 0 H_tmp).

  - rewrite -> fold_unfold_compile_aux_minus.
    Check (verifying_the_concatenation).
    assert (H_tmp := verifying_the_concatenation
           (compile_aux ae1) (compile_aux ae2) 0 0
           IHae1 IHae2).
    rewrite -> Nat.add_0_l in H_tmp.
    rewrite -> List.app_assoc.
    exact (verify_sub (compile_aux ae1 ++ compile_aux ae2) 0 H_tmp).
Qed.
*)

(* Subsidiary question:
   What is the practical consequence of this theorem?
*)

(* ********** *)

(* end of term-project.v *)
