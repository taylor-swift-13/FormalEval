Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

(* Inductive relation definition for fib4 sequence *)
Inductive fib4_at : nat -> nat -> Prop :=
| fib4_at_0 : fib4_at 0 0
| fib4_at_1 : fib4_at 1 0
| fib4_at_2 : fib4_at 2 2
| fib4_at_3 : fib4_at 3 0
| fib4_at_SSSS : forall i a b c d,
    fib4_at i a ->
    fib4_at (S i) b ->
    fib4_at (S (S i)) c ->
    fib4_at (S (S (S i))) d ->
    fib4_at (S (S (S (S i)))) (a + b + c + d).

(* Pre-condition *)
Definition problem_46_pre (input : nat) : Prop := True.

(* Post-condition specification *)
Definition problem_46_spec (input : nat) (output : nat) : Prop :=
  fib4_at input output.

(* Test case proof *)
Example test_fib4_5 : problem_46_spec 5 4.
Proof.
  unfold problem_46_spec.
  
  (* We need to prove fib4_at 5 4.
     Since 5 = 1 + 4, we use the recursive constructor fib4_at_SSSS with i=1.
     This requires knowing fib4(1), fib4(2), fib4(3), and fib4(4).
     Target sum: fib4(1) + fib4(2) + fib4(3) + fib4(4) = 4 *)
  
  (* Rewrite 4 as the sum of the previous values: 0 + 2 + 0 + 2 *)
  replace 4 with (0 + 2 + 0 + 2) by reflexivity.
  
  (* Apply the inductive step for n=5 (i=1) *)
  apply fib4_at_SSSS.
  
  - (* fib4(1) = 0 *)
    apply fib4_at_1.
    
  - (* fib4(2) = 2 *)
    apply fib4_at_2.
    
  - (* fib4(3) = 0 *)
    apply fib4_at_3.
    
  - (* fib4(4) = 2 *)
    (* Now we need to prove fib4(4) = 2.
       Since 4 = 0 + 4, we use fib4_at_SSSS with i=0.
       Target sum: fib4(0) + fib4(1) + fib4(2) + fib4(3) = 2 *)
    
    (* Rewrite 2 as sum: 0 + 0 + 2 + 0 *)
    replace 2 with (0 + 0 + 2 + 0) by reflexivity.
    
    apply fib4_at_SSSS.
    + apply fib4_at_0.
    + apply fib4_at_1.
    + apply fib4_at_2.
    + apply fib4_at_3.
Qed.