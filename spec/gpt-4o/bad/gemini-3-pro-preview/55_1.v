Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

(* 
   Standard definition of Fibonacci sequence.
   We use a nested match to ensure the termination checker is satisfied 
   and to avoid "ill-formed recursive definition" errors.
*)
Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S m => match m with
           | 0 => 1
           | S p => fib p + fib m
           end
  end.

(* 
   Specification definition.
   We interpret the requirement as the existence of a sequence 'f' 
   that satisfies the Fibonacci base cases and recurrence relation,
   and whose n-th term equals fib_n.
*)
Definition fib_spec (n : nat) (fib_n : nat) : Prop :=
  (n = 0 -> fib_n = 0) /\
  (n = 1 \/ n = 2 -> fib_n = 1) /\
  (n >= 3 -> exists f : nat -> nat, 
    f 1 = 1 /\ f 2 = 1 /\ 
    (forall i, 3 <= i <= n -> f i = f (i - 1) + f (i - 2)) /\ 
    fib_n = f n).

(* Test case: input = 10, output = 55 *)
Example fib_test_case : fib_spec 10 55.
Proof.
  unfold fib_spec.
  repeat split.
  
  (* Case n = 0 *)
  - intros H. 
    lia.
    
  (* Case n = 1 or n = 2 *)
  - intros H. 
    lia.
    
  (* Case n >= 3 *)
  - intros H.
    exists fib.
    repeat split.
    
    (* f 1 = 1 *)
    + reflexivity.
    
    (* f 2 = 1 *)
    + reflexivity.
    
    (* Recurrence relation *)
    + intros i H_range.
      (* Ensure i >= 3 structurally *)
      destruct i as [|i0]. lia.
      destruct i0 as [|i1]. lia.
      (* i = S (S i1). Since i >= 3, i1 >= 1. *)
      
      (* Simplify fib (S (S i1)) to fib i1 + fib (S i1) *)
      simpl.
      
      (* Match arguments with the specification *)
      replace (S (S i1) - 1) with (S i1) by lia.
      replace (S (S i1) - 2) with i1 by lia.
      
      (* fib i1 + fib (S i1) = fib (S i1) + fib i1 *)
      apply Nat.add_comm.
      
    (* fib_n = f n *)
    + simpl.
      reflexivity.
Qed.