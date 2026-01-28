Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

(* Specification Definitions *)

Fixpoint factorial (n : nat) : Z :=
  match n with
  | O => 1
  | S n' => Z.of_nat n * factorial n'
  end.

Fixpoint sum_1_to_n (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => Z.of_nat n + sum_1_to_n n'
  end.

Definition f_element (i : nat) : Z :=
  if Nat.even i then factorial i
  else sum_1_to_n i.

Fixpoint f_list (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => f_list n' ++ [f_element n]
  end.

Definition f_spec (n : nat) (result : list Z) : Prop :=
  result = f_list n /\
  length result = n /\
  forall i : nat, (1 <= i <= n)%nat ->
    nth (i - 1) result 0 = f_element i.

(* Example Proof *)

Example test_f_list_5 : f_spec 5 [1; 2; 6; 24; 15].
Proof.
  (* Unfold the specification *)
  unfold f_spec.
  
  (* Split the conjunctions *)
  repeat split.
  
  - (* Goal 1: Verify the result list matches f_list 5 *)
    (* vm_compute evaluates the function completely *)
    vm_compute.
    reflexivity.
    
  - (* Goal 2: Verify the length is 5 *)
    simpl.
    reflexivity.
    
  - (* Goal 3: Verify the nth element property for all valid i *)
    intros i Hi.
    (* Since 1 <= i <= 5, we can enumerate the possible values of i.
       Lia proves that i must be one of these values. *)
    assert (H_cases : i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5)%nat by lia.
    
    (* Destruct the cases to substitute i with concrete values (1, 2, 3, 4, 5).
       This allows vm_compute to evaluate the terms containing i. *)
    destruct H_cases as [-> | [-> | [-> | [-> | ->]]]];
      vm_compute; reflexivity.
Qed.