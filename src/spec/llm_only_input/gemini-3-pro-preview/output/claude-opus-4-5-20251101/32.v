Require Import Reals.
Require Import List.
Require Import Coq.Reals.Rpower.
Require Import Lra. (* For linear real arithmetic *)
Require Import Lia. (* For linear integer arithmetic *)
Import ListNotations.

Open Scope R_scope.

(* Specification Definitions *)
Fixpoint poly (xs : list R) (x : R) : R :=
  match xs with
  | [] => 0
  | c :: cs => c + x * poly cs x
  end.

Definition find_zero_spec (xs : list R) (root : R) : Prop :=
  (exists n : nat, length xs = 2 * n /\ n > 0)%nat /\
  (last xs 0 <> 0) /\
  poly xs root = 0.

(* Test Case Proof *)
Example test_find_zero : find_zero_spec [-10; -2] (-5).
Proof.
  (* Unfold the specification definition *)
  unfold find_zero_spec.
  
  (* Split the conjunctions into separate subgoals *)
  repeat split.
  
  - (* Goal 1: exists n : nat, length [-10; -2] = 2 * n /\ n > 0 *)
    exists 1%nat.
    simpl. (* Reduces length [-10; -2] to 2 *)
    split.
    + (* 2 = 2 * 1 *)
      lia.
    + (* 1 > 0 *)
      lia.
      
  - (* Goal 2: last [-10; -2] 0 <> 0 *)
    simpl. (* Reduces last [-10; -2] 0 to -2 *)
    lra.   (* Prove -2 <> 0 *)
    
  - (* Goal 3: poly [-10; -2] (-5) = 0 *)
    simpl. (* Unfolds poly calculation: -10 + (-5) * (-2 + (-5) * 0) *)
    lra.   (* Solves the arithmetic equation *)
Qed.