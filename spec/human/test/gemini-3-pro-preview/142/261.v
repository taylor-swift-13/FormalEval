Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.NArith.NArith Coq.Bool.Bool.
Import ListNotations.

(* Open Z_scope for Z arithmetic operations. 
   We will explicitly annotate nat literals with %nat to avoid scope confusion. *)
Open Scope Z_scope.

Fixpoint sum_transformed (l : list Z) (n : nat) : Z :=
  match l with
  | [] => 0
  | h :: t =>
      let transformed :=
        (* Use Nat.eqb explicitly to avoid ambiguity with =? notation in Z_scope *)
        if (Nat.eqb (Nat.modulo n 3%nat) 0%nat) then (Z.mul h h)
        else if andb (Nat.eqb (Nat.modulo n 4%nat) 0%nat) (negb (Nat.eqb (Nat.modulo n 3%nat) 0%nat)) 
             then Z.mul (Z.mul h h) h
        else h in
      Z.add transformed (sum_transformed t (S n))
  end.

Definition sum_squares_impl (lst : list Z) : Z := sum_transformed lst 0%nat.

Definition problem_142_pre (lst : list Z) : Prop := True.

Definition problem_142_spec (lst : list Z) (output : Z) : Prop :=
  output = sum_squares_impl lst.

Example test_case_1 : problem_142_spec [6; 7; 8; 9; 10; 11; -13; -14; -15; -16; -17; -17; 18; 19; -11; 20; 20] 6877.
Proof.
  (* Unfold the specification and implementation definitions *)
  unfold problem_142_spec.
  unfold sum_squares_impl.

  (* Simplify the expression by computation. 
     compute evaluates the fixpoint and arithmetic operations. *)
  compute.

  (* The goal reduces to 6877 = 6877 *)
  reflexivity.
Qed.