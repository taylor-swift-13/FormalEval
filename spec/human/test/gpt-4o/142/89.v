Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.NArith.NArith Coq.Bool.Bool.
Import ListNotations.

Open Scope Z_scope.

Fixpoint sum_transformed (l : list Z) (n : nat) : Z :=
  match l with
  | [] => 0%Z
  | h :: t =>
      let transformed :=
        if (Nat.eqb (Nat.modulo n 3) 0%nat) then (Z.mul h h)
        else if andb (Nat.eqb (Nat.modulo n 4) 0%nat) (negb (Nat.eqb (Nat.modulo n 3) 0%nat)) then Z.mul (Z.mul h h) h
        else h in
      Z.add transformed (sum_transformed t (S n))
  end.

Definition sum_squares_impl (lst : list Z) : Z := sum_transformed lst 0%nat.

Definition problem_142_pre (lst : list Z) : Prop := True.

Definition problem_142_spec (lst : list Z) (output : Z) : Prop :=
  output = sum_squares_impl lst.

Example problem_142_test_case_1 :
  problem_142_spec [0%Z; 0%Z; 0%Z; 27%Z; 3%Z; 0%Z; 23%Z; 0%Z; 8%Z; 0%Z; -1%Z; 0%Z] 1796%Z.
Proof.
  unfold problem_142_spec.
  unfold sum_squares_impl.
  simpl.
  (* Index 0: 0^2 = 0 *)
  (* Index 1: 0 (unchanged) *)
  (* Index 2: 0 (unchanged) *)
  (* Index 3: 27^3 = 19683 *)
  (* Index 4: 3^2 = 9 *)
  (* Index 5: 0 (unchanged) *)
  (* Index 6: 23^2 = 529 *)
  (* Index 7: 0 (unchanged) *)
  (* Index 8: 8 (unchanged) *)
  (* Index 9: 0 (unchanged) *)
  (* Index 10: -1 (unchanged) *)
  (* Index 11: 0 (unchanged) *)
  (* Sum = 0 + 0 + 0 + 19683 + 9 + 0 + 529 + 0 + 8 + 0 - 1 + 0 = 1796 *)
  reflexivity.
Qed.

Example problem_142_test_case_2 :
  problem_142_spec [] 0%Z.
Proof.
  unfold problem_142_spec.
  unfold sum_squares_impl.
  simpl.
  reflexivity.
Qed.

Example problem_142_test_case_3 :
  problem_142_spec [-1%Z; -5%Z; 2%Z; -1%Z; -5%Z] (-126%Z).
Proof.
  unfold problem_142_spec.
  unfold sum_squares_impl.
  simpl.
  reflexivity.
Qed.