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
  problem_142_spec [-12%Z; -15%Z; -17%Z; 20%Z; 33%Z; 82%Z; 49%Z; 39%Z; 45%Z; 48%Z; 49%Z; 50%Z; 58%Z; 70%Z; 64%Z; 72%Z; 80%Z; 82%Z; 88%Z; 92%Z; 94%Z; 50%Z; 88%Z] 1494271%Z.
Proof.
  unfold problem_142_spec.
  unfold sum_squares_impl.
  simpl.
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