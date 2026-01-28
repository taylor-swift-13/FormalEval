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
  problem_142_spec [3%Z; 6%Z; 12%Z; 15%Z; 18%Z; 21%Z; 24%Z; 27%Z; 30%Z; 21%Z] 34149%Z.
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