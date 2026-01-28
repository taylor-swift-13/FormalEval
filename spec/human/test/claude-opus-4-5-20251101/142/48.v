Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.NArith.NArith Coq.Bool.Bool.
Import ListNotations.

Fixpoint sum_transformed (l : list Z) (n : nat) : Z :=
  match l with
  | [] => 0%Z
  | h :: t =>
      let transformed :=
        if (Nat.modulo n 3 =? 0%nat) then (Z.mul h h)
        else if andb (Nat.modulo n 4 =? 0%nat) (negb (Nat.modulo n 3 =? 0%nat)) then Z.mul (Z.mul h h) h
        else h in
      Z.add transformed (sum_transformed t (S n))
  end.

Definition sum_squares_impl (lst : list Z) : Z := sum_transformed lst 0%nat.

Definition problem_142_pre (lst : list Z) : Prop := True.

Definition problem_142_spec (lst : list Z) (output : Z) : Prop :=
  output = sum_squares_impl lst.

Example problem_142_test2 : problem_142_spec [1%Z; (-2)%Z; 2%Z; (-4)%Z; 5%Z; (-6)%Z; 7%Z; (-8)%Z; 9%Z; (-10)%Z; (-8)%Z] 998%Z.
Proof.
  unfold problem_142_spec.
  unfold sum_squares_impl.
  simpl.
  reflexivity.
Qed.