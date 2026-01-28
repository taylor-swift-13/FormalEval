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

Example test_sum_squares_2 : sum_squares_impl [0%Z; 0%Z; 0%Z; 0%Z; 3%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z] = 27%Z.
Proof.
  unfold sum_squares_impl.
  simpl.
  reflexivity.
Qed.