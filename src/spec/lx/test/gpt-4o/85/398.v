Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Fixpoint sum_even_at_odd_indices (l : list Z) (n : nat) : Z :=
  match l with
  | [] => 0
  | h :: t =>
    if andb (Nat.odd n) (Z.even h) then
      h + sum_even_at_odd_indices t (S n)
    else
      sum_even_at_odd_indices t (S n)
  end.

Definition add_spec (lst : list Z) (output : Z) : Prop :=
  lst <> [] ->
  output = sum_even_at_odd_indices lst 0.

Example add_test :
  add_spec [9%Z; 4%Z; 5%Z; 6%Z; 9%Z; 10%Z; 11%Z; 555%Z; 13%Z; 15%Z] 20%Z.
Proof.
  unfold add_spec.
  intros H.
  simpl.
  reflexivity.
Qed.