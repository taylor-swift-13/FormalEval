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
  add_spec [22%Z; 33%Z; 44%Z; 55%Z; 66%Z; 77%Z; 88%Z; 99%Z; 44%Z; 22%Z; 77%Z] 22%Z.
Proof.
  unfold add_spec.
  intros H.
  simpl.
  reflexivity.
Qed.