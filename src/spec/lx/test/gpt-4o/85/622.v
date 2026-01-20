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
  add_spec [2%Z; 4%Z; 6%Z; 17%Z; 10%Z; 8%Z; 10%Z; 12%Z; 14%Z; 16%Z; 18%Z; 20%Z; 17%Z; 24%Z; 26%Z; 28%Z; 30%Z] 112%Z.
Proof.
  unfold add_spec.
  intros H.
  simpl.
  reflexivity.
Qed.