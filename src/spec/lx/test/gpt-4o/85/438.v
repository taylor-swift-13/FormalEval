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
  add_spec [3%Z; 5%Z; 7%Z; 9%Z; 2%Z; 6%Z; 6%Z; 8%Z; 10%Z; 556%Z; 99%Z; 187%Z; 920%Z; 42%Z; 37%Z; 29%Z; 7%Z; 8%Z; 6%Z; 100%Z] 720%Z.
Proof.
  unfold add_spec.
  intros H.
  simpl.
  reflexivity.
Qed.