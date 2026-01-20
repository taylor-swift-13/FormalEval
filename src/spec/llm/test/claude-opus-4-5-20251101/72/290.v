Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Fixpoint sum_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

Definition is_palindrome (l : list Z) : Prop :=
  l = rev l.

Definition will_it_fly_spec (q : list Z) (w : Z) (result : bool) : Prop :=
  result = true <-> (is_palindrome q /\ sum_list q <= w).

Example test_will_it_fly : will_it_fly_spec [1%Z; 2%Z; 11%Z; 4%Z; 5%Z; 6%Z] 10%Z false.
Proof.
  unfold will_it_fly_spec.
  split.
  - intros H.
    discriminate H.
  - intros [H1 H2].
    unfold is_palindrome in H1.
    simpl in H1.
    discriminate H1.
Qed.