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

Example test_will_it_fly : will_it_fly_spec [1%Z; 2%Z; 2%Z; 3%Z; 1%Z; 0%Z] 18%Z false.
Proof.
  unfold will_it_fly_spec.
  split.
  - intros H.
    discriminate H.
  - intros [H_pal _].
    unfold is_palindrome in H_pal.
    simpl in H_pal.
    discriminate H_pal.
Qed.