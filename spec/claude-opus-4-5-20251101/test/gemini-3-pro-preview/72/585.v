Require Import List.
Require Import ZArith.
Require Import Psatz. (* For lia *)
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

Example test_will_it_fly : will_it_fly_spec [7; 2; 4; 5; 5; 2] 16 false.
Proof.
  unfold will_it_fly_spec.
  split.
  - intros H.
    inversion H.
  - intros [H_pal H_sum].
    unfold is_palindrome in H_pal.
    simpl in H_pal.
    inversion H_pal.
Qed.