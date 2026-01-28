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

Example test_will_it_fly : will_it_fly_spec [2%Z; 4%Z; 6%Z; 8%Z; 10%Z; 12%Z; 14%Z; 11%Z; 17%Z; 17%Z; 10%Z; 20%Z; 12%Z] 22%Z false.
Proof.
  unfold will_it_fly_spec.
  split.
  - intros H. discriminate H.
  - intros [Hpal Hsum].
    simpl in Hsum.
    lia.
Qed.