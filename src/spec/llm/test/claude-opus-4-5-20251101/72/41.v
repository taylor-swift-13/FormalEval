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

Example test_will_it_fly : will_it_fly_spec [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z] 8%Z true.
Proof.
  unfold will_it_fly_spec.
  split.
  - intros _.
    split.
    + unfold is_palindrome.
      simpl.
      reflexivity.
    + simpl.
      lia.
  - intros [_ _].
    reflexivity.
Qed.