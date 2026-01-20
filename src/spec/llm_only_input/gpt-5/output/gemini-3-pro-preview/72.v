Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> (q = rev q /\ sum_list q <= w).

Example will_it_fly_test : will_it_fly_spec [3%Z; 2%Z; 3%Z] 9%Z true.
Proof.
  unfold will_it_fly_spec, sum_list.
  split.
  - intros H.
    split.
    + simpl. reflexivity.
    + simpl. lia.
  - intros H.
    reflexivity.
Qed.