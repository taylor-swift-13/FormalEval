Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> (q = rev q /\ sum_list q <= w).

Example test_will_it_fly : will_it_fly_spec [30; 14; 2; 4; 4; 5] 10 false.
Proof.
  unfold will_it_fly_spec.
  split.
  - intros H.
    inversion H.
  - intros [H_pal H_sum].
    simpl in H_pal.
    discriminate H_pal.
Qed.