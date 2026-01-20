Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> (q = rev q /\ sum_list q <= w).

Example test_will_it_fly : will_it_fly_spec [13; 3; 4; 5; 3; 3] 42 false.
Proof.
  unfold will_it_fly_spec.
  split.
  - intros H.
    discriminate.
  - intros [H_pal _].
    simpl in H_pal.
    inversion H_pal.
Qed.