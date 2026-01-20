Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Import ListNotations.

Open Scope Z_scope.

Definition sum_Z (l : list Z) : Z := fold_right Z.add 0%Z l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> q = rev q /\ sum_Z q <= w.

Example will_it_fly_test :
  will_it_fly_spec [1%Z; 2%Z; 3%Z; 2%Z; 1%Z; 0%Z; 1%Z; 1%Z] 31%Z false.
Proof.
  unfold will_it_fly_spec.
  split.
  - intros H.
    exfalso. discriminate H.
  - intros [Hpal _].
    exfalso.
    apply (f_equal (fun l => nth 1%nat l 0%Z)) in Hpal.
    simpl in Hpal.
    assert (2%Z <> 1%Z) by lia.
    congruence.
Qed.