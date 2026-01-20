Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

Import ListNotations.

Open Scope Z_scope.

Definition sum_Z (l : list Z) : Z := fold_right Z.add 0%Z l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> q = rev q /\ sum_Z q <= w.

Example will_it_fly_test :
  will_it_fly_spec [1%Z; 2%Z; 3%Z; 2%Z; 1%Z; 0%Z; 1%Z] 14%Z false.
Proof.
  unfold will_it_fly_spec.
  split.
  - intros H. exfalso. discriminate H.
  - intros [Hpal Hle].
    exfalso.
    simpl in Hpal.
    assert (Htl := f_equal (@tl Z) Hpal).
    simpl in Htl.
    assert (Hhd := f_equal (fun l => hd 0%Z l) Htl).
    simpl in Hhd.
    discriminate Hhd.
Qed.