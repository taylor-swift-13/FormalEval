Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> (q = rev q /\ sum_list q <= w).

Example test_will_it_fly : will_it_fly_spec [7] 7 true.
Proof.
  unfold will_it_fly_spec.
  split.
  - intros _.
    split.
    + simpl.
      reflexivity.
    + unfold sum_list.
      simpl.
      lia.
  - intros _.
    reflexivity.
Qed.