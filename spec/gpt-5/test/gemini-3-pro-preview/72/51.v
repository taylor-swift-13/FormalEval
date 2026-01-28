Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_Z (l : list Z) : Z := fold_right Z.add 0%Z l.

Definition will_it_fly_spec (q : list Z) (w : Z) (res : bool) : Prop :=
  res = true <-> q = rev q /\ sum_Z q <= w.

Example test_will_it_fly : will_it_fly_spec [1; 1; 1; 1; 1; 1; 1; 2; 1] 7 false.
Proof.
  unfold will_it_fly_spec.
  split.
  - (* Left to Right implication *)
    intros H.
    discriminate H.
  - (* Right to Left implication *)
    intros [_ H_sum].
    unfold sum_Z in H_sum.
    simpl in H_sum.
    (* H_sum reduces to (10 ?= 7) <> Gt, which is Gt <> Gt, i.e., False *)
    exfalso.
    apply H_sum.
    reflexivity.
Qed.