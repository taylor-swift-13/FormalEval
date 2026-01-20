Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition triples_sum_to_zero_spec (l : list Z) (res : bool) : Prop :=
  res = true <->
  (exists i j k : nat,
    (i < length l)%nat /\ (j < length l)%nat /\ (k < length l)%nat /\
    i <> j /\ i <> k /\ j <> k /\
    nth i l 0 + nth j l 0 + nth k l 0 = 0).

Example test_triples_sum_to_zero : triples_sum_to_zero_spec [1] false.
Proof.
  unfold triples_sum_to_zero_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    destruct H as [i [j [k [Hi [Hj [Hk [Hij [Hik [Hjk Hsum]]]]]]]]].
    simpl in Hi, Hj, Hk.
    lia.
Qed.