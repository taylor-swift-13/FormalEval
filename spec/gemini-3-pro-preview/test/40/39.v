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

Example test_triples_sum_to_zero : triples_sum_to_zero_spec [1; 2; 3; 4; 5; 4] false.
Proof.
  unfold triples_sum_to_zero_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    destruct H as [i [j [k [Hi [Hj [Hk [Hij [Hik [Hjk Hsum]]]]]]]]].
    assert (Hpos: Forall (fun x => x > 0) [1; 2; 3; 4; 5; 4]).
    { repeat (constructor; try lia). }
    rewrite Forall_forall in Hpos.
    assert (Hin_i: In (nth i [1; 2; 3; 4; 5; 4] 0) [1; 2; 3; 4; 5; 4]).
    { apply nth_In; assumption. }
    assert (Hin_j: In (nth j [1; 2; 3; 4; 5; 4] 0) [1; 2; 3; 4; 5; 4]).
    { apply nth_In; assumption. }
    assert (Hin_k: In (nth k [1; 2; 3; 4; 5; 4] 0) [1; 2; 3; 4; 5; 4]).
    { apply nth_In; assumption. }
    apply Hpos in Hin_i.
    apply Hpos in Hin_j.
    apply Hpos in Hin_k.
    lia.
Qed.