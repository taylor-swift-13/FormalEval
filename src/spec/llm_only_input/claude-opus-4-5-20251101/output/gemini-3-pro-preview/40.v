Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition triples_sum_to_zero_spec (l : list Z) (res : bool) : Prop :=
  res = true <->
  (exists i j k : nat,
    (i < length l)%nat /\ (j < length l)%nat /\ (k < length l)%nat /\
    i <> j /\ i <> k /\ j <> k /\
    nth i l 0 + nth j l 0 + nth k l 0 = 0).

Example test_triples_sum_to_zero :
  triples_sum_to_zero_spec [1%Z; 3%Z; 5%Z; 0%Z] false.
Proof.
  unfold triples_sum_to_zero_spec.
  split.
  - intros H. discriminate.
  - intros [i [j [k [Hi [Hj [Hk [Hij [Hik [Hjk Hsum]]]]]]]]].
    simpl in Hi, Hj, Hk.
    (* We need to check all possible combinations of i, j, k from {0,1,2,3} *)
    (* where i <> j, i <> k, j <> k *)
    (* The list is [1; 3; 5; 0] *)
    (* Possible values: nth 0 = 1, nth 1 = 3, nth 2 = 5, nth 3 = 0 *)
    assert (i < 4)%nat as Hi' by lia.
    assert (j < 4)%nat as Hj' by lia.
    assert (k < 4)%nat as Hk' by lia.
    (* Enumerate all cases *)
    destruct i as [|[|[|[|i']]]]; try lia;
    destruct j as [|[|[|[|j']]]]; try lia;
    destruct k as [|[|[|[|k']]]]; try lia;
    simpl in Hsum;
    try (exfalso; lia).
Qed.