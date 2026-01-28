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

Example test_triples_sum_to_zero : triples_sum_to_zero_spec [1; 2; 3; 4; 5; 2; 4] false.
Proof.
  unfold triples_sum_to_zero_spec.
  split.
  - intros H. discriminate H.
  - intros H.
    destruct H as [i [j [k [Hi [Hj [Hk [_ [_ [_ Hsum]]]]]]]]].
    simpl in Hi, Hj, Hk.
    assert (Hpos: forall n, (n < 7)%nat -> nth n [1; 2; 3; 4; 5; 2; 4] 0 > 0).
    {
      intros n Hn.
      do 7 (destruct n as [|n]; [simpl; lia|]).
      simpl in Hn; lia.
    }
    assert (Hi_val: nth i [1; 2; 3; 4; 5; 2; 4] 0 > 0) by (apply Hpos; lia).
    assert (Hj_val: nth j [1; 2; 3; 4; 5; 2; 4] 0 > 0) by (apply Hpos; lia).
    assert (Hk_val: nth k [1; 2; 3; 4; 5; 2; 4] 0 > 0) by (apply Hpos; lia).
    lia.
Qed.