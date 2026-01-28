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

Example test_triples_sum_to_zero : triples_sum_to_zero_spec [1; 2; 3; -6; 7; 0; -1; 2; 1] true.
Proof.
  unfold triples_sum_to_zero_spec.
  split.
  - intros _.
    (* We need to provide three indices i, j, k such that l[i] + l[j] + l[k] = 0.
       Let's pick:
       i = 0 (value 1)
       j = 5 (value 0)
       k = 6 (value -1)
       Sum: 1 + 0 + (-1) = 0.
    *)
    exists 0%nat, 5%nat, 6%nat.
    repeat split.
    + simpl. lia. (* 0 < 9 *)
    + simpl. lia. (* 5 < 9 *)
    + simpl. lia. (* 6 < 9 *)
    + lia.        (* 0 <> 5 *)
    + lia.        (* 0 <> 6 *)
    + lia.        (* 5 <> 6 *)
    + simpl. reflexivity. (* 1 + 0 + -1 = 0 *)
  - intros _. reflexivity.
Qed.