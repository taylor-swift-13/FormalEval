Require Import Coq.ZArith.ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition choose_num_spec (x y result : Z) : Prop :=
  (result = -1 <-> (forall n : Z, x <= n <= y -> Z.Odd n)) /\
  (result <> -1 -> 
     Z.Even result /\ 
     x <= result <= y /\ 
     (forall n : Z, x <= n <= y -> Z.Even n -> n <= result)).

Example test_choose_num : choose_num_spec 12 15 14.
Proof.
  unfold choose_num_spec.
  split.
  - (* result = -1 <-> all numbers in range are odd *)
    split.
    + (* 14 = -1 -> all odd *)
      intros H. discriminate H.
    + (* all odd -> 14 = -1 *)
      intros H.
      (* 12 is in range and even, contradiction *)
      assert (H12: 12 <= 12 <= 15) by lia.
      specialize (H 12 H12).
      unfold Z.Odd in H.
      destruct H as [k Hk].
      lia.
  - (* result <> -1 -> properties hold *)
    intros _.
    split.
    + (* 14 is even *)
      unfold Z.Even. exists 7. reflexivity.
    + split.
      * (* 12 <= 14 <= 15 *)
        lia.
      * (* 14 is the largest even in range *)
        intros n Hrange Heven.
        unfold Z.Even in Heven.
        destruct Heven as [k Hk].
        (* n = 2*k, and 12 <= n <= 15 *)
        (* So 12 <= 2*k <= 15, meaning k is 6 or 7 *)
        (* If k = 6, n = 12; if k = 7, n = 14 *)
        (* In both cases n <= 14 *)
        lia.
Qed.