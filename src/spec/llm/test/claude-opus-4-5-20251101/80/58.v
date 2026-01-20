Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition three_consecutive_distinct (s : list ascii) (i : nat) : Prop :=
  match nth_error s i, nth_error s (i + 1), nth_error s (i + 2) with
  | Some c1, Some c2, Some c3 => c1 <> c2 /\ c1 <> c3 /\ c2 <> c3
  | _, _, _ => False
  end.

Definition is_happy_spec (s : list ascii) (result : bool) : Prop :=
  (result = true <->
    (length s >= 3 /\
     forall i, i + 2 < length s -> three_consecutive_distinct s i)) /\
  (result = false <->
    (length s < 3 \/
     exists i, i + 2 < length s /\
       match nth_error s i, nth_error s (i + 1), nth_error s (i + 2) with
       | Some c1, Some c2, Some c3 => c1 = c2 \/ c1 = c3 \/ c2 = c3
       | _, _, _ => False
       end)).

Definition test_string : list ascii :=
  " "%char :: "t"%char :: "h"%char :: "i"%char :: "s"%char :: " "%char ::
  "i"%char :: "s"%char :: " "%char :: "b"%char :: "a"%char :: "c"%char ::
  "b"%char :: "a"%char :: "c"%char :: "b"%char :: "a"%char :: " "%char ::
  "c"%char :: "o"%char :: "m"%char :: "m"%char :: "b"%char :: "e"%char ::
  "n"%char :: "s"%char :: "t"%char :: nil.

Example test_is_happy_bacbacba : is_happy_spec test_string false.
Proof.
  unfold is_happy_spec.
  split.
  - split.
    + intro H. discriminate H.
    + intro H.
      destruct H as [Hlen Hall].
      assert (H20 : 20 + 2 < length test_string).
      { simpl. lia. }
      specialize (Hall 20 H20).
      unfold three_consecutive_distinct in Hall.
      simpl in Hall.
      destruct Hall as [Hneq1 [Hneq2 Hneq3]].
      exfalso.
      apply Hneq1.
      reflexivity.
  - split.
    + intro H.
      right.
      exists 20.
      split.
      * simpl. lia.
      * simpl. left. reflexivity.
    + intro H.
      reflexivity.
Qed.