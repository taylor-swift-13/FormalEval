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

Example test_is_happy_abbaacbaccb : is_happy_spec ("a"%char :: "b"%char :: "b"%char :: "a"%char :: "a"%char :: "c"%char :: "b"%char :: "a"%char :: "c"%char :: "c"%char :: "b"%char :: nil) false.
Proof.
  unfold is_happy_spec.
  split.
  - (* result = true <-> ... *)
    split.
    + (* true -> ... *)
      intro H. discriminate H.
    + (* ... -> true *)
      intro H.
      destruct H as [Hlen Hall].
      specialize (Hall 1).
      assert (H1: 1 + 2 < 11) by lia.
      specialize (Hall H1).
      unfold three_consecutive_distinct in Hall.
      simpl in Hall.
      destruct Hall as [Hneq1 _].
      exfalso.
      apply Hneq1.
      reflexivity.
  - (* result = false <-> ... *)
    split.
    + (* false -> ... *)
      intro H.
      right.
      exists 1.
      split.
      * simpl. lia.
      * simpl. left. reflexivity.
    + (* ... -> false *)
      intro H.
      reflexivity.
Qed.