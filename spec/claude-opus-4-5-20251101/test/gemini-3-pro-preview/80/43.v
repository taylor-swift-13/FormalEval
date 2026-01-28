Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope char_scope.

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

Fixpoint string_to_list (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: string_to_list s'
  end.

Definition test_input : list ascii := string_to_list " this is baaacbacbbat"%string.

Example test_happy_case : is_happy_spec test_input false.
Proof.
  unfold is_happy_spec.
  split.
  - split; intro H.
    + discriminate H.
    + destruct H as [_ Hdist].
      specialize (Hdist 10).
      assert (Hbound: 10 + 2 < length test_input).
      { unfold test_input. simpl. lia. }
      apply Hdist in Hbound.
      unfold three_consecutive_distinct in Hbound.
      unfold test_input in Hbound.
      simpl in Hbound.
      destruct Hbound as [Hneq _].
      exfalso; apply Hneq; reflexivity.
  - split; intro H.
    + right. exists 10. split.
      * unfold test_input. simpl. lia.
      * unfold test_input. simpl. left. reflexivity.
    + reflexivity.
Qed.