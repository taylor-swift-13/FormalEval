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

Definition test_str := [" "; "t"; "h"; "i"; "s"; " "; "i"; "s"; " "; "b"; "a"; "c"; "b"; "a"; "c"; "b"; "a"; " "; "c"; "o"; "m"; "m"; "e"; "n"; "s"; "t"].

Example test_happy_case : is_happy_spec test_str false.
Proof.
  unfold is_happy_spec.
  split.
  - split; intro H.
    + discriminate H.
    + destruct H as [_ Hforall].
      assert (Hidx: 19 + 2 < length test_str).
      { unfold test_str. simpl. lia. }
      specialize (Hforall 19 Hidx).
      unfold three_consecutive_distinct in Hforall.
      unfold test_str in Hforall.
      simpl in Hforall.
      tauto.
  - split; intro H.
    + right.
      exists 19.
      split.
      * unfold test_str. simpl. lia.
      * unfold test_str. simpl.
        tauto.
    + reflexivity.
Qed.