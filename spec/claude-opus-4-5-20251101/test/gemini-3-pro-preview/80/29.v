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

Definition test_input := string_to_list " this is bacbacba comment"%string.

Example test_happy_case : is_happy_spec test_input false.
Proof.
  unfold is_happy_spec.
  split.
  - (* Case: result = true <-> ... *)
    split; intro H.
    + (* Left to Right: false = true -> ... *)
      discriminate H.
    + (* Right to Left: ... -> false = true *)
      destruct H as [_ H_all].
      (* We check index 20 where 'm', 'm', 'e' appear *)
      specialize (H_all 20).
      unfold test_input in *.
      simpl in H_all.
      (* 20 + 2 < 25 *)
      assert (H_idx : 20 + 2 < 25). { lia. }
      apply H_all in H_idx.
      destruct H_idx as [H_neq _].
      (* 'm' <> 'm' is a contradiction *)
      contradiction H_neq. reflexivity.
  - (* Case: result = false <-> ... *)
    split; intro H.
    + (* Left to Right: false = false -> ... *)
      right.
      exists 20.
      unfold test_input.
      split.
      * simpl. lia.
      * simpl.
        (* 'm' = 'm' is true *)
        left. reflexivity.
    + (* Right to Left: ... -> false = false *)
      reflexivity.
Qed.