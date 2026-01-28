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

Example test_happy_case : is_happy_spec (string_to_list " this is bacbacba commbenst"%string) false.
Proof.
  unfold is_happy_spec.
  split.
  - (* Case: result = true <-> ... *)
    split; intro H.
    + (* Left to Right: false = true -> ... *)
      discriminate H.
    + (* Right to Left: ... -> false = true *)
      destruct H as [_ Hforall].
      (* Counterexample at index 19: 'o', 'm', 'm' *)
      specialize (Hforall 19).
      assert (Hbound : 19 + 2 < length (string_to_list " this is bacbacba commbenst"%string)).
      { simpl. lia. }
      apply Hforall in Hbound.
      simpl in Hbound.
      destruct Hbound as [_ [_ Hneq]].
      (* Hneq : "m" <> "m" *)
      congruence.
  - (* Case: result = false <-> ... *)
    split; intro H.
    + (* Left to Right: false = false -> ... *)
      right.
      exists 19.
      split.
      * simpl. lia.
      * simpl. right. right. reflexivity.
    + (* Right to Left: ... -> false = false *)
      reflexivity.
Qed.