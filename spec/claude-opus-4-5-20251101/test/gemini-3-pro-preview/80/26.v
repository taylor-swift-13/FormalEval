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

Example test_happy_case : is_happy_spec ["b"; "a"; "g"; "b"; "e"; "b"; "f"] false.
Proof.
  unfold is_happy_spec.
  split.
  - (* Case: result = true <-> ... *)
    split; intro H.
    + (* Left to Right: false = true -> ... *)
      discriminate H.
    + (* Right to Left: ... -> false = true *)
      destruct H as [_ Hforall].
      (* We demonstrate a contradiction at index 3 where characters are 'b', 'e', 'b' *)
      assert (Hcond : 3 + 2 < length ["b"; "a"; "g"; "b"; "e"; "b"; "f"]).
      { simpl. lia. }
      specialize (Hforall 3 Hcond).
      unfold three_consecutive_distinct in Hforall.
      simpl in Hforall.
      (* Hforall implies 'b' <> 'b', which is false *)
      destruct Hforall as [_ [Hcontra _]].
      exfalso.
      apply Hcontra.
      reflexivity.
  - (* Case: result = false <-> ... *)
    split; intro H.
    + (* Left to Right: false = false -> length < 3 \/ ... *)
      right.
      exists 3.
      split.
      * simpl. lia.
      * simpl. right. left. reflexivity.
    + (* Right to Left: ... -> false = false *)
      reflexivity.
Qed.