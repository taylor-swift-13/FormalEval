Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

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

Example test_case_input_a : is_happy_spec ["a"%char] false.
Proof.
  unfold is_happy_spec.
  split.
  - (* Part 1: result = true <-> ... *)
    split; intro H.
    + (* Left to Right: false = true -> ... *)
      discriminate H.
    + (* Right to Left: ... -> false = true *)
      destruct H as [Hlen _].
      simpl in Hlen.
      (* Hlen : 3 <= 1, which is False *)
      repeat apply le_S_n in Hlen.
      inversion Hlen.
  - (* Part 2: result = false <-> ... *)
    split; intro H.
    + (* Left to Right: false = false -> ... *)
      left.
      (* length ["a"] < 3 *)
      simpl.
      unfold lt.
      repeat constructor.
    + (* Right to Left: ... -> false = false *)
      reflexivity.
Qed.