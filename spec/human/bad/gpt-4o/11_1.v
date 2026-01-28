Require Import List.
Require Import Ascii.
Require Import String.
Require Import Bool.
Require Import Arith.
Import ListNotations.
Open Scope string_scope.

(* 定义 Spec 规约 *)

(* Pre: inputs have equal length and contain only '0' or '1' characters *)
Definition problem_11_pre (a b : string) : Prop :=
  String.length a = String.length b /\
  forall i,
    i < String.length a ->
      ((String.get i a = Some "0"%char) \/ (String.get i a = Some "1"%char)) /\
      ((String.get i b = Some "0"%char) \/ (String.get i b = Some "1"%char)).

(* 定义 Spec 规约 *)

Definition problem_11_spec (a b output : string) : Prop :=
  String.length a = String.length b /\
  String.length output = String.length a /\
  forall i,
    i < String.length output ->
    (String.get i a = String.get i b -> String.get i output = Some "0"%char) /\
    (String.get i a <> String.get i b -> String.get i output = Some "1"%char).

(* Helper function to compute the XOR of two characters *)
Definition xor_char (c1 c2 : ascii) : ascii :=
  if ascii_dec c1 c2 then "0"%char else "1"%char.

(* Function to compute string XOR *)
Fixpoint string_xor (a b : string) : string :=
  match a, b with
  | EmptyString, EmptyString => EmptyString
  | String c1 s1, String c2 s2 => String (xor_char c1 c2) (string_xor s1 s2)
  | _, _ => EmptyString
  end.

Example test_problem_11_spec :
  problem_11_spec "111000" "101010" "010010".
Proof.
  unfold problem_11_spec.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + intros i Hi. (* The length of the string is 6, thus i ranges from 0 to 5 *)
      assert (Hi': i < 6) by lia.
      destruct i as [|i']; [| destruct i' as [|i']; [| destruct i' as [|i']; [| destruct i' as [|i']; [|destruct i' as [|i']; [| lia]]]]];
      simpl; repeat split; unfold String.get; simpl;
      try solve [reflexivity | destruct (ascii_dec _ _); reflexivity | destruct (ascii_dec _ _); congruence].
Qed.