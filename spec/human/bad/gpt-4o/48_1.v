Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Fixpoint check_palindrome (s : string) (i : nat) : bool :=
  let len := String.length s in
  match i <? len / 2 with
  | true =>
    match String.get i s, String.get (len - 1 - i) s with
    | Some c1, Some c2 => if Ascii.eqb c1 c2 then check_palindrome s (i + 1) else false
    | _, _ => false
    end
  | false => true
  end.

Definition is_palindrome (s : string) : bool := check_palindrome s 0.

Example problem_48_test_case_0 :
  problem_48_spec "" (is_palindrome "").
Proof.
  unfold problem_48_spec.
  simpl.
  split.
  - intros _.
    intros i H.
    simpl in H.
    lia.
  - intros H.
    reflexivity.
Qed.