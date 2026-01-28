Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Fixpoint InStr (a : ascii) (s : string) : Prop :=
  match s with
  | EmptyString => False
  | String b s' => a = b \/ InStr a s'
  end.

Definition same_char_sets (s0 s1 : string) : Prop :=
  forall a : ascii, InStr a s0 <-> InStr a s1.

Definition same_chars_spec (s0 s1 : string) (res : bool) : Prop :=
  (res = true <-> same_char_sets s0 s1) /\
  (res = false <-> ~ same_char_sets s0 s1).

Example test_same_chars : same_chars_spec "eabcdzzzz" "dddzzzzzzzddeddabc" true.
Proof.
  unfold same_chars_spec.
  assert (H_sets : same_char_sets "eabcdzzzz" "dddzzzzzzzddeddabc").
  {
    unfold same_char_sets.
    intro a.
    simpl.
    split; intro H.
    - (* Forward direction: s0 -> s1 *)
      repeat match goal with
      | [ H : _ \/ _ |- _ ] => destruct H as [H|H]
      | [ H : False |- _ ] => contradiction H
      end;
      subst;
      repeat (left; reflexivity || right);
      try contradiction.
    - (* Backward direction: s1 -> s0 *)
      repeat match goal with
      | [ H : _ \/ _ |- _ ] => destruct H as [H|H]
      | [ H : False |- _ ] => contradiction H
      end;
      subst;
      repeat (left; reflexivity || right);
      try contradiction.
  }
  split.
  - (* Case res = true *)
    split; intro; [ assumption | reflexivity ].
  - (* Case res = false *)
    split; intro H.
    + discriminate H.
    + contradiction H.
Qed.