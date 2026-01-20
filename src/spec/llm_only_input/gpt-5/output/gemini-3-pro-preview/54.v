Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Local Open Scope string_scope.

Fixpoint char_in_string (c : ascii) (s : string) : Prop :=
  match s with
  | EmptyString => False
  | String c' s' => c = c' \/ char_in_string c s'
  end.

Definition same_chars_spec (s0 s1 : string) (result : bool) : Prop :=
  result = true <-> (forall c : ascii, char_in_string c s0 <-> char_in_string c s1).

Example same_chars_test : same_chars_spec "eabcdzzzz" "dddzzzzzzzddeddabc" true.
Proof.
  unfold same_chars_spec.
  split.
  - intros _.
    intro c.
    repeat simpl.
    tauto.
  - intros _.
    reflexivity.
Qed.