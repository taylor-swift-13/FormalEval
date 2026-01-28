Require Import List Ascii String.
Import List.ListNotations.
Open Scope string_scope.

Definition problem_54_pre (s0 s1 : string) : Prop := True.

Definition problem_54_spec (s0 s1 : string) (b : bool) : Prop :=
  let list_s0 := list_ascii_of_string s0 in
  let list_s1 := list_ascii_of_string s1 in
  b = true <-> (forall (c : ascii), In c list_s0 <-> In c list_s1).

Lemma test_same_chars_true:
  problem_54_spec "eabcdzzzz" "dddzzzzzzzddeddabc" true.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intro H; reflexivity.
  - intro H.
    apply eq_sym.
    apply eq_refl.
Qed.