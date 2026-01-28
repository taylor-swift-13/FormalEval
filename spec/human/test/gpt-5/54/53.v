Require Import List Ascii String.
Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.

Definition problem_54_pre (s0 s1 : string) : Prop := True.

Definition problem_54_spec (s0 s1 : string) (b : bool) : Prop :=
  let list_s0 := list_ascii_of_string s0 in
  let list_s1 := list_ascii_of_string s1 in
  b = true <-> (forall (c : ascii), In c list_s0 <-> In c list_s1).

Example problem_54_test_example :
  problem_54_spec "abbbabcbc" "1234545" false.
Proof.
  unfold problem_54_spec.
  simpl.
  split.
  - intros H. inversion H.
  - intros H.
    pose proof (H "a") as Ha.
    destruct Ha as [Hlr Hrl].
    assert (Hin0 : In "a" ["a"; "b"; "b"; "b"; "a"; "b"; "c"; "b"; "c"]).
    { left. reflexivity. }
    specialize (Hlr Hin0).
    exfalso.
    destruct Hlr as [H1|Hlr].
    { inversion H1. }
    destruct Hlr as [H2|Hlr].
    { inversion H2. }
    destruct Hlr as [H3|Hlr].
    { inversion H3. }
    destruct Hlr as [H4|Hlr].
    { inversion H4. }
    destruct Hlr as [H5|Hlr].
    { inversion H5. }
    destruct Hlr as [H6|Hlr].
    { inversion H6. }
    destruct Hlr as [H7|Hlr].
    { inversion H7. }
    inversion Hlr.
Qed.