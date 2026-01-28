Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["This"%string; "is"%string; "a"%string; "long"%string; "list"%string; "of"%string; "strings"%string; "needs"%string; "tto"%string; "be"%string; "concatenated"%string; "into"%string; "a"%string; "single"%string; "string"%string; "without"%string; "any"%string; "extra"%string; "or"%string; "characters"%string; "hello
world"%string; "in"%string; "between"%string; "them"%string] ("Thisisalonglistofstringsneedsttobeconcatenatedintoasinglestringwithoutanyextraorcharactershello
worldinbetweenthem"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.