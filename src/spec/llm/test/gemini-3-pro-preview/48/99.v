Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Open Scope string_scope.

Fixpoint string_rev (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => (string_rev s') ++ (String c EmptyString)
  end.

Definition is_palindrome_spec (text : string) (result : bool) : Prop :=
  result = true <-> text = string_rev text.

Example test_palindrome_complex : is_palindrome_spec "Was it a caraaWas it a car or a cat I rbWas it a car ostep on no petsr a ca t I saw?ca orWas it a car or a cat I saw?r a sacat I saw?" false.
Proof.
  unfold is_palindrome_spec.
  split.
  - intros H.
    discriminate.
  - intros H.
    compute in H.
    discriminate.
Qed.