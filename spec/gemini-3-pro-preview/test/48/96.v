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

Example test_palindrome_complex : is_palindrome_spec "aaWas it a car or na cat I saw?bWas it a car ostep on no peabbbWas it a car oaaaabcar I rbWas it a car ostep on no petsr a ca t I saw?cat I saw?referca ca t I saw?ca" false.
Proof.
  unfold is_palindrome_spec.
  simpl.
  split.
  - intros H. inversion H.
  - intros H. congruence.
Qed.