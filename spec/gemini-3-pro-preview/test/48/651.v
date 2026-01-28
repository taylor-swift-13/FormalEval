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

Example test_palindrome_foeman : is_palindrome_spec "foeman,Step on no pets" false.
Proof.
  unfold is_palindrome_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    compute in H.
    discriminate H.
Qed.