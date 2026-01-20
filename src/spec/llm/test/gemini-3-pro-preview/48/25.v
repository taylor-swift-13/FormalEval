Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Open Scope string_scope.

(* Function definition as provided in the specification *)
Fixpoint string_rev (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => (string_rev s') ++ (String c EmptyString)
  end.

(* Specification definition as provided *)
Definition is_palindrome_spec (text : string) (result : bool) : Prop :=
  result = true <-> text = string_rev text.

(* Test case: input = ["Was it a car orWas it a car or a cat I saw?refer a sacat I saw?"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "Was it a car orWas it a car or a cat I saw?refer a sacat I saw?" false.
Proof.
  unfold is_palindrome_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    compute in H.
    discriminate H.
Qed.