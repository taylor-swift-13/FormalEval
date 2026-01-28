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

(* Test case: input = ["aaWas it a car or a cat I saw?bWas it a car osteaabcp on no petsrr a ca t I saw?ca"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "aaWas it a car or a cat I saw?bWas it a car osteaabcp on no petsrr a ca t I saw?ca" false.
Proof.
  unfold is_palindrome_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    vm_compute in H.
    congruence.
Qed.