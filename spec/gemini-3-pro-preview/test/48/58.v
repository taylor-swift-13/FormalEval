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

(* Test case: input = ["abbbWas it a car or I rbWas it a car ostep on no petsr a ca t I saw?cat I saw?referc"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "abbbWas it a car or I rbWas it a car ostep on no petsr a ca t I saw?cat I saw?referc" false.
Proof.
  unfold is_palindrome_spec.
  split.
  - intros H.
    inversion H.
  - intros H.
    simpl in H.
    discriminate.
Qed.