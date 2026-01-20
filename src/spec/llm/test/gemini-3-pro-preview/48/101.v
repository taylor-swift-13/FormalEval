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

(* Test case: input = ["abbWaas it a car oabbbWasradar it a car oaaaabcar I rbWas it a car ostep on no petsr a ca t I saw?caI saw?refercbccc"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "abbWaas it a car oabbbWasradar it a car oaaaabcar I rbWas it a car ostep on no petsr a ca t I saw?caI saw?refercbccc" false.
Proof.
  unfold is_palindrome_spec.
  split.
  - intros H. inversion H.
  - intros H.
    vm_compute in H.
    discriminate.
Qed.