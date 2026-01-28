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

(* Test case: input = ["eEvisattcanarlere"], output = false *)
Example test_palindrome_new : is_palindrome_spec "eEvisattcanarlere" false.
Proof.
  unfold is_palindrome_spec.
  split.
  - intros H.
    discriminate H.
  - intros H.
    compute in H.
    congruence.
Qed.