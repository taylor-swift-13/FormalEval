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

(* Test case: input = ["awaa"], output = false *)
Example test_palindrome_awaa : is_palindrome_spec "awaa" false.
Proof.
  unfold is_palindrome_spec.
  simpl.
  split.
  - intros H.
    discriminate H.
  - intros H.
    assert (H_eq: String.eqb "awaa" "aawa" = String.eqb "aawa" "aawa").
    { rewrite H. reflexivity. }
    simpl in H_eq.
    discriminate H_eq.
Qed.