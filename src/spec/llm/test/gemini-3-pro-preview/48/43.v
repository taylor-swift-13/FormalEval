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

(* Test case: input = ["aa"], output = true *)
Example test_palindrome_aa : is_palindrome_spec "aa" true.
Proof.
  unfold is_palindrome_spec.
  simpl.
  split.
  - intros H. reflexivity.
  - intros H. reflexivity.
Qed.