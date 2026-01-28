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

(* Test case: input = ["man,Taco"], output = false *)
Example test_palindrome_man_taco : is_palindrome_spec "man,Taco" false.
Proof.
  unfold is_palindrome_spec.
  simpl.
  split.
  - intros H.
    discriminate.
  - intros H.
    discriminate.
Qed.