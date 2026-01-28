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

(* Test case: input = ["sis"], output = true *)
Example test_palindrome_sis : is_palindrome_spec "sis" true.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "sis" *)
  simpl.
  
  (* The goal becomes: true = true <-> "sis" = "sis" *)
  split.
  - (* Left to Right *)
    intros H.
    reflexivity.
  - (* Right to Left *)
    intros H.
    reflexivity.
Qed.