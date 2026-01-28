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

(* Test case: input = ["saw??"], output = false *)
Example test_palindrome_saw : is_palindrome_spec "saw??" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "saw??" *)
  simpl.
  
  (* The goal becomes: false = true <-> "saw??" = "??was" *)
  split.
  - (* Left to Right: false = true -> "saw??" = "??was" *)
    intros H.
    discriminate.
  - (* Right to Left: "saw??" = "??was" -> false = true *)
    intros H.
    discriminate.
Qed.