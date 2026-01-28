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

(* Test case: input = ["sa??"], output = false *)
Example test_palindrome_sa : is_palindrome_spec "sa??" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "sa??" *)
  simpl.
  
  (* The goal becomes: false = true <-> "sa??" = "??as" *)
  split.
  - (* Left to Right: false = true -> "sa??" = "??as" *)
    intros H.
    discriminate H.
  - (* Right to Left: "sa??" = "??as" -> false = true *)
    intros H.
    discriminate H.
Qed.