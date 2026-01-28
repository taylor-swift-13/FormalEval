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

(* Test case: input = ["joOnfO"], output = false *)
Example test_palindrome_joOnfO : is_palindrome_spec "joOnfO" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "joOnfO" *)
  simpl.
  
  (* The goal becomes: false = true <-> "joOnfO" = "OfnOoj" *)
  split.
  - (* Left to Right: false = true -> "joOnfO" = "OfnOoj" *)
    intros H.
    (* Premise is false *)
    inversion H.
  - (* Right to Left: "joOnfO" = "OfnOoj" -> false = true *)
    intros H.
    (* Premise is false due to distinct strings *)
    inversion H.
Qed.