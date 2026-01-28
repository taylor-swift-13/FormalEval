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

(* Test case: input = ["Dere"], output = false *)
Example test_palindrome_dere : is_palindrome_spec "Dere" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "Dere" to "ereD" *)
  simpl.
  
  (* The goal becomes: false = true <-> "Dere" = "ereD" *)
  split.
  - (* Left to Right: false = true -> "Dere" = "ereD" *)
    intros H.
    (* false = true is a contradiction *)
    discriminate H.
  - (* Right to Left: "Dere" = "ereD" -> false = true *)
    intros H.
    (* "Dere" = "ereD" is a contradiction because 'D' <> 'e' *)
    discriminate H.
Qed.