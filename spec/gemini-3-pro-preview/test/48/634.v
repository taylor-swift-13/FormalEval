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

(* Test case: input = ["Rats"], output = false *)
Example test_palindrome_rats : is_palindrome_spec "Rats" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "Rats" *)
  simpl.
  
  (* The goal becomes: false = true <-> "Rats" = "staR" *)
  split.
  - (* Left to Right: false = true -> "Rats" = "staR" *)
    intros H.
    discriminate.
  - (* Right to Left: "Rats" = "staR" -> false = true *)
    intros H.
    discriminate.
Qed.