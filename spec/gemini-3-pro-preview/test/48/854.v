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

(* Test case: input = ["canal12zZ2@"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "canal12zZ2@" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "canal12zZ2@" *)
  simpl.
  
  (* The goal becomes: false = true <-> "canal12zZ2@" = "@2Zz21lanac" *)
  split.
  - (* Left to Right: false = true -> "canal12zZ2@" = "@2Zz21lanac" *)
    intros H.
    discriminate H.
  - (* Right to Left: "canal12zZ2@" = "@2Zz21lanac" -> false = true *)
    intros H.
    discriminate H.
Qed.