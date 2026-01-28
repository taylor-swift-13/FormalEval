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

(* Test case: input = ["Evivl"], output = false *)
Example test_palindrome_Evivl : is_palindrome_spec "Evivl" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "Evivl" *)
  simpl.
  
  (* The goal becomes: false = true <-> "Evivl" = "lvivE" *)
  split.
  - (* Left to Right: false = true -> "Evivl" = "lvivE" *)
    intros H.
    (* Contradiction: false cannot equal true *)
    discriminate H.
  - (* Right to Left: "Evivl" = "lvivE" -> false = true *)
    intros H.
    (* Contradiction: "Evivl" cannot equal "lvivE" *)
    discriminate H.
Qed.