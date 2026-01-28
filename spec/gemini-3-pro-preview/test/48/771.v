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

(* Test case: input = ["Ablba.PA"], output = false *)
Example test_palindrome_ablba_pa : is_palindrome_spec "Ablba.PA" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "Ablba.PA" *)
  simpl.
  
  (* The goal becomes: false = true <-> "Ablba.PA" = "AP.ablbA" *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    (* Contradiction: false cannot equal true *)
    discriminate H.
  - (* Right to Left: "Ablba.PA" = "AP.ablbA" -> ... *)
    intros H.
    (* Contradiction: The strings are distinct *)
    discriminate H.
Qed.