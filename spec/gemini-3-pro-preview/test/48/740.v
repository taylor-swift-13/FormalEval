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

(* Test case: input = ["Ky"], output = false *)
Example test_palindrome_ky : is_palindrome_spec "Ky" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "Ky" *)
  simpl.
  
  (* The goal becomes: false = true <-> "Ky" = "yK" *)
  split.
  - (* Left to Right: false = true -> "Ky" = "yK" *)
    intros H.
    inversion H.
  - (* Right to Left: "Ky" = "yK" -> false = true *)
    intros H.
    inversion H.
Qed.