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

(* Test case: input = ["lvEvil"], output = false *)
Example test_palindrome_lvEvil : is_palindrome_spec "lvEvil" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "lvEvil" *)
  simpl.
  
  (* The goal becomes: false = true <-> "lvEvil" = "livEvl" *)
  split.
  - (* Left to Right: false = true -> "lvEvil" = "livEvl" *)
    intros H.
    inversion H.
  - (* Right to Left: "lvEvil" = "livEvl" -> false = true *)
    intros H.
    inversion H.
Qed.