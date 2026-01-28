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

(* Test case: input = ["gese"], output = false *)
Example test_palindrome_gese : is_palindrome_spec "gese" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "gese" *)
  simpl.
  
  (* The goal becomes: false = true <-> "gese" = "eseg" *)
  split.
  - (* Left to Right: false = true -> "gese" = "eseg" *)
    intros H.
    discriminate.
  - (* Right to Left: "gese" = "eseg" -> false = true *)
    intros H.
    inversion H.
Qed.