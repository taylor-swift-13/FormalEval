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

(* Test case: input = ["Taco not"], output = false *)
Example test_palindrome_taco_not : is_palindrome_spec "Taco not" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "Taco not" *)
  simpl.
  
  (* The goal becomes: false = true <-> "Taco not" = "ton ocaT" *)
  split.
  - (* Left to Right: false = true -> "Taco not" = "ton ocaT" *)
    intros H.
    inversion H.
  - (* Right to Left: "Taco not" = "ton ocaT" -> false = true *)
    intros H.
    discriminate.
Qed.