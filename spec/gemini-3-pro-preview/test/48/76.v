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

(* Test case: input = ["racecrar"], output = false *)
Example test_palindrome_racecrar : is_palindrome_spec "racecrar" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "racecrar" *)
  simpl.
  
  (* The goal becomes: false = true <-> "racecrar" = "rarcracr" *)
  split.
  - (* Left to Right: false = true -> "racecrar" = "rarcracr" *)
    intros H.
    (* false = true is a contradiction *)
    discriminate H.
  - (* Right to Left: "racecrar" = "rarcracr" -> false = true *)
    intros H.
    (* "racecrar" = "rarcracr" is a contradiction due to distinct characters *)
    discriminate H.
Qed.