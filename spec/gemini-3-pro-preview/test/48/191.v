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

(* Test case: input = ["Tacco"], output = false *)
Example test_palindrome_tacco : is_palindrome_spec "Tacco" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "Tacco" to "occaT" *)
  simpl.
  
  (* The goal becomes: false = true <-> "Tacco" = "occaT" *)
  split.
  - (* Left to Right: false = true -> "Tacco" = "occaT" *)
    intros H.
    (* Premise is false, so we can discriminate *)
    discriminate.
  - (* Right to Left: "Tacco" = "occaT" -> false = true *)
    intros H.
    (* Premise is false ("Tacco" <> "occaT"), so we can discriminate *)
    discriminate.
Qed.