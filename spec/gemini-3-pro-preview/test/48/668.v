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

(* Test case: input = ["wswawww"], output = false *)
Example test_palindrome_wswawww : is_palindrome_spec "wswawww" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "wswawww" *)
  simpl.
  
  (* The goal becomes: false = true <-> "wswawww" = "wwwawsw" *)
  split.
  - (* Left to Right: false = true -> ... (Contradiction) *)
    intros H.
    discriminate.
  - (* Right to Left: "wswawww" = "wwwawsw" -> ... (Contradiction) *)
    intros H.
    (* The strings differ at the second character ('s' vs 'w'), so they are not equal *)
    congruence.
Qed.