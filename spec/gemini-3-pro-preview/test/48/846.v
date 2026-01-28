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

(* Test case: input = ["Pana.mPa."], output = false *)
Example test_palindrome_pana : is_palindrome_spec "Pana.mPa." false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "Pana.mPa." *)
  simpl.
  
  (* The goal becomes: false = true <-> "Pana.mPa." = ".aPm.anaP" *)
  split.
  - (* Left to Right: false = true -> "Pana.mPa." = ".aPm.anaP" *)
    intros H.
    discriminate.
  - (* Right to Left: "Pana.mPa." = ".aPm.anaP" -> false = true *)
    intros H.
    discriminate.
Qed.