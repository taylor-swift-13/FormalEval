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

(* Test case: input = ["Able was I ere Iba."], output = false *)
Example test_palindrome_false : is_palindrome_spec "Able was I ere Iba." false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev *)
  simpl.
  
  (* The goal becomes: false = true <-> "Able was I ere Iba." = ".abI ere I saw elbA" *)
  split.
  - (* Left to Right: false = true -> ... *)
    intros H.
    discriminate.
  - (* Right to Left: "Able..." = ".abI..." -> false = true *)
    intros H.
    discriminate.
Qed.