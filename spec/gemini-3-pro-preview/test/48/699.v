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

(* Test case: input = ["Panam.a."], output = false *)
Example test_palindrome_panama : is_palindrome_spec "Panam.a." false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* Simplify string_rev "Panam.a." *)
  simpl.
  
  (* The goal becomes: false = true <-> "Panam.a." = ".a.manaP" *)
  split.
  - (* Left to Right: false = true -> "Panam.a." = ".a.manaP" *)
    intros H.
    (* false = true is a contradiction *)
    discriminate.
  - (* Right to Left: "Panam.a." = ".a.manaP" -> false = true *)
    intros H.
    (* "Panam.a." = ".a.manaP" is a contradiction *)
    discriminate.
Qed.