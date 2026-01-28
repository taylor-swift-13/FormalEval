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

(* Test case: input = ["saw?12@zZ2@@@@!3j  nama21"], output = false *)
Example test_palindrome_complex : is_palindrome_spec "saw?12@zZ2@@@@!3j  nama21" false.
Proof.
  (* Unfold the specification definition *)
  unfold is_palindrome_spec.
  
  (* The goal becomes: false = true <-> text = rev text *)
  split.
  - (* Left to Right: false = true -> text = rev text *)
    intros H.
    (* false = true is a contradiction *)
    discriminate.
  - (* Right to Left: text = rev text -> false = true *)
    intros H.
    (* Simplify the reversed string in the hypothesis *)
    simpl in H.
    (* The strings are manifestly different, so equality is impossible *)
    discriminate.
Qed.