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

(* Test case: input = ["xywzx"], output = false *)
Example test_palindrome_xywzx : is_palindrome_spec "xywzx" false.
Proof.
  unfold is_palindrome_spec.
  simpl.
  split.
  - intros H.
    discriminate H.
  - intros H.
    (* H : "xywzx" = "xzwyx" *)
    (* Injection peels off the first character 'x' which matches *)
    injection H as _ H1.
    (* Injection peels off the second character, 'y' vs 'z', which differs *)
    injection H1 as H2 _.
    (* Inversion on the ascii equality 'y' = 'z' exposes the bit differences *)
    inversion H2.
    (* Discriminate solves the contradictory equality of booleans *)
    discriminate.
Qed.