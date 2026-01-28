Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

(* Specification definition *)
Fixpoint correct_bracketing_aux (s : string) (cnt : Z) : bool :=
  match s with
  | EmptyString => Z.eqb cnt 0
  | String c s' =>
      let cnt1 :=
        if Ascii.eqb c (Ascii.ascii_of_nat 40) then Z.succ cnt
        else if Ascii.eqb c (Ascii.ascii_of_nat 41) then Z.pred cnt
        else cnt in
      if Z.ltb cnt1 0 then false else correct_bracketing_aux s' cnt1
  end.

Definition correct_bracketing_fun (brackets : string) : bool :=
  correct_bracketing_aux brackets 0%Z.

Definition correct_bracketing_spec (brackets : string) (res : bool) : Prop :=
  res = correct_bracketing_fun brackets.

(* Test case proof *)
Example test_correct_bracketing : correct_bracketing_spec "(((())(())())(()))()()(()(())))((((((()((()(()(()())((((((()((()(((((((((((()((()((()(())(()()(((())))())(()))()(()())())(())(())(()(())(())())())()())()(((((((()(()(()(())(((((()((()(()(())((((((()((()(()(())())(((((((()((()(()(())(((((((()((()(()(((((((()(()()(()(())((()())())())))()))())()))))))))))((()())())(())(())))(())(((()(()()(()(())(()()())())())))()))(())(" false.
Proof.
  (* Unfold the specification to expose the equality *)
  unfold correct_bracketing_spec.
  (* Unfold the function definition *)
  unfold correct_bracketing_fun.
  (* Evaluate the function on the concrete input and check equality *)
  reflexivity.
Qed.