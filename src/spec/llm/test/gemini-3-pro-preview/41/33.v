Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

(* Specification definition inferred from the test case *)
(* Function that computes the sum of squares of elements in a list *)
Definition solution (l : list Z) : Z :=
  fold_right (fun x acc => x * x + acc) 0 l.

(* Test case: input = [13%Z], output = 169%Z *)
Example test_case : solution [13] = 169.
Proof.
  (* Unfold the definition of the function *)
  unfold solution.
  (* Simplify the expression using list and arithmetic reduction *)
  simpl.
  (* Prove that 169 equals 169 *)
  reflexivity.
Qed.