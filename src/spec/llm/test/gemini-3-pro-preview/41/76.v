Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

(* Specification definition inferred from the test case *)
(* Function that computes the sum of squares of elements in a list *)
Definition solution (l : list Z) : Z :=
  fold_right (fun x acc => x * x + acc) 0 l.

(* Test case: input = [42%Z], output = 1764%Z *)
Example test_case : solution [42] = 1764.
Proof.
  (* Unfold the definition of the function *)
  unfold solution.
  (* Simplify the expression using list and arithmetic reduction *)
  simpl.
  (* Prove that 1764 equals 1764 *)
  reflexivity.
Qed.