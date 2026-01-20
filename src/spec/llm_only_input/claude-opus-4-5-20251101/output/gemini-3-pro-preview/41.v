Require Import ZArith.
Require Import List.
Import ListNotations.

Open Scope Z_scope.

(* Since no specification was provided, I'll create a reasonable one based on the test case *)
(* Input [2] gives output 4, which suggests squaring the single element *)

Definition square_head (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: _ => x * x
  end.

Example test_square_head : square_head [2%Z] = 4%Z.
Proof.
  unfold square_head.
  simpl.
  reflexivity.
Qed.