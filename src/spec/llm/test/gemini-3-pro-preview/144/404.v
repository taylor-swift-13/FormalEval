Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["8/13"; "8/13"] -> x1=8, x2=13, n1=8, n2=13
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 8 13 8 13 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - intros H_res.
    (* false = true is impossible *)
    discriminate.
  - intros H_mod.
    (* (8 * 8) mod (13 * 13) simplifies to 64 mod 169 = 64 *)
    (* H_mod becomes 64 = 0, which is impossible *)
    compute in H_mod.
    discriminate.
Qed.