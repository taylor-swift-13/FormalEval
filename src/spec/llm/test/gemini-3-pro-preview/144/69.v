Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["6/8"; "3/88"] -> x1=6, x2=8, n1=3, n2=88
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 6 8 3 88 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    (* Here result is false, so we have false = true, a contradiction *)
    intros H_res.
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (6 * 3) mod (8 * 88) *)
    (* 6 * 3 = 18 *)
    (* 8 * 88 = 704 *)
    (* 18 mod 704 = 18 *)
    (* H_mod implies 18 = 0, a contradiction *)
    compute in H_mod.
    discriminate.
Qed.