Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["12/9"; "112/9"] -> x1=12, x2=9, n1=112, n2=9
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 12 9 112 9 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (12 * 112) mod (9 * 9) *)
    (* 12 * 112 = 1344 *)
    (* 9 * 9 = 81 *)
    (* 1344 mod 81 = 48 *)
    (* H_mod becomes 48 = 0 *)
    compute in H_mod.
    discriminate H_mod.
Qed.