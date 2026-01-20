Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["111/7"; "467/736"] -> x1=111, x2=7, n1=467, n2=736
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 111 7 467 736 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (111 * 467) mod (7 * 736) *)
    vm_compute in H_mod.
    (* 317 = 0 is impossible *)
    discriminate H_mod.
Qed.