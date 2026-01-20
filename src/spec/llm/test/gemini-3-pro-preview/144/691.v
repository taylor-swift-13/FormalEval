Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["8523/5922291"; "23/5922291"] -> x1=8523, x2=5922291, n1=23, n2=5922291
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 8523 5922291 23 5922291 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate (8523 * 23) mod (5922291 * 5922291) *)
    (* This reduces to 196029 = 0, which is false *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.