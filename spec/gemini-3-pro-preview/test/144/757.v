Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["85233803/2291"; "8523/522291"] -> x1=85233803, x2=2291, n1=8523, n2=522291
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 85233803 2291 8523 522291 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res is false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Compute the modulo to show it is not 0 *)
    vm_compute in H_mod.
    (* H_mod reduces to something like 723... = 0, which is false *)
    discriminate H_mod.
Qed.