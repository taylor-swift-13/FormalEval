Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["4553/384"; "9999/0100"] -> x1=4553, x2=384, n1=9999, n2=100
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 4553 384 9999 100 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Evaluate the modulo to show it is not 0 *)
    vm_compute in H_mod.
    (* H_mod becomes 21447 = 0, which is false *)
    discriminate H_mod.
Qed.