Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["5453/84"; "545/84"] -> x1=5453, x2=84, n1=545, n2=84
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 5453 84 545 84 false.
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
    (* Calculate modulo: (5453 * 545) mod (84 * 84) *)
    (* 5453 * 545 = 2971885 *)
    (* 84 * 84 = 7056 *)
    (* 2971885 mod 7056 = 1309 *)
    (* 1309 = 0 is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.