Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["16853/58"; "16853/58"] -> x1=16853, x2=58, n1=16853, n2=58
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 16853 58 16853 58 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true, which is contradictory *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Compute the modulo value to show it is not 0 *)
    vm_compute in H_mod.
    (* H_mod reduces to 1089 = 0, which is contradictory *)
    discriminate H_mod.
Qed.