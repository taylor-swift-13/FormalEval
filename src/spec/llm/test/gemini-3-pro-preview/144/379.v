Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["468/136"; "453/38"] -> x1=468, x2=136, n1=453, n2=38
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 468 136 453 38 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Compute the modulo: (468 * 453) mod (136 * 38) *)
    (* 212004 mod 5168 = 116 *)
    (* H_mod becomes 116 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.