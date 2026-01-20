Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["435383/38"; "43583/38"] -> x1=435383, x2=38, n1=43583, n2=38
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 435383 38 43583 38 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Compute the modulo to show it's not 0 *)
    vm_compute in H_mod.
    (* This reveals a contradiction (non-zero value = 0) *)
    discriminate.
Qed.