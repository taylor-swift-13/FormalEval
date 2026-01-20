Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["316533/58"; "11/9"] -> x1=316533, x2=58, n1=11, n2=9
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 316533 58 11 9 false.
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
    (* Calculate modulo: (316533 * 11) mod (58 * 9) *)
    vm_compute in H_mod.
    (* Result is 123 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.