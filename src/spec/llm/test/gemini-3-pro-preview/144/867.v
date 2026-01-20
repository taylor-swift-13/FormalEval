Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["597/2975"; "3880/241"] -> x1=597, x2=2975, n1=3880, n2=241
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 597 2975 3880 241 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Since result is false, H_res is false = true, which is impossible *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Evaluate the modulo arithmetic *)
    vm_compute in H_mod.
    (* H_mod becomes 165435 = 0, which is a contradiction *)
    discriminate.
Qed.