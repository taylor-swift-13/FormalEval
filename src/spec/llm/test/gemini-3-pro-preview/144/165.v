Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["23/52"; "380/241"] -> x1=23, x2=52, n1=380, n2=241
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 23 52 380 241 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: false = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> false = true *)
    intros H_mod.
    (* Calculate values: 23 * 380 = 8740, 52 * 241 = 12532 *)
    (* 8740 mod 12532 = 8740 *)
    (* H_mod becomes 8740 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.