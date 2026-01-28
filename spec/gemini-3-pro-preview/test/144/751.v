Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["4380/24"; "380/24"] -> x1=4380, x2=24, n1=380, n2=24
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 4380 24 380 24 false.
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
    (* Simplify algebraic expressions: (4380 * 380) mod (24 * 24) *)
    (* 4380 * 380 = 1664400 *)
    (* 24 * 24 = 576 *)
    (* 1664400 mod 576 = 336 *)
    (* H_mod becomes 336 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.