Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["453/83384"; "1653/58"] -> x1=453, x2=83384, n1=1653, n2=58
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 453 83384 1653 58 false.
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
    (* Calculate (453 * 1653) mod (83384 * 58) *)
    (* 453 * 1653 = 748809 *)
    (* 83384 * 58 = 4836272 *)
    (* 748809 mod 4836272 = 748809 *)
    (* H_mod becomes 748809 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.