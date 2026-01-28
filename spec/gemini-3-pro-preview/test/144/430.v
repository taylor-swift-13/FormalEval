Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["453/384"; "921/739"] -> x1=453, x2=384, n1=921, n2=739
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 453 384 921 739 false.
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
    (* Evaluate the modulo: (453 * 921) mod (384 * 739) *)
    (* 453 * 921 = 417213 *)
    (* 384 * 739 = 283776 *)
    (* 417213 mod 283776 = 133437 *)
    (* H_mod becomes 133437 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.