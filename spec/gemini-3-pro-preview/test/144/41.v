Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["119/13"; "1319/13"] -> x1=119, x2=13, n1=1319, n2=13
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 119 13 1319 13 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* Since result is false, H_res : false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate the modulo: (119 * 1319) mod (13 * 13) *)
    vm_compute in H_mod.
    (* H_mod reduces to a contradiction (e.g., 129 = 0) *)
    discriminate H_mod.
Qed.