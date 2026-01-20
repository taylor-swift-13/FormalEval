Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["7/225"; "9493/29"] -> x1=7, x2=225, n1=9493, n2=29
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 7 225 9493 29 false.
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
    (* Compute the modulo: (7 * 9493) mod (225 * 29) *)
    vm_compute in H_mod.
    (* H_mod reduces to 1201 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.