Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["921/773"; "921/73"] -> x1=921, x2=773, n1=921, n2=73
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 921 773 921 73 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* H_res implies false = true, which is impossible *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Evaluate the modulo arithmetic to show it is not 0 *)
    vm_compute in H_mod.
    (* H_mod reduces to 1805 = 0, which is false *)
    discriminate H_mod.
Qed.