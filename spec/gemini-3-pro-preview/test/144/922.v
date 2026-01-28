Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["921/799"; "921/799"] -> x1=921, x2=799, n1=921, n2=799
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 921 799 921 799 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Evaluate the modulo operation to check if it equals 0 *)
    vm_compute in H_mod.
    (* H_mod reduces to 209840 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.