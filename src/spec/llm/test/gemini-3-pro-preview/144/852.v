Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["23/25"; "921/7939"] -> x1=23, x2=25, n1=921, n2=7939
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 23 25 921 7939 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_contra.
    inversion H_contra.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Compute the modulo value to show contradiction *)
    vm_compute in H_mod.
    (* H_mod is now 21183 = 0 *)
    discriminate H_mod.
Qed.