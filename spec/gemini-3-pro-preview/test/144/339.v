Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["4767/736"; "9999/0100"] -> x1=4767, x2=736, n1=9999, n2=100
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 4767 736 9999 100 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true, which is a contradiction *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Check if (4767 * 9999) mod (736 * 100) is 0 *)
    vm_compute in H_mod.
    (* H_mod reduces to 46033 = 0, which is a contradiction *)
    discriminate.
Qed.