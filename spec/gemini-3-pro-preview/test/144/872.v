Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["467/736"; "4674/736"] -> x1=467, x2=736, n1=4674, n2=736
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 467 736 4674 736 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* H_res : false = true, which is a contradiction *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Verify that (467 * 4674) mod (736 * 736) is not 0 *)
    vm_compute in H_mod.
    (* H_mod reduces to 15974 = 0, which is a contradiction *)
    discriminate.
Qed.