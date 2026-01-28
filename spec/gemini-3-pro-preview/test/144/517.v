Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["37/55"; "161111/78"] -> x1=37, x2=55, n1=161111, n2=78
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 37 55 161111 78 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is impossible *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate (37 * 161111) mod (55 * 78) *)
    vm_compute in H_mod.
    (* Reduces to 2297 = 0, which is impossible *)
    discriminate.
Qed.