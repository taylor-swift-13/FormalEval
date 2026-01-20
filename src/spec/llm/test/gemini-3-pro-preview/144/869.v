Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["8577/291"; "85777/291"] -> x1=8577, x2=291, n1=85777, n2=291
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 8577 291 85777 291 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is impossible *)
    discriminate.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Evaluate the modulo to show it is not 0 *)
    vm_compute in H_mod.
    (* H_mod becomes <non_zero_value> = 0, which is a contradiction *)
    discriminate.
Qed.