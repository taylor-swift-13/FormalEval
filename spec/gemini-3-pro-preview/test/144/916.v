Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["921/7939"; "11/119"] -> x1=921, x2=7939, n1=11, n2=119
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 921 7939 11 119 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (921 * 11) mod (7939 * 119) *)
    vm_compute in H_mod.
    (* H_mod becomes 10131 = 0, which is false *)
    discriminate H_mod.
Qed.