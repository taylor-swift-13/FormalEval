Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["176/9"; "3921/73"] -> x1=176, x2=9, n1=3921, n2=73
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 176 9 3921 73 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* H_res is false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (176 * 3921) mod (9 * 73) *)
    (* (176 * 3921) mod (9 * 73) evaluates to 246 *)
    (* H_mod becomes 246 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.