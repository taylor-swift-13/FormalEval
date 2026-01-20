Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["205/25"; "112/9"] -> x1=205, x2=25, n1=112, n2=9
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 205 25 112 9 false.
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
    (* Simplify algebraic expressions: (205 * 112) mod (25 * 9) *)
    (* 205 * 112 = 22960 *)
    (* 25 * 9 = 225 *)
    (* 22960 mod 225 = 10 *)
    (* H_mod becomes 10 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate.
Qed.