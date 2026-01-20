Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["7/2"; "11711/7"] -> x1=7, x2=2, n1=11711, n2=7
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 7 2 11711 7 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (7 * 11711) mod (2 * 7) *)
    (* 7 * 11711 = 81977 *)
    (* 2 * 7 = 14 *)
    (* 81977 mod 14 = 7 *)
    (* H_mod becomes 7 = 0, which is false *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.