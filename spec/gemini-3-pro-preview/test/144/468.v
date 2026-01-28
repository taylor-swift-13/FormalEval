Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["3/8"; "23/52"] -> x1=3, x2=8, n1=23, n2=52
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 3 8 23 52 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res is false = true *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (3 * 23) mod (8 * 52) *)
    (* 3 * 23 = 69 *)
    (* 8 * 52 = 416 *)
    (* 69 mod 416 = 69 *)
    (* H_mod becomes 69 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.