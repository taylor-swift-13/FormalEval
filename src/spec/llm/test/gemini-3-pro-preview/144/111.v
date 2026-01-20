Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["1333/19"; "1333/19"] -> x1=1333, x2=19, n1=1333, n2=19
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 1333 19 1333 19 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res : false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Calculate (1333 * 1333) mod (19 * 19) *)
    (* 1333 * 1333 = 1776889 *)
    (* 19 * 19 = 361 *)
    (* 1776889 mod 361 = 47 *)
    vm_compute in H_mod.
    (* H_mod becomes 47 = 0, which is a contradiction *)
    discriminate H_mod.
Qed.