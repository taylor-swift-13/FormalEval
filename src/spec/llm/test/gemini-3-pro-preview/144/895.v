Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["1831/13"; "99/100"] -> x1=1831, x2=13, n1=99, n2=100
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 1831 13 99 100 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (1831 * 99) mod (13 * 100) *)
    (* 1831 * 99 = 181269 *)
    (* 13 * 100 = 1300 *)
    (* 181269 mod 1300 = 569 *)
    (* 569 = 0 is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.