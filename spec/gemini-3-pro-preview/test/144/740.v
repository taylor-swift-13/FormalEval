Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["99/100"; "99/100"] -> x1=99, x2=100, n1=99, n2=100
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 99 100 99 100 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is impossible *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (99 * 99) mod (100 * 100) *)
    (* 99 * 99 = 9801 *)
    (* 100 * 100 = 10000 *)
    (* 9801 mod 10000 = 9801 *)
    (* 9801 = 0 is impossible *)
    compute in H_mod.
    discriminate H_mod.
Qed.