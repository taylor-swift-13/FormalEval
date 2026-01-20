Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["111/17"; "1111/7"] -> x1=111, x2=17, n1=1111, n2=7
   Output: false -> result=false
*)
Example test_simplify_1 : simplify_spec 111 17 1111 7 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is a contradiction *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (111 * 1111) mod (17 * 7) *)
    (* 111 * 1111 = 123321 *)
    (* 17 * 7 = 119 *)
    (* 123321 mod 119 = 37 *)
    vm_compute in H_mod.
    (* 37 = 0 is a contradiction *)
    discriminate H_mod.
Qed.