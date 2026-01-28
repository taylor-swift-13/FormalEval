Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["4767/736"; "16/17"] -> x1=4767, x2=736, n1=16, n2=17
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 4767 736 16 17 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* false = true is impossible *)
    inversion H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (4767 * 16) mod (736 * 17) *)
    (* 4767 * 16 = 76272 *)
    (* 736 * 17 = 12512 *)
    (* 76272 mod 12512 = 1200 *)
    (* 1200 = 0 is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.