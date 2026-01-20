Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["111/17"; "111/7"] -> x1=111, x2=17, n1=111, n2=7
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 111 17 111 7 false.
Proof.
  unfold simplify_spec.
  intros H_nonzero.
  split.
  - (* Left to Right: result = true -> mod = 0 *)
    intros H_res.
    (* result is false, so H_res implies false = true, which is a contradiction *)
    discriminate H_res.
  - (* Right to Left: mod = 0 -> result = true *)
    intros H_mod.
    (* Simplify algebraic expressions: (111 * 111) mod (17 * 7) *)
    (* 111 * 111 = 12321 *)
    (* 17 * 7 = 119 *)
    (* 12321 mod 119 = 64 *)
    (* H_mod implies 64 = 0, which is a contradiction *)
    vm_compute in H_mod.
    discriminate H_mod.
Qed.