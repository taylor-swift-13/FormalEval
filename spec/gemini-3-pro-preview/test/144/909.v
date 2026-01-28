Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["7/725"; "111/9"] -> x1=7, x2=725, n1=111, n2=9
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 7 725 111 9 false.
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
    (* Simplify algebraic expressions: (7 * 111) mod (725 * 9) *)
    (* 7 * 111 = 777 *)
    (* 725 * 9 = 6525 *)
    (* 777 mod 6525 = 777 *)
    (* H_mod becomes 777 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.