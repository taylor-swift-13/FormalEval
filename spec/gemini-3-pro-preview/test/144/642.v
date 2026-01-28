Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 * n2 <> 0 ->
  (result = true <-> (x1 * n1) mod (x2 * n2) = 0).

(* 
   Test case mapping:
   Input: ["163/58"; "16/17"] -> x1=163, x2=58, n1=16, n2=17
   Output: false -> result=false
*)
Example test_simplify_2 : simplify_spec 163 58 16 17 false.
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
    (* Simplify algebraic expressions: (163 * 16) mod (58 * 17) *)
    (* 163 * 16 = 2608 *)
    (* 58 * 17 = 986 *)
    (* 2608 mod 986 = 636 *)
    (* H_mod becomes 636 = 0, which is a contradiction *)
    compute in H_mod.
    discriminate H_mod.
Qed.